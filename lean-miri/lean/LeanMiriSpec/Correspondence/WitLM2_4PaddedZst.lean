/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.WitLM2_4Core

/-!
# Padded ZST Union Witnesses and General `lean-miri` Step Theorems (`LM-2.4`)

Extracted from `WitLM2_4.lean` (Section 12 first half) so every `LM-2.4`
witness module stays strictly `< 3,500` LOC.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 12. Padded Union with `[(); N]` ZST Array Arm (`kani#5176` / `kani#5159`)

This section proves the Stage-1 simulation theorems and concrete multi-step
witnesses for `#[repr(C)] union` types carrying a zero-sized `[(); N]` array
arm alongside scalar payload arms (`u8`, `u32`) and an uninhabited 0-byte arm
(`VoidZst`). -/

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.layout_eq
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact hu.layout_eq
  | uninitIndirect _ _ _ _ _ _ _ hc _ _ _ => exact hc
  | zstArrayIndirect _ _ _ hc _ _ _ => exact hc
  | zstUninit _ _ _ _ _ _ _ hc _ _ _ => exact hc
  | zstOverlay _ _ _ _ _ _ _ _ _ hc _ _ _ => exact hc

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.cache_layout
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    PaddedZstUnionLocalRel mach decl layouts slot
      { mls with layout := some (translateTy decl.ty layouts) } := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact .ofUnionLocalRel _ _ hu.cache_layout
  | uninitIndirect S n N f_z zstFlIdx mp _ _ hwt hfields hmem =>
    exact .uninitIndirect S n N f_z zstFlIdx mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem
  | zstArrayIndirect N mp _ _ hk hsz hmem =>
    exact .zstArrayIndirect N mp _
      (fun l hl => (Option.some.inj hl).symm) hk hsz hmem
  | zstUninit S n N f_z zstFlIdx mp _ _ hwt hfields hmem =>
    exact .zstUninit S n N f_z zstFlIdx mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp _ _ hwt hfields hmem =>
    exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem

theorem _root_.LeanMiriSpec.Correspondence.ZstZeroMemRel.of_live_base
    {mach mach' : AnnealMachine} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : ZstZeroMemRel mach mp)
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a) :
    ZstZeroMemRel mach' mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hsz hlen hmut =>
    exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hl)
      ((hbase allocId la hl).trans hb) hptr hsz hlen hmut

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.of_live_base
    {mach mach' : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls)
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a) :
    PaddedZstUnionLocalRel mach' decl layouts slot mls := by
  cases h with
  | ofUnionLocalRel _ _ hu =>
    exact .ofUnionLocalRel _ _ (hu.of_live_base hlive hbase)
  | uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields
      (by
        cases hmem with
        | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
            hlen hmut hp hal hex hnat hmask =>
          exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hlive_u)
            ((hbase allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask)
  | zstArrayIndirect N mp c hc hk hsz hmem =>
    exact .zstArrayIndirect N mp c hc hk hsz (hmem.of_live_base hlive hbase)
  | zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields
      (by
        cases hmem with
        | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
            hlen hmut hp hal hex hnat hmask =>
          exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hlive_u)
            ((hbase allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask)
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem =>
    exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields
      (hmem.of_live_base hlive hbase)

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.allocLive
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact hu.allocLive
  | uninitIndirect _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ _ _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstArrayIndirect _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstUninit _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ _ _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstOverlay _ _ _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc _ hprov _ _ hl _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionUninitMemRel.of_filter_live
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : PaddedZstUnionUninitMemRel mach uTy layouts S mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    PaddedZstUnionUninitMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } }
      uTy layouts S mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    have hne_id : (allocId != id) = true := by
      rw [bne_iff_ne]
      intro heq; subst heq
      exact hne (by simp [hprov, Miri.Memory.Provenance.getAllocId])
    have hl' : (allocId, la) ∈
        (mach.memory.live.filter (fun entry => entry.1 != id)).toList := by
      rw [Array.toList_filter, List.mem_filter]
      exact ⟨hl, hne_id⟩
    exact .mk allocId tag baseAddr la hprov hmis hmeta hl' hb hptr hovf hsz hlen hmut hp hal hex hnat hmask

theorem _root_.LeanMiriSpec.Correspondence.ZstZeroMemRel.of_filter_live
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : ZstZeroMemRel mach mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    ZstZeroMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } } mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hsz hlen hmut =>
    have hne_id : (allocId != id) = true := by
      rw [bne_iff_ne]
      intro heq; subst heq
      exact hne (by simp [hprov, Miri.Memory.Provenance.getAllocId])
    have hl' : (allocId, la) ∈
        (mach.memory.live.filter (fun entry => entry.1 != id)).toList := by
      rw [Array.toList_filter, List.mem_filter]
      exact ⟨hl, hne_id⟩
    exact .mk allocId tag baseAddr la hprov hmis hmeta hl' hb hptr hsz hlen hmut

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.of_dealloc
    {mach : AnnealMachine} {val : Miri.Interpreter.LocalValue AnnealProv}
    {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls)
    (hdisj : ∀ mp mp', val = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    PaddedZstUnionLocalRel { mach with memory := deallocLocalMemory mach.memory val }
      decl layouts slot mls := by
  cases h with
  | ofUnionLocalRel _ _ hu =>
    exact .ofUnionLocalRel _ _ (hu.of_dealloc hdisj)
  | uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields (hmem.of_filter_live hne)
  | zstArrayIndirect N mp c hc hk hsz hmem =>
    cases val with
    | dead => exact .zstArrayIndirect N mp c hc hk hsz hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstArrayIndirect N mp c hc hk hsz hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstArrayIndirect N mp c hc hk hsz hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstArrayIndirect N mp c hc hk hsz (hmem.of_filter_live hne)
  | zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields (hmem.of_filter_live hne)
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields (hmem.of_filter_live hne)

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.lookup_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf) {i : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls i = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : i < af.locals.length) (hlt_mf : i < mf.locals.size),
      get? af.locals i = some slot ∧
      mf.locals[i]? = some mls ∧
      mf.locals[i]'hlt_mf = mls ∧
      PaddedZstUnionLocalRel mach decl body.layouts slot mls := by
  rw [get?_eq_getElem?] at hdecl
  obtain ⟨hlt_d, _⟩ := List.getElem?_eq_some_iff.mp hdecl
  have hlt_af : i < af.locals.length := by rw [hrel.af_locals_len]; exact hlt_d
  have hlt_mf : i < mf.locals.size := by rw [hrel.mf_locals_size]; exact hlt_d
  have hslot : get? af.locals i = some (af.locals[i]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[i]? = some (mf.locals[i]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  have hdecl' : get? body.localDecls i = some decl := hdecl
  exact ⟨af.locals[i]'hlt_af, mf.locals[i]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hrel.locals_rel i decl _ _ hdecl' hslot hmls⟩

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.update_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : PaddedZstUnionLocalRel mach decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4PaddedZst body mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < mf.locals.size) :
    FrameRelLM2_4PaddedZst body mach af
      (cacheFrameLocalLayout mf idx hlt_mf (translateTy decl.ty body.layouts)) where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := hrel.af_locals_len
  mf_locals_size := by unfold cacheFrameLocalLayout; rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    unfold cacheFrameLocalLayout at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      rw [hdecl] at hdecl_i
      cases hdecl_i
      cases hmls_i
      have hmls_orig : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
        Array.getElem?_eq_getElem hlt_mf
      exact (hrel.locals_rel idx decl slot_i _ hdecl hslot_i hmls_orig).cache_layout
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.indirect_allocId
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), c⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  have hlt_mf : j < mf.locals.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hlt_d : j < body.localDecls.length := hrel.mf_locals_size ▸ hlt_mf
  have hlt_af : j < af.locals.length := hrel.af_locals_len ▸ hlt_d
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_d]
  have hslot : get? af.locals j = some (af.locals[j]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hloc := hrel.locals_rel j _ _ _ hdecl hslot hj
  generalize body.localDecls[j]'hlt_d = decl_j at hloc
  generalize af.locals[j]'hlt_af = slot_j at hloc
  cases hloc with
  | ofUnionLocalRel _ _ hu =>
    cases hu with
    | base _ _ hl =>
      cases hl with
      | indirect _ _ _ _ _ hmp =>
        cases hmp with
        | mk a t _ _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ =>
          exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
    | union _ _ _ _ _ _ _ _ _ _ _ hmem =>
      cases hmem with
      | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
    | unionOverlay _ _ _ _ _ _ _ _ _ _ _ _ _ hmem =>
      cases hmem with
      | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | uninitIndirect _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstArrayIndirect _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstUninit _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstOverlay _ _ _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.update_local_dealloc
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf) (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : PaddedZstUnionLocalRel
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4PaddedZst body
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf }
    where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj idx i mp mp' (mf.locals[idx]'hlt_mf).layout mls_i.layout h_eq
      · have h0 : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
          Array.getElem?_eq_getElem hlt_mf
        rw [h0]
        cases hls : mf.locals[idx]'hlt_mf
        rw [hls] at hv; dsimp only at hv; subst hv; rfl
      · rw [hmls_i]
        cases mls_i
        dsimp only at hv'; subst hv'; rfl

/-- **`step_storageLive_LM2_4PaddedZst_simulation`** (`G3`): `StorageLive(loc)`
on any declared local `loc` in `StateRelLM2_4PaddedZst` (including active
padded ZST unions `zstUninit`, `zstOverlay`, `uninitIndirect`, and
`zstArrayIndirect`): both `annealStepHooksLM2_4PaddedZst` and `annealStepHooksLM2_4`
step in lockstep with `stepMirFn body s` to `StateRelLM2_4PaddedZst`, freeing any
stack allocation owned by `loc` and preserving `StepPreservesNodup` and
`StepPreservesHighWater m 0`. -/
theorem step_storageLive_LM2_4PaddedZst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    StepRelLM2_4PaddedZst body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageLive loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4PaddedZst, annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageLive_any_eq hframes hlt_mf hty hlive
  have hm_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := hm
  have hstep_pz := miri_step_at_statement_ok
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq
  have hstep_base := miri_step_at_statement_ok
    (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_base rfl hfr.location_eq
  rw [hstep_pz, hstep_base]
  refine ⟨?_, rfl, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4PaddedZst.step
    have hnew : PaddedZstUnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .uninit
        { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
      rw [hmls_eq]
      exact .ofUnionLocalRel _ _ (.base _ _
        (.immediate .uninit .uninit mls.layout hloc.layout_eq (Or.inl ⟨rfl, rfl⟩)))
    have hfr' := hfr.update_local_dealloc hdisj hdecl .uninit (.live (.immediate .uninit)) hnew
    exact StateRelLM2_4PaddedZst.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_storageDead_LM2_4PaddedZst_simulation`** (`G3`): `StorageDead(loc)`
on any declared local `loc ≠ 0` in `StateRelLM2_4PaddedZst`: both
`annealStepHooksLM2_4PaddedZst` and `annealStepHooksLM2_4` step in lockstep with
`stepMirFn body s` to `StateRelLM2_4PaddedZst`, freeing any stack allocation
owned by `loc` and preserving `StepPreservesNodup` and `StepPreservesHighWater m 0`. -/
theorem step_storageDead_LM2_4PaddedZst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    StepRelLM2_4PaddedZst body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageDead loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4PaddedZst, annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageDead_any_eq hframes hlt_mf hne hlive
  have hm_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := hm
  have hstep_pz := miri_step_at_statement_ok
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq
  have hstep_base := miri_step_at_statement_ok
    (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_base rfl hfr.location_eq
  rw [hstep_pz, hstep_base]
  refine ⟨?_, rfl, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4PaddedZst.step
    have hnew : PaddedZstUnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .dead
        { topFrame.locals[loc]'hlt_mf with value := .dead } := by
      rw [hmls_eq]
      exact .ofUnionLocalRel _ _ (.base _ _ (.dead mls.layout hloc.layout_eq))
    have hfr' := hfr.update_local_dealloc hdisj hdecl .dead .dead hnew
    exact StateRelLM2_4PaddedZst.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨(topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

/-- **Conservativity & Transfer Theorem (`G4`)**:
For any statement `⟨.assign dst (.use op), span⟩` at `s.frame.stmtIdx` of `bb`
where `annealEvalOperandLM2_4PaddedZst` agrees with `annealEvalOperandLM2_4` on
`translateOperand op` (including all non-union operands via
`annealEvalOperandLM2_4PaddedZst_eq_of_not_unionLocal`, all `[]`-projected union
copies/moves via `annealEvalOperandLM2_4PaddedZst_eq_of_projection`, and all
inhabited `[Field j fty]` union field reads via
`annealEvalOperandLM2_4PaddedZst_eq_of_inhabited_field`):
1. `Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
   Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m`;
2. Any `StepRelLM2_4 body m (stepMirFn body s) (Step.step (annealStepHooksLM2_4 ...) () m)`
   transfers immediately to `StepRelLM2_4PaddedZst` under `annealStepHooksLM2_4PaddedZst`! -/
theorem step_padded_zst_transfer_assign_use
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData} {dst : Place} {op : Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign dst (.use op), span⟩)
    (hop : ∀ known,
      annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts (translateOperand op) known =
        annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known)
    (hvalid : ∀ dest st1 src st2,
      (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace () (translatePlace dst) true m = .ok dest st1 →
      annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some dest.layout) st1 = .ok src st2 →
      annealValidateOpLM2_4PaddedZst body.layouts src st2 = .ok () st2) :
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    (StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) →
      StepRelLM2_4PaddedZst body m (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m)) := by
  have heval_eq :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
        (translateStmt ⟨.assign dst (.use op), span⟩) m =
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign dst (.use op), span⟩) m := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translateRvalue]
    exact annealStepHooksLM2_4PaddedZst_assign_use_eq body.localDecls body.layouts ()
      (translatePlace dst) (translateOperand op) _ m hop hvalid
  have hstep_eq :
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 body.localDecls body.layouts) () m := by
    unfold Miri.Interpreter.Step.step
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]
    dsimp only
    rw [hloc, hbody]
    dsimp only
    rw [translateBody_basicBlocks_getElem?, hbb]
    dsimp only [Option.map]
    rw [translateBasicBlockData_statements_getElem?, hstmt]
    dsimp only [Option.map]
    rw [heval_eq]
  exact ⟨hstep_eq, fun h => by rw [hstep_eq]; exact h.toPaddedZst⟩

/-- `isUnionLocal` holds for any local declared with a `WellTypedPaddedZstUnionTy`. -/
theorem isUnionLocal_of_wellTypedPaddedZst {body : CapturedMir} {u : Local} {uDecl : LocalDecl}
    {S N f_z zstFlIdx : Nat} (hdecl : get? body.localDecls u = some uDecl)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx) :
    isUnionLocal body.localDecls body.layouts u = true := by
  obtain ⟨n, hn, _⟩ := hwt.fields_union
  simp only [isUnionLocal, lookupLocalDeclLayout, hdecl, LeanMiriSpec.Correspondence.isUnionLayout, hn]

/-- Whole-union copy (`_w = copy _u`) of an all-uninit `[(); N]`-initialized
padded union (`PaddedZstUnionLocalRel.zstUninit`) into an uninitialized immediate
union local `_w` steps both machines in lockstep (`StateRelLM2_4PaddedZst`),
copying `InitMask.new (translateSizeBytes S) false` into `_w`'s fresh allocation
via `union_copy_uninit_alloc_spec` (`kani#5176`). -/
theorem step_padded_zst_union_whole_copy_uninit_mask_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (List.replicate n .unit))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4PaddedZst body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (List.replicate n .unit))) ∧
      (∀ j, j ≠ w → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
      PaddedZstUnionUninitMemRel m'.machine uDecl.ty body.layouts S mp ∧
      PaddedZstUnionUninitMemRel m'.machine wDecl.ty body.layouts S mp_w ∧
      LiveAllocsNodup m'.machine ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have hwu : w ≠ u := by
    intro h; subst h; rw [hw_uninit] at hu_slot; cases hu_slot
  have hwt_w : WellTypedPaddedZstUnionTy body.layouts wDecl.ty S N f_z zstFlIdx := hty ▸ hwt
  have hfields_w : (translateTy wDecl.ty body.layouts).layout.fields = .Union n := hty ▸ hfields_u
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨slot_w, mls_w, hlt_af_w, hlt_w, hslot_w, hmls_w, hmls_w_eq, hloc_w⟩ :=
    hframe.lookup_local hdecl_w
  rw [hw_uninit] at hslot_w
  injection hslot_w with hslot_w
  subst hslot_w
  have hw_imm' := hw_imm topFrame hframes mls_w hmls_w
  have hloc_w' : LocalRel m.machine wDecl body.layouts .uninit mls_w := by
    cases hloc_w with
    | ofUnionLocalRel _ _ hu =>
      cases hu with
      | base _ _ hl => exact hl
    | uninitIndirect _ _ _ _ _ mp' _ _ _ _ _ => exact absurd rfl (hw_imm' mp')
  have hcache_w := hloc_w'.layout_eq
  have hmls_w_val : mls_w.value = .live (.immediate .uninit) := by
    cases hloc_w' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hcache_w)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hwu] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperand body.localDecls body.layouts (.Copy ⟨u, #[]⟩) (some layW) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ :=
    annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hcache_u
  have hlt_w₁ : w < topFrame₁.locals.size := by
    dsimp only [topFrame₁, topFrame₀]; rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]
    exact hlt_w
  have hmls_w₁ : topFrame₁.locals[w]? = some { mls_w with layout := some layW } := by
    dsimp only [topFrame₁, topFrame₀, cacheFrameLocalLayout]
    simp [Ne.symm hwu, hmls_w_eq]
  have hw₁ : topFrame₁.locals[w]'hlt_w₁ = { mls_w with layout := some layW } := by
    have h := Array.getElem?_eq_getElem hlt_w₁
    rw [hmls_w₁] at h
    exact (Option.some.inj h).symm
  have hc_w₁ : (topFrame₁.locals[w]'hlt_w₁).layout = some layW := by rw [hw₁]
  have hval_w₁ : (topFrame₁.locals[w]'hlt_w₁).value = .live (.immediate .uninit) := by
    rw [hw₁]; exact hmls_w_val
  obtain ⟨alloc, htry, hbs, hlen_alloc, hnat, hmut, hal, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layW.layout.size layW.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hmem_orig := hmem
  cases hmem with
  | mk allocId tag baseAddr la hprov_u hmis_u hmeta_u hlive_u hbase_u hptr_u hovf_u hsz_u
      hlen_u hmut_u hp_u hal_u hex_u hnat_u hmask_u =>
  have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
  have hlayW_toNat : layW.layout.size.bytes.toNat = S := by
    rw [hlayW_sz]
    exact translateSizeBytes_toNat_of_valid hS
  obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, hA_mask,
      hA_extra, hA_native, _⟩ :=
    union_copy_uninit_alloc_spec (src := la.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS false hlen_u hsz_u hp_u hmask_u
      (by change alloc.len = S; rw [hlen_alloc, hlayW_toNat])
      (by change alloc.byteSize = translateSizeBytes S; rw [hbs, hlayW_sz])
      hmut hprov_alloc
      (by show (alloc.withExtra none).initializationMask.len = translateSizeBytes S
          change alloc.initializationMask.len = translateSizeBytes S
          rw [hmask_alloc, hlayW_sz]; rfl)
  have hcopy_w' : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]; exact hcopy_w
  have hmemcopy := annealMemCopyOp_freshUnion (body := body) (m := m₁) rfl hlt_w₁ hdecl_w hc_w₁
    hval_w₁ hwt_w.sized htry hres hnodup hprov_u hlive_u hbase_u hptr_u hcopy_w'
    layU topFrame.localsIdentity
  have hunion_w := isUnionLocal_of_wellTypedPaddedZst hdecl_w hwt_w
  have hunion_u := isUnionLocal_of_wellTypedPaddedZst hdecl_u hwt
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (.copy ⟨u, .nil⟩))) = true := by
    simp [lm24Assign, lm24Place, hunion_w]
  have huse : usesMemCopy ⟨.indirect mp, layU⟩ = true := by
    simp [usesMemCopy, layU, hfields_u]
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := hop
  have hop_pz : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := by
    show annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
      (.Copy ⟨u, #[]⟩) (some layW) m₀ = .ok ⟨.indirect mp, layU⟩ m₁
    unfold annealEvalOperandLM2_4PaddedZst
    simp only [hunion_u, ↓reduceIte]
    exact hop
  let mp_w := stackAllocPlace id
  let mach₃ := stackAllocMachine m.machine mem' id A_w
  let tf₃ := setFrameLocalIndirect topFrame₁ w hlt_w₁ mp_w
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    rw [show Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_4 body.localDecls body.layouts) ()
          (translateRvalue (.use (.copy ⟨u, .nil⟩))) ⟨w, #[]⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ by
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok hevalPlace']
      dsimp only [translateRvalue]
      rw [EStateM.bind_eq_ok hop']
      simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hval_u : annealValidateOpLM2_4PaddedZst body.layouts ⟨.indirect mp, layU⟩ m₁ = .ok () m₁ := by
    obtain ⟨defPath, args, tl, n', _, hk, _, hlt900, hlookup, hfu, hvar, huninh, _⟩ := hwt.adt_spec
    have htid : layU.ty = uDecl.ty.layoutIdx + 100 := by
      simp [layU, translateTy, encodeTyId, hk, hlookup, Nat.add_comm]
    have hlo : 100 ≤ uDecl.ty.layoutIdx + 100 := Nat.le_add_left 100 _
    have hhi : uDecl.ty.layoutIdx + 100 < 1000 := Nat.add_lt_add_right hlt900 100
    have hsub : uDecl.ty.layoutIdx + 100 - 100 = uDecl.ty.layoutIdx := Nat.add_sub_cancel _ 100
    have hlay_fields : layU.layout.fields = .Union n' := by
      simp [layU, translateTy, hk, hlookup, translateTypeLayout, translateFieldsShape, hfu]
    have hlay_var : layU.layout.variants = .Single 0 := by
      simp [layU, translateTy, hk, hlookup, translateTypeLayout, translateVariantsShape, hvar]
    have hclass : annealUnionValidityClassify body.layouts layU.ty m₁ =
        .ok (.aggregate false false false) m₁ := by
      rw [htid]
      unfold annealUnionValidityClassify
      simp only [hlo, hhi, and_self, ↓reduceIte, hsub, hlookup, hvar, pure, Pure.pure, EStateM.pure]
    have hinhab : annealUnionValidityInhabited body.layouts layU.ty = true := by
      rw [htid]
      unfold annealUnionValidityInhabited
      have hne50 : (uDecl.ty.layoutIdx + 100 == 50) = false :=
        Bool.eq_false_iff.mpr (fun h => by
          have heq := beq_iff_eq.mp h
          have : 100 ≤ 50 := heq ▸ Nat.le_add_left 100 uDecl.ty.layoutIdx
          exact absurd this (by decide))
      simp [hne50, hhi, hsub, hlookup, huninh, hvar]
    unfold annealValidateOpLM2_4PaddedZst Miri.Interpreter.ValidityVisitor.validatePlace
    simp only [annealUnionValidityHooks, Bool.false_eq_true, ↓reduceIte,
      pure, Pure.pure, EStateM.pure, bind, Bind.bind, EStateM.bind]
    unfold Miri.Interpreter.ValidityVisitor.visit
    simp only [bind, Bind.bind, EStateM.bind]
    rw [hclass]
    simp only [hlay_fields, hlay_var, hinhab, Bool.false_eq_true, ↓reduceIte, pure, Pure.pure]
    rfl
  have hm_stmt_pz : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    rw [show Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts) ()
          (translateRvalue (.use (.copy ⟨u, .nil⟩))) ⟨w, #[]⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ by
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
        ⟨w, #[]⟩ true m = .ok destPlace m₀ from hevalPlace)]
      dsimp only [translateRvalue]
      rw [EStateM.bind_eq_ok hop_pz]
      dsimp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
        annealRvalueHooks]
      rw [EStateM.bind_eq_ok hval_u]
      simp only [huse, ↓reduceIte]]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
  have hstep_m_pz := miri_step_at_statement_ok (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt_pz rfl hloc₃
  -- Anneal side: `validateLoadedValue` accepts `.aggregate 0 (List.replicate n .unit)` on a union local.
  have hvld : validateLoadedValue body.layouts body.localDecls (.copy ⟨u, .nil⟩)
      (.aggregate 0 (List.replicate n .unit)) = true := by
    obtain ⟨defPath, args, _, _, _, hk, _⟩ := hwt.adt_spec
    have hpt : placeTy body.localDecls body.layouts ⟨u, .nil⟩ = some uDecl.ty := by
      simp [placeTy, hdecl_u, resolveProjectedTy]
    simp only [validateLoadedValue, operandTy]
    rw [hpt]; dsimp only; rw [hk]
  have hnoUninit : valueContainsUninit (.aggregate 0 (List.replicate n .unit)) = false := by
    have hlist : ∀ k : Nat, valueListContainsUninit (List.replicate k Value.unit) = false := by
      intro k; induction k with | zero => rfl | succ k ih => simpa [List.replicate_succ, valueListContainsUninit, valueContainsUninit] using ih
    exact hlist n
  have hrv : evalRvalue s.frame.locals (.use (.copy ⟨u, .nil⟩)) s.memory body.localDecls
      body.layouts =
      .ok (.aggregate 0 (List.replicate n .unit)) s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    simp only [evalOperand, hu_slot, readProjectedValue, hnoUninit, hvld]
  let locals₂ := s.frame.locals.set w (.init (.aggregate 0 (List.replicate n .unit)))
  have ha_ok : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
    unfold evalStmt
    dsimp only
    rw [hrv]
    simp only []
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]
    simp [hw_uninit, set?_eq_some_set hlt_af_w, locals₂]
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A_w hres
  have hmem_w : PaddedZstUnionUninitMemRel mach₃ wDecl.ty body.layouts S mp_w :=
    .mk id .one (annealStackBaseAddr id) ⟨.stack, A_w⟩ rfl rfl rfl
      (by simp [mach₃, stackAllocMachine])
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
      hA_sz hA_len hA_mut hA_prov
      (by rw [hA_align]; exact hal) hA_extra (by rw [hA_native]; exact hnat) hA_mask
  have hmem_u : PaddedZstUnionUninitMemRel mach₃ uDecl.ty body.layouts S mp := by
    cases hmem_orig with
    | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
        hlen hmut hp hal hex hnat hmask =>
      exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive_b _ hlive_u)
        ((hbase_b allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask
  have hframe₁ : FrameRelLM2_4PaddedZst body m.machine s.frame topFrame₁ :=
    (hframe.cache_local_layout hdecl_w hlt_w).cache_local_layout hdecl_u hlt_u₀
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
    (hdisj.cache_layout hlt_w _).cache_layout hlt_u₀ _
  let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
  let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
  have hframe_fin : FrameRelLM2_4PaddedZst body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
    { body_eq := hframe.body_eq
      location_eq := rfl
      af_locals_len := by
        show (s.frame.locals.set w _).length = _
        rw [List.length_set]; exact hframe.af_locals_len
      mf_locals_size := by
        show (topFrame₁.locals.set w _ hlt_w₁).size = _
        rw [Array.size_set]; exact hframe₁.mf_locals_size
      locals_rel := by
        intro i decl slot mls hdecl hslot hmls
        have hslot' : get? locals₂ i = some slot := hslot
        have hmls' : (topFrame₁.locals.set w
            { topFrame₁.locals[w]'hlt_w₁ with value := .live (.indirect mp_w) } hlt_w₁)[i]? =
            some mls := hmls
        rw [get?_eq_getElem?, List.getElem?_set] at hslot'
        rw [Array.getElem?_set] at hmls'
        by_cases hiw : w = i
        · subst hiw
          simp only [↓reduceIte, hlt_af_w, Option.some.injEq] at hslot' hmls'
          subst hslot' hmls'
          rw [hdecl_w] at hdecl
          cases hdecl
          refine .zstUninit S n N f_z zstFlIdx mp_w _ ?_ hwt_w hfields_w hmem_w
          intro l hl; rw [hc_w₁] at hl; exact (Option.some.inj hl).symm
        · simp only [hiw, ↓reduceIte] at hslot' hmls'
          exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b hbase_b }
  have hdisj_fin : MemoryAllocDisjoint tf_fin := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_w : w = i
    · subst hi_w
      have hj_w : w ≠ j := hij
      simp only [hj_w, ↓reduceIte] at hj
      simp only [↓reduceIte] at hi
      obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
      injection hi with hi; injection hi with hv _; injection hv with hv; injection hv with hv
      subst hv; rw [ha]
      simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact fun h => hfreshne a la' hla h.symm
    · simp only [hi_w, ↓reduceIte] at hi
      by_cases hj_w : w = j
      · subst hj_w
        simp only [↓reduceIte] at hj
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
        injection hj with hj; injection hj with hv _; injection hv with hv; injection hv with hv
        subst hv; rw [ha]
        simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact hfreshne a la' hla
      · simp only [hj_w, ↓reduceIte] at hj
        exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
  have hstate' : StateRelLM2_4PaddedZst body (advanceStmt s locals₂ s.memory) m' :=
    StateRelLM2_4PaddedZst.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩ hframe_fin hcal hstack hbor hprot
      hcaller hdisj_fin
  have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
      IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
    intro tf htf j hj himm_j
    rw [hframes] at htf
    have htf' : topFrame = tf := by simpa using htf
    subst htf'
    have h₁ := (himm_j.cache_layout hlt_w layW).cache_layout hlt_u₀ layU
    intro mls hmls
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
    rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
    exact h₁ mls hmls
  refine ⟨advanceStmt s locals₂ s.memory, m', mp_w, tf_fin, by rw [hstep_a, ha_ok],
    hstep_m, hstep_m_pz, hstate', ?_, ?_, rfl, ⟨(topFrame₁.locals[w]'hlt_w₁).layout, ?_⟩,
    ⟨some layU, ?_⟩, hmem_u, hmem_w, LiveAllocsNodup.stackAllocMachine A_w hnodup hres,
    himm_fin, rfl, rfl⟩
  · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_w]
  · intro j hj
    simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]
  · simp [tf_fin, tf₃, setFrameLocalIndirect]
  · dsimp only [tf_fin, tf₃, setFrameLocalIndirect]
    rw [Array.getElem?_set_ne _ hwu]
    dsimp only [topFrame₁, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self, hmls_u₀]

/-- Concrete `#[repr(C)] union PU { z: [(); 4], a: u8, b: u32, void: VoidZst }`
(`S = 4`, `N = 4`, `n = 4`). -/
def lm24ZstArr4Layout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .array ⟨0⟩ 4, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def lm24VoidZstLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .empty,
    isUninhabited := true, fieldLayouts := [] }

def lm24PULayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0, 1, 3] }

def lm24PULayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lm24U8Layout, lm24U32Layout, lm24ZstArr4Layout, lm24VoidZstLayout, lm24PULayout] }

def lm24UnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def lm24ZstArr4Ty : Ty := { kind := .array (.tuple []) 4, layoutIdx := 2 }
def lm24VoidZstTy : Ty := { kind := .adt "VoidZst" [], layoutIdx := 3 }
def lm24PUTy : Ty := { kind := .adt "PU" [], layoutIdx := 4 }

theorem lm24_wt_PU : WellTypedPaddedZstUnionTy lm24PULayouts lm24PUTy 4 4 0 2 where
  size_valid := Or.inr (Or.inr (Or.inl rfl))
  count_pos := by decide
  fields_union := ⟨4, rfl, by decide⟩
  size_eq := rfl
  sized := rfl
  align_le := by decide
  adt_spec := ⟨"PU", [], lm24PULayout, 4, lm24ZstArr4Layout,
    rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Anneal `LocalSlot` of `PU` initialized via its `[(); 4]` ZST arm (`f_z = 0`):
all 4 union field slots hold `.unit`, whose `encodeByLayoutIdxAux` byte image is
4 `.uninit` bytes (`replicateUninitBytes 4`). -/
def lm24PUZstSlot : LocalSlot := .init (.aggregate 0 [.unit, .unit, .unit, .unit])

/-- The Anneal `LocalSlot` of `PU` initialized via its `u8` arm (`f = 1`) with `0x55_u8`. -/
def lm24PUU8Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0 [.unit, .scalar ⟨n, 1⟩, .unit, .unit])

/-- The Anneal `LocalSlot` of `PU` initialized via its `u32` arm (`f = 2`) with `n_u32`. -/
def lm24PUU32Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0 [.unit, .unit, .scalar ⟨n, 4⟩, .unit])

/-- The Anneal `LocalSlot` of `PU` after `_1 = PU { a: 0x55_u8 }` is overwritten
by `_1.0 = copy _5` (`[(); 4]` ZST arm): all 4 typed slots become `.unit` and the
`D13a` raw-byte overlay retains `0x55` at byte `0` and `.uninit` at bytes `[1, 4)`. -/
def lm24PUZstOverU8Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0
    ([.unit, .unit, .unit, .unit] ++
      [.aggregate 0
        (encodeRawAbstractByteVals
          (encodeLittleEndianBytes n 1 none ++ replicateUninitBytes 3))]))

/-- Locals of `lm24PUBody`:
- `_0: u32`
- `_1: PU`
- `_2: u8`
- `_3: u32`
- `_4: PU`
- `_5: [(); 4]`
- `_6: [(); 4]`
- `_7: ()`
- `_8: VoidZst` -/
def lm24PUBody : CapturedMir where
  defPath := "lm_2_4_witness::padded_zst_unions"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    lm24Decl lm24U32Ty,
    lm24Decl lm24PUTy,
    lm24Decl lm24U8Ty,
    lm24Decl lm24U32Ty,
    lm24Decl lm24PUTy,
    lm24Decl lm24ZstArr4Ty,
    lm24Decl lm24ZstArr4Ty,
    lm24Decl lm24UnitTy,
    lm24Decl lm24VoidZstTy]
  basicBlocks := [
    -- `bb0`: `_1 = PU { z: copy _5 }; _4 = copy _1; _6 = copy (_4.0: [(); 4]); _2 = copy (_4.1: u8)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨4, [.field 0 lm24ZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb1`: `_1.0 = copy _5; _4 = move _1; _3 = copy (_4.2: u32)` (UB)
    { statements := [
        mkStmt (.assign ⟨1, [.field 0 lm24ZstArr4Ty]⟩ (.use (.copy (local_ 5)))),
        mkStmt (.assign (local_ 4) (.use (.move (local_ 1)))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb2`: `_1 = PU { a: 0x55_u8 }; _1.0 = copy _5; _6 = copy (_1.0: [(); 4]); _2 = copy (_1.1: u8); _3 = copy (_1.2: u32)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 1)) [.constant (lm24ConstU8 0x55)])),
        mkStmt (.assign ⟨1, [.field 0 lm24ZstArr4Ty]⟩ (.use (.copy (local_ 5)))),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨1, [.field 1 lm24U8Ty]⟩))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨1, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb3`: `_1 = PU { z: copy _5 }; _7 = copy (_1.0[2 of 4]: ()); _7 = copy (_1.0[4 of 5]: ())` (well-formed OOB UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty, .constantIndex 2 4 false]⟩))),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty, .constantIndex 4 5 false]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb4`: `_1 = PU { b: 0x01020304_u32 }; _8 = copy (_1.3: VoidZst)` (Uninhabited 0-byte arm UB, `kani#5159`)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 2)) [.constant (lm24ConstU32 0x01020304)])),
        mkStmt (.assign (local_ 8) (.use (.copy ⟨1, [.field 3 lm24VoidZstTy]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb5`: `_1 = PU { z: copy _5 }; StorageDead(_1); StorageLive(_1); _6 = copy (_1.0: [(); 4])` (Uninit union local UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb6`: `_1 = PU { a: 0x55_u8 }; _4 = copy _1; _7 = copy (_4.0[2 of 4]: ()); _2 = copy (_4.1: u8); _3 = copy (_4.2: u32)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 1)) [.constant (lm24ConstU8 0x55)])),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨4, [.field 0 lm24ZstArr4Ty, .constantIndex 2 4 false]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm24FnAbi
  layouts := lm24PULayouts
  allocations := []

def lm24PUAnnealState (b k : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := k, locals := locals }
    memory := (initMachineState lm24PUBody []).memory }

/-- Initial Anneal state of block `b` in `lm24PUBody` with `_5, _6 : [(); 4]`
initialized to `zstArrayVal 4` (matching their live 0-byte allocations in
`lm24PUInitMiriFrame` under tightened `PaddedZstUnionLocalRel.zstArrayIndirect`,
`R-c`) and all other locals `.uninit`. -/
def lm24PUInitAnneal (b : Nat) : MachineState :=
  lm24PUAnnealState b 0
    [.uninit, .uninit, .uninit, .uninit, .uninit,
     .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]

/-- Zero-byte mutable allocation backing `_5 : [(); 4]` in `lean-miri`. -/
def lm24ZstArr4Alloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[] (translateAlignBytes 1) .Mut)
    (by with_unfolding_all rfl)).withExtra none

def lm24ThirdAllocId : Miri.Memory.AllocId := ⟨3, by decide⟩
def lm24ThirdBaseAddr : UInt64 := 0x3000

def lm24ThirdMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes lm24ThirdBaseAddr,
            some (.concrete lm24ThirdAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24FourthAllocId : Miri.Memory.AllocId := ⟨4, by decide⟩
def lm24FourthBaseAddr : UInt64 := 0x4000

def lm24FourthMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes lm24FourthBaseAddr,
            some (.concrete lm24FourthAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24PUUninitAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv)
      (translateSizeBytes 4) (translateAlignBytes 4) .Uninit
      (fun _ _ => some #[0, 0, 0, 0]))
    (by with_unfolding_all rfl)).withExtra none

private theorem allocation_eq_of_parts {P E : Type}
    {a b : Miri.Memory.Allocation P E}
    (hraw : unionAllocRaw a = unionAllocRaw b)
    (hsz : a.byteSize = b.byteSize)
    (hprov : a.provenanceMap = b.provenanceMap)
    (hmask : a.initializationMask = b.initializationMask)
    (hal : a.align = b.align)
    (hmut : a.mutability = b.mutability)
    (hex : a.extra = b.extra)
    (hnat : a.nativeBuffer = b.nativeBuffer) :
    a = b := by
  induction a using Miri.Memory.Allocation.casesOn
  induction b using Miri.Memory.Allocation.casesOn
  cases hraw; cases hsz; cases hprov; cases hmask; cases hal; cases hmut; cases hex; cases hnat
  rfl

private theorem lm24PU_copy_uninitAlloc4_eq :
    Miri.Memory.Allocation.copy lm24PUUninitAlloc4
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true lm24PUUninitAlloc4 =
    .ok () lm24PUUninitAlloc4 := by
  obtain ⟨dest', hcopy, hsz, _, hal, hmut, hprov, hmask, hex, hnat, hraw⟩ :=
    union_copy_uninit_alloc_spec (src := lm24PUUninitAlloc4) (dest := lm24PUUninitAlloc4)
      (S := 4) (Or.inr (Or.inr (Or.inl rfl))) false
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  rw [hcopy]
  congr 1
  exact allocation_eq_of_parts hraw
    (hsz.trans (by with_unfolding_all rfl))
    (hprov.trans (by with_unfolding_all rfl))
    (hmask.trans (by with_unfolding_all rfl))
    hal
    (hmut.trans (by with_unfolding_all rfl))
    hex hnat

def lm24PUMachine : AnnealMachine :=
  { memory :=
      { (Miri.Memory.MemoryState.empty : AnnealMemory) with
        nextAllocId := 5
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[{ allocId := witnessAllocId, address := witnessBaseAddr },
                      { allocId := lm24SecondAllocId, address := lm24SecondBaseAddr },
                      { allocId := lm24ThirdAllocId, address := lm24ThirdBaseAddr },
                      { allocId := lm24FourthAllocId, address := lm24FourthBaseAddr }]
        intToPtrMap := #[{ address := witnessBaseAddr, allocId := witnessAllocId },
                         { address := lm24SecondBaseAddr, allocId := lm24SecondAllocId },
                         { address := lm24ThirdBaseAddr, allocId := lm24ThirdAllocId },
                         { address := lm24FourthBaseAddr, allocId := lm24FourthAllocId }] }
    borrowTracker := none }

def lm24PUInitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24PUBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm24U32Ty lm24PULayouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U32Ty lm24PULayouts) },
      { value := .live (.indirect lm24BaseMemPlace), layout := some (translateTy lm24PUTy lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U8Ty lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U32Ty lm24PULayouts) },
      { value := .live (.indirect lm24Arr2MemPlace), layout := some (translateTy lm24PUTy lm24PULayouts) },
      { value := .live (.indirect lm24ThirdMemPlace), layout := some (translateTy lm24ZstArr4Ty lm24PULayouts) },
      { value := .live (.indirect lm24FourthMemPlace), layout := some (translateTy lm24ZstArr4Ty lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24UnitTy lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24VoidZstTy lm24PULayouts) }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm24PUInitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24PUInitMiriFrame b]⟩, machine := lm24PUMachine }

def lm24PUMiriAt (b k : Nat) : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame b with location := .mir ⟨b, k⟩ }]⟩, machine := lm24PUMachine }

private theorem lm24PU_memCopyOp_eq
    (f : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hf4 : annealForceUnionAllocation lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
      { stack := ⟨#[f]⟩, machine := lm24PUMachine } =
      .ok ⟨lm24Arr2MemPlace, translateTy lm24PUTy lm24PULayouts⟩
        { stack := ⟨#[f]⟩, machine := lm24PUMachine }) :
    annealMemCopyOp lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
      { stack := ⟨#[f]⟩, machine := lm24PUMachine } =
    .ok () { stack := ⟨#[f]⟩, machine := lm24PUMachine } := by
  have hfind_src : lm24PUMachine.memory.live.find? (fun (k, _) => k == witnessAllocId) =
      some (witnessAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := by
    with_unfolding_all rfl
  have hfind_dst : lm24PUMachine.memory.live.findIdx? (fun (k, _) => k == lm24SecondAllocId) =
      some 1 := by
    with_unfolding_all rfl
  have hbase_src : lm24PUMachine.lookupBaseAddr witnessAllocId = some witnessBaseAddr := by
    with_unfolding_all rfl
  have hbase_dst : lm24PUMachine.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
    with_unfolding_all rfl
  have hneq : (witnessAllocId == lm24SecondAllocId) = false := by decide
  unfold annealMemCopyOp
  dsimp only []
  rw [EStateM.bind_eq_ok hf4]
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    lm24BaseMemPlace, lm24Arr2MemPlace, Option.bind, Miri.Memory.Provenance.getAllocId]
  rw [hbase_src, hfind_src, hbase_dst, hfind_dst]
  dsimp only []
  have hget1 : lm24PUMachine.memory.live[1]? =
      some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := rfl
  rw [hget1]
  dsimp only []
  have hoff1 :
      Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes witnessBaseAddr).bytes - witnessBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
  have hoff2 :
      Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
  have hlay_sz : (translateTy lm24PUTy lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
  simp only [hoff1, hoff2, hlay_sz, hneq, lm24PU_copy_uninitAlloc4_eq]
  rfl

private theorem lm24PU_bb0_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 0 1)).2 = .ok true := by
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 0 1) = .ok destPlace (lm24PUMiriAt 0 1) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 0 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMiriAt 0 1) := by with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 0 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMiriAt 0 1) := by with_unfolding_all rfl
  have hmc := lm24PU_memCopyOp_eq { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ }
    (by with_unfolding_all rfl)
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 0 1) =
    .ok () (lm24PUMiriAt 0 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 0 1) =
    .ok () (lm24PUMiriAt 0 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 0 1) = .ok destPlace (lm24PUMiriAt 0 1) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.copy (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) (lm24PUMiriAt 0 1) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) (lm24PUMiriAt 0 1) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      (topFrame' := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      rfl rfl rfl (blockIdx := 0) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      (topFrame' := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      rfl rfl rfl (blockIdx := 0) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

def lm24PUMovedFrame1 (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { lm24PUInitMiriFrame 1 with
    locals := (lm24PUInitMiriFrame 1).locals.set! 1
      { value := .live (.immediate .uninit), layout := some (translateTy lm24PUTy lm24PULayouts) },
    location := .mir ⟨1, k⟩ }

def lm24PUMovedMiri1 (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24PUMovedFrame1 k]⟩, machine := lm24PUMachine }

private theorem lm24PU_bb1_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 1 1)).2 = .ok true := by
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 1 1) = .ok destPlace (lm24PUMiriAt 1 1) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 1 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMovedMiri1 1) := by with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 1 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMovedMiri1 1) := by with_unfolding_all rfl
  have hmc := lm24PU_memCopyOp_eq (lm24PUMovedFrame1 1) (by with_unfolding_all rfl)
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.move (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 1 1) =
    .ok () (lm24PUMovedMiri1 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.move (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 1 1) =
    .ok () (lm24PUMovedMiri1 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 1 1) = .ok destPlace (lm24PUMiriAt 1 1) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.move (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.move (local_ 1))))))
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.move (local_ 1)))) (lm24PUMiriAt 1 1) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.move (local_ 1))))))
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.move (local_ 1)))) (lm24PUMiriAt 1 1) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      rfl rfl rfl (blockIdx := 1) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      rfl rfl rfl (blockIdx := 1) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

theorem miri_step_eq
    (hooks :
      Miri.Interpreter.StepHooks
        AnnealProv
        Miri.Interpreter.LocalLayout
        Unit
        AnnealMachine
        Unit
        (Miri.Interpreter.RuntimePlace AnnealProv))
    (m : AnnealStepState) (r : Except Miri.Interpreter.StepError Bool)
    (h : (Miri.Interpreter.Step.step hooks () m).2 = r) :
    Miri.Interpreter.Step.step hooks () m =
      ((Miri.Interpreter.Step.step hooks () m).1, r) :=
  Prod.ext rfl h

/-- Kernel-checked multi-step execution of `bb0` in `lm24PUBody` (`kani#5176`):
1. `_1 = PU { z: copy _5 }` constructs `PU` via its `[(); 4]` ZST array arm:
   Anneal stores `lm24PUZstSlot` (`[.unit, .unit, .unit, .unit]`, whose
   `encodeByLayoutIdxAux` byte image is `replicateUninitBytes 4`) and `lean-miri`
   preserves `InitMask.new (translateSizeBytes 4) false` on `_1`'s 4-byte allocation;
2. `_4 = copy _1` copies the `[(); 4]`-initialized union in lockstep, preserving
   `lm24PUZstSlot` in Anneal and `InitMask.new (translateSizeBytes 4) false` in
   `_4`'s allocation in `lean-miri`;
3. `_6 = copy (_4.0: [(); 4])` reads the inhabited `[(); 4]` ZST arm from `_4`,
   succeeding in both Anneal (`zstArrayVal 4`) and `lean-miri`
   even though all 4 bytes of `_4` are uninitialized;
4. `_2 = copy (_4.1: u8)` reads the uninitialized `u8` payload arm of `_4`,
   faulting with `.ub` in both Anneal and `lean-miri`. -/
theorem lm24_padded_zst_agg_copy_read_zst_and_payload_ub_steps :
    let s₀ := lm24PUInitAnneal 0
    let s₁ := lm24PUAnnealState 0 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₂ := lm24PUAnnealState 0 2
      [.uninit, lm24PUZstSlot, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₃ := lm24PUAnnealState 0 3
      [.uninit, lm24PUZstSlot, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .fail .ub ∧
    encodeByLayoutIdxAux 8 lm24PULayouts lm24PUTy.layoutIdx
      (.aggregate 0 [.unit, .unit, .unit, .unit]) = some (replicateUninitBytes 4) ∧
    ∃ m₁ m₂ m₃ m₄ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 0) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₃ =
        (m₄, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, lm24PUMiriAt 0 1, lm24PUMiriAt 0 2, lm24PUMiriAt 0 3, _,
    ?_, lm24PU_bb0_step1.1, lm24PU_bb0_step1.2, ?_, ?_, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

/-- Kernel-checked multi-step execution of `bb1` in `lm24PUBody` under BOTH
unmodified `annealStepHooksLM2_4` and `annealStepHooksLM2_4PaddedZst`:
1. `_1.0 = copy _5` writes the `[(); 4]` ZST arm into uninitialized `_1` via
   `uninitFieldWriteShell?` + `writeProjectedForLocal` in Anneal (`lm24PUZstSlot`)
   and `annealEvalUnionFieldPlace` + 0-byte `annealMemCopyOp` in `lean-miri`;
2. `_4 = move _1` moves the `[(); 4]`-initialized union into `_4`, deinitializing
   `_1` and copying `InitMask.new (translateSizeBytes 4) false` into `_4`;
3. `_3 = copy (_4.2: u32)` reads the uninitialized `u32` payload arm of `_4`,
   faulting with `.ub` in both Anneal and `lean-miri`. -/
theorem lm24_padded_zst_field_write_move_and_u32_ub_steps :
    let s₀ := lm24PUInitAnneal 1
    let s₁ := lm24PUAnnealState 1 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₂ := lm24PUAnnealState 1 2
      [.uninit, .uninit, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .fail .ub ∧
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 1) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 1)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, lm24PUMiriAt 1 1, lm24PUMovedMiri1 2, _,
    ?_, ?_, lm24PU_bb1_step1.1, lm24PU_bb1_step1.2, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

/-- Kernel-checked 5-step execution of `bb2` in `lm24PUBody` under BOTH
`annealStepHooksLM2_4` and `annealStepHooksLM2_4PaddedZst`:
1. `_1 = PU { a: 0x55_u8 }` initializes byte `0` to `0x55` and leaves trailing
   padding bytes `[1, 4)` uninitialized;
2. `_1.0 = copy _5` overwrites `_1` with the 0-byte `[(); 4]` ZST arm, setting
   typed slots to `[.unit, .unit, .unit, .unit]` and attaching the raw-byte
   overlay `lm24PUZstOverU8Slot 0x55` in Anneal while preserving byte `0 = 0x55`
   and `[1, 4)` uninitialized in `lean-miri`;
3. `_6 = copy (_1.0: [(); 4])` reads the `[(); 4]` ZST arm, succeeding in both;
4. `_2 = copy (_1.1: u8)` reads back `0x55_u8` from the retained byte `0` in both;
5. `_3 = copy (_1.2: u32)` reads the wider `u32` arm whose trailing bytes `[1, 4)`
   are uninitialized, faulting with `.ub` in both machines. -/
theorem lm24_padded_zst_overwrite_payload_retains_bytes_steps :
    let s₀ := lm24PUInitAnneal 2
    let s₁ := lm24PUAnnealState 2 1
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₂ := lm24PUAnnealState 2 2
      [.uninit, lm24PUZstOverU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₃ := lm24PUAnnealState 2 3
      [.uninit, lm24PUZstOverU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₄ := lm24PUAnnealState 2 4
      [.uninit, lm24PUZstOverU8Slot 0x55, .init (.scalar ⟨0x55, 1⟩), .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .step s₄ ∧
    stepMirFn lm24PUBody s₄ = .fail .ub ∧
    ∃ m₁ m₂ m₃ m₄ m₅ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 2) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 2)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₄ =
        (m₅, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₄).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, _, _, _, _, _,
    Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_,
    Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

set_option maxRecDepth 200000 in
/-- Kernel-checked 3-step execution of `bb3` in `lm24PUBody` under
`annealStepHooksLM2_4PaddedZst` (the pinned `annealStepHooksLM2_4` supports
neither the `[(); 4]` aggregate nor the `ConstantIndex` read):
1. `_1 = PU { z: copy _5 }` constructs `PU` via its `[(); 4]` ZST arm;
2. `_7 = copy (_1.0[2 of 4]: ())` reads in-bounds ZST element `2 < 4`, succeeding
   in both Anneal (`zstUnitVal`) and `lean-miri` (the union's place at the
   zero-sized `()` layout);
3. `_7 = copy (_1.0[4 of 5]: ())` (well-formed `offset = 4 < min_length = 5`,
   exceeding array length `N = 4`) faults with `.ub` in Anneal and with
   vendored `Miri.Interpreter.projectConstantIndex`'s `.bounds 5 4`
   (`"bounds check failed: index 4 >= len 5"`) in `lean-miri`. -/
theorem lm24_padded_zst_elem_index_and_oob_ub_steps :
    let s₀ := lm24PUInitAnneal 3
    let s₁ := lm24PUAnnealState 3 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₂ := lm24PUAnnealState 3 2
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .init zstUnitVal, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .fail .ub ∧
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 3) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "bounds check failed: index 4 >= len 5")) := by
  let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
  let m₁ := lm24PUMiriAt 3 1
  let m₂ := lm24PUMiriAt 3 2
  let m₃ := (Miri.Interpreter.Step.step hooks () m₂).1
  exact ⟨rfl, rfl, rfl, m₁, m₂, m₃,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    miri_step_eq hooks m₂ _ (by with_unfolding_all rfl)⟩

set_option maxRecDepth 200000 in
/-- Kernel-checked negative control (`bb4` in `lm24PUBody`, `kani#5159`) and
storage lifecycle (`bb5` in `lm24PUBody`):
1. In `bb4`, `_1 = PU { b: 0x01020304_u32 }` initializes all 4 bytes of `_1`,
   and reading the uninhabited 0-byte field `_8 = copy (_1.3: VoidZst)` faults
   with `.ub` in Anneal (`tyIsUninhabited = true`) and in `lean-miri` under
   `annealStepHooksLM2_4PaddedZst` with `"validation: zero-variant enum value"`,
   produced by vendored `Miri.Interpreter.ValidityVisitor.validatePlace` inside
   `annealRvalueHooksLM2_4PaddedZst.copyOp` (whereas the pinned unvalidated
   `annealStepHooksLM2_4` accepts the same read,
   `lm24_padded_zst_uninhabited_arm_base_adapter_accepts`);
2. In `bb5`, `_1 = PU { z: copy _5 }`, `StorageDead(_1)`, and `StorageLive(_1)`
   step in lockstep (freeing `_1`'s 4-byte allocation and re-activating `_1` as
   an uninitialized immediate `.immediate .uninit`), after which
   `_6 = copy (_1.0: [(); 4])` on the never-written `.uninit` union `_1` faults
   in both Anneal and `lean-miri` (`"field read of uninitialized union"`).
   **Model boundary (`R-b`)**: both Anneal (`MirSemantics.evalOperand` on
   `LocalSlot.uninit`) and `lean-miri`'s `annealEvalUnionField` (on
   `.immediate .uninit`) are stricter than rustc's Miri (and MiniRust's
   `evalValue_load_union_zstArray_field`), which allocate union storage at
   `StorageLive` and accept 0-byte inhabited field reads on never-written
   unions; see `lm24_never_written_union_zst_read_boundary` below. -/
theorem lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps :
    let s4₀ := lm24PUInitAnneal 4
    let s4₁ := lm24PUAnnealState 4 1
      [.uninit, lm24PUU32Slot 0x01020304, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s5₀ := lm24PUInitAnneal 5
    let s5₁ := lm24PUAnnealState 5 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s5₂ := lm24PUAnnealState 5 2
      [.uninit, .dead, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s5₃ := lm24PUAnnealState 5 3
      [.uninit, .uninit, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s4₀ = .step s4₁ ∧
    stepMirFn lm24PUBody s4₁ = .fail .ub ∧
    stepMirFn lm24PUBody s5₀ = .step s5₁ ∧
    stepMirFn lm24PUBody s5₁ = .step s5₂ ∧
    stepMirFn lm24PUBody s5₂ = .step s5₃ ∧
    stepMirFn lm24PUBody s5₃ = .fail .ub ∧
    ∃ m4₁ m4₂ m5₁ m5₂ m5₃ m5₄ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 4) = (m4₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m4₁ =
        (m4₂, .error (.undefinedBehavior "validation: zero-variant enum value")) ∧
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 5) = (m5₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m5₁ = (m5₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m5₂ = (m5₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m5₃ =
        (m5₄, .error (.undefinedBehavior "field read of uninitialized union")) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₃).2 =
        .error (.undefinedBehavior "field read of uninitialized union") := by
  let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
  let m4₁ := (Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 4)).1
  let m4₂ := (Miri.Interpreter.Step.step hooks () m4₁).1
  let m5₁ := lm24PUMiriAt 5 1
  let m5₂ : AnnealStepState :=
    { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
        locals := (lm24PUInitMiriFrame 5).locals.set! 1
          { value := .dead, layout := some (translateTy lm24PUTy lm24PULayouts) },
        location := .mir ⟨5, 2⟩ }]⟩
      machine := { lm24PUMachine with memory := deallocLocalMemory lm24PUMachine.memory (.live (.indirect lm24BaseMemPlace)) } }
  let m5₃ : AnnealStepState :=
    { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
        locals := (lm24PUInitMiriFrame 5).locals.set! 1
          { value := .live (.immediate .uninit), layout := some (translateTy lm24PUTy lm24PULayouts) },
        location := .mir ⟨5, 3⟩ }]⟩
      machine := { lm24PUMachine with memory := deallocLocalMemory lm24PUMachine.memory (.live (.indirect lm24BaseMemPlace)) } }
  let m5₄ := (Miri.Interpreter.Step.step hooks () m5₃).1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, m4₁, m4₂, m5₁, m5₂, m5₃, m5₄,
    miri_step_eq hooks (lm24PUInitMiri 4) _ (by with_unfolding_all rfl),
    miri_step_eq hooks m4₁ _ (by with_unfolding_all rfl),
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    miri_step_eq hooks m5₃ _ (by with_unfolding_all rfl),
    by with_unfolding_all rfl⟩

/-- The pinned adapter `annealStepHooksLM2_4` accepts the read of the
uninhabited field `_8 = copy (_1.3: VoidZst)` in `bb4`: it copies the 0-byte
field without calling `ValidityVisitor`, and the step succeeds. Anneal faults
there (`lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps`), and
`annealStepHooksLM2_4PaddedZst` faults via vendored
`Miri.Interpreter.ValidityVisitor.validatePlace` inside `copyOp`
(`"validation: zero-variant enum value"`), matching rustc's validated typed
copy without any custom uninhabited-type operand override hook. -/
theorem lm24_padded_zst_uninhabited_arm_base_adapter_accepts :
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 4)).2 = .ok true ∧
    (Miri.Interpreter.Step.step hooks_base ()
        (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 4)).1).2 = .ok true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-! ### `lm24PUInit_stateRel`, Partially Initialized Whole-Copy Witness (`bb6`), and General Step Theorems (`G3`) -/

theorem lm24PU_uninitMem1 :
    PaddedZstUnionUninitMemRel lm24PUMachine lm24PUTy lm24PULayouts 4 lm24BaseMemPlace :=
  .mk witnessAllocId witnessTag witnessBaseAddr
    { kind := .stack, allocation := lm24PUUninitAlloc4 }
    rfl rfl rfl (List.Mem.head _) (by with_unfolding_all rfl) rfl (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_uninitMem4 :
    PaddedZstUnionUninitMemRel lm24PUMachine lm24PUTy lm24PULayouts 4 lm24Arr2MemPlace :=
  .mk lm24SecondAllocId witnessTag lm24SecondBaseAddr
    { kind := .stack, allocation := lm24PUUninitAlloc4 }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.head _)) (by with_unfolding_all rfl) rfl (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_zstMem5 : ZstZeroMemRel lm24PUMachine lm24ThirdMemPlace :=
  .mk lm24ThirdAllocId witnessTag lm24ThirdBaseAddr
    { kind := .stack, allocation := lm24ZstArr4Alloc }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (by with_unfolding_all rfl) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_zstMem6 : ZstZeroMemRel lm24PUMachine lm24FourthMemPlace :=
  .mk lm24FourthAllocId witnessTag lm24FourthBaseAddr
    { kind := .stack, allocation := lm24ZstArr4Alloc }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    (by with_unfolding_all rfl) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

/-- **Initial state relation (`G3`)**: for every block `b`, `lm24PUInitAnneal b`
and `lm24PUInitMiri b` satisfy `StateRelLM2_4PaddedZst lm24PUBody`. -/
theorem lm24PUInit_stateRel (b : Nat) :
    StateRelLM2_4PaddedZst lm24PUBody (lm24PUInitAnneal b) (lm24PUInitMiri b) := by
  refine .mk (lm24PUInitMiriFrame b) rfl rfl ⟨_, rfl⟩
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
    rfl rfl rfl rfl rfl ?_
  · intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 | 7 | 8 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .ofUnionLocalRel _ _ (.base _ _
        (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm) (.inl ⟨rfl, rfl⟩)))
    | 1 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .uninitIndirect 4 4 4 0 2 lm24BaseMemPlace _
        (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl lm24PU_uninitMem1
    | 4 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _
        (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl lm24PU_uninitMem4
    | 5 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 lm24ThirdMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl lm24PU_zstMem5
    | 6 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 lm24FourthMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl lm24PU_zstMem6
    | k + 9 =>
      change (none : Option LocalDecl) = some decl at hdecl
      cases hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    match i, j with
    | 1, 1 | 4, 4 | 5, 5 | 6, 6 => exact absurd rfl hij
    | 1, 4 | 1, 5 | 1, 6 | 4, 1 | 4, 5 | 4, 6 | 5, 1 | 5, 4 | 5, 6 | 6, 1 | 6, 4 | 6, 5 =>
      injection hi with hi; injection hi with hvi _; injection hvi with hvi; injection hvi with hvi
      injection hj with hj; injection hj with hvj _; injection hvj with hvj; injection hvj with hvj
      subst hvi hvj
      decide
    | 0, _ | 2, _ | 3, _ | 7, _ | 8, _ => cases hi
    | _, 0 | _, 2 | _, 3 | _, 7 | _, 8 => cases hj
    | k + 9, _ =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hi).1
      rw [hsz] at hlt; omega
    | _, k + 9 =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hj).1
      rw [hsz] at hlt; omega

/-- Partially initialized `4`-byte `PU` allocation after `_1 = PU { a: 0x55_u8 }`
in `bb6`: byte `0` holds `0x55` (initialized) and bytes `[1, 4)` are uninitialized. -/
def lm24PUU8Alloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeBytes Miri.ABI.Size.ZERO #[0x55]
      (Miri.ABI.Size.ofBytes 8) lm24PUUninitAlloc4 with
  | .ok () a => a
  | .error _ a => a

/-- Destination `4`-byte `PU` allocation after `_4 = copy _1` copies
`lm24PUU8Alloc4` into `lm24PUUninitAlloc4` (`union_copy_freshAlloc_spec`). -/
def lm24PUU8CopiedAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeUninit
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1) (Miri.ABI.Size.ofBytes 3))
      (Miri.ABI.Size.ofBytes 8)
      ((extractExceptOk
        (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[0x55, 0, 0, 0]
          (translateAlignBytes 4) .Mut)
        (by with_unfolding_all rfl)).withExtra none) with
  | .ok () a => a
  | .error _ a => a

private theorem lm24PU_copy_u8Alloc4_eq :
    Miri.Memory.Allocation.copy lm24PUU8Alloc4
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true lm24PUUninitAlloc4 =
    .ok () lm24PUU8CopiedAlloc4 := by
  obtain ⟨dest', hcopy, hsz, _, hal, hmut, hprov, hmask, _, hex, hnat, hraw⟩ :=
    union_copy_freshAlloc_spec (src := lm24PUU8Alloc4) (dest := lm24PUUninitAlloc4)
      (S := 4) (k := 1) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (by decide)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (Or.inl (by with_unfolding_all rfl)) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  rw [hcopy]
  congr 1
  exact allocation_eq_of_parts
    (hraw.trans (by with_unfolding_all rfl))
    (hsz.trans (by with_unfolding_all rfl))
    (hprov.trans (by with_unfolding_all rfl))
    (hmask.trans (by with_unfolding_all rfl))
    (hal.trans (by with_unfolding_all rfl))
    (hmut.trans (by with_unfolding_all rfl))
    (hex.trans (by with_unfolding_all rfl))
    (hnat.trans (by with_unfolding_all rfl))

def lm24PUBb6Machine1 : AnnealMachine :=
  { lm24PUMachine with
    memory :=
      { lm24PUMachine.memory with
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] } }

def lm24PUBb6Machine2 : AnnealMachine :=
  { lm24PUMachine with
    memory :=
      { lm24PUMachine.memory with
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] } }

def lm24PUBb6Miri1 : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with location := .mir ⟨6, 1⟩ }]⟩,
    machine := lm24PUBb6Machine1 }

def lm24PUBb6Miri2 (k : Nat) : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with location := .mir ⟨6, k⟩ }]⟩,
    machine := lm24PUBb6Machine2 }

private theorem lm24PU_bb6_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri1 = (lm24PUBb6Miri2 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri1).2 = .ok true := by
  let f1 := { lm24PUInitMiriFrame 6 with location := .mir ⟨6, 1⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hf4 : annealForceUnionAllocation lm24PUBody.localDecls lm24PUBody.layouts destPlace
      lm24PUBb6Miri1 =
      .ok ⟨lm24Arr2MemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hfind_src : lm24PUBb6Machine1.memory.live.find? (fun (k, _) => k == witnessAllocId) =
      some (witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }) := by
    with_unfolding_all rfl
  have hfind_dst : lm24PUBb6Machine1.memory.live.findIdx? (fun (k, _) => k == lm24SecondAllocId) =
      some 1 := by
    with_unfolding_all rfl
  have hbase_src : lm24PUBb6Machine1.lookupBaseAddr witnessAllocId = some witnessBaseAddr := by
    with_unfolding_all rfl
  have hbase_dst : lm24PUBb6Machine1.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
    with_unfolding_all rfl
  have hneq : (witnessAllocId == lm24SecondAllocId) = false := by decide
  have hmc : annealMemCopyOp lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      destPlace lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold annealMemCopyOp
    dsimp only []
    rw [EStateM.bind_eq_ok hf4]
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      lm24BaseMemPlace, lm24Arr2MemPlace, Option.bind, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri1]
    rw [hbase_src, hfind_src, hbase_dst, hfind_dst]
    dsimp only []
    have hget1 : lm24PUBb6Machine1.memory.live[1]? =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := rfl
    rw [hget1]
    dsimp only []
    have hoff1 :
        Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes witnessBaseAddr).bytes - witnessBaseAddr) =
          Miri.ABI.Size.ZERO := rfl
    have hoff2 :
        Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
          Miri.ABI.Size.ZERO := rfl
    have hlay_sz : (translateTy lm24PUTy lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
    dsimp only [destPlace]
    simp only [hoff1, hoff2, hlay_sz, hneq, lm24PU_copy_u8Alloc4_eq]
    rfl
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true lm24PUBb6Miri1 = .ok destPlace lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri1 =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri1 =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true lm24PUBb6Miri1 = .ok destPlace lm24PUBb6Miri1 from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.copy (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      lm24PUBb6Miri1 = ({ stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 }, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) lm24PUBb6Miri1 = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      lm24PUBb6Miri1 = ({ stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 }, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) lm24PUBb6Miri1 = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f1) (topFrame' := f1)
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f1) (topFrame' := f1)
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

def lm24PUU8Msc55 : Miri.Memory.ScalarInt :=
  extractExceptOk (translateScalarInt ⟨0x55, 1⟩) (by with_unfolding_all rfl)

private theorem lm24PUU8CopiedAlloc4_readScalar_u8 :
    lm24PUU8CopiedAlloc4.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) false =
    .ok (.fromScalarInt lm24PUU8Msc55) := by
  have hmask : lm24PUU8CopiedAlloc4.initializationMask = unionCopiedPrefixMask 4 1 := by
    with_unfolding_all rfl
  have hinit : lm24PUU8CopiedAlloc4.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) = .ok (.ok ()) := by
    rw [hmask]
    exact (IsUnionPrefixMask.of_copied 4 1).init (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inl rfl) (by decide) (by decide)
  exact union_readScalar_prefix (sc := ⟨0x55, 1⟩)
    ⟨Or.inl rfl, by decide, by decide, by with_unfolding_all rfl⟩
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide) (by decide)
    hinit (by with_unfolding_all rfl)

private theorem lm24PUU8CopiedAlloc4_readScalar_u32 :
    ∃ bad, lm24PUU8CopiedAlloc4.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) false =
    .error (.invalidUninitBytes (some ⟨Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4), bad⟩)) := by
  have hmask : lm24PUU8CopiedAlloc4.initializationMask = unionCopiedPrefixMask 4 1 := by
    with_unfolding_all rfl
  obtain ⟨bad, hbad⟩ : ∃ bad, lm24PUU8CopiedAlloc4.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) = .ok (.error bad) := by
    rw [hmask]
    exact (IsUnionPrefixMask.of_copied 4 1).uninit (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
  exact ⟨bad, union_readScalar_uninit hbad⟩

def lm24PUBb6Miri4 : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 4⟩ }]⟩,
    machine := lm24PUBb6Machine2 }

private theorem lm24PU_bb6_step3 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUBb6Miri2 3) = (lm24PUBb6Miri4, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUBb6Miri2 3)).2 = .ok true := by
  let f3 := { lm24PUInitMiriFrame 6 with location := .mir ⟨6, 3⟩ }
  let f3' := { lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 3⟩ }
  let m3' : AnnealStepState := { stack := ⟨#[f3']⟩, machine := lm24PUBb6Machine2 }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 2 none (.ofAllocationToken 0), translateTy lm24U8Ty lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨2, #[]⟩ true (lm24PUBb6Miri2 3) = .ok destPlace (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 1 lm24U8Ty]⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUBb6Miri2 3) =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 1 lm24U8Ty]⟩))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUBb6Miri2 3) =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hread : annealReadImmediateLM2_2
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) =
    .ok ⟨.scalar (.fromScalarInt lm24PUU8Msc55), translateTy lm24U8Ty lm24PULayouts⟩
      (lm24PUBb6Miri2 3) := by
    have hfind : lm24PUBb6Machine2.memory.live.find? (fun (k, _) => k == lm24SecondAllocId) =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }) := by
      with_unfolding_all rfl
    have hbase : lm24PUBb6Machine2.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
      with_unfolding_all rfl
    have hrel0 : Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
    have hsz0 : ((translateTy lm24U8Ty lm24PULayouts).layout.size == Miri.ABI.Size.ZERO) = false := rfl
    have hfields_sc : (translateTy lm24U8Ty lm24PULayouts).layout.fields = .Primitive := rfl
    have hsz_sc : (translateTy lm24U8Ty lm24PULayouts).layout.size = translateSizeBytes 1 := rfl
    have hrepr : (translateTy lm24U8Ty lm24PULayouts).layout.backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes 1) false)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * 1)) - 1) })) := rfl
    change annealReadIndirectImmediate lm24Arr2MemPlace
      (translateTy lm24U8Ty lm24PULayouts) (lm24PUBb6Miri2 3) = _
    unfold annealReadIndirectImmediate
    rw [show lm24Arr2MemPlace.ptr.provenance = some (.concrete lm24SecondAllocId witnessTag) from rfl,
      hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri2, hbase, hfind, lm24Arr2MemPlace, hrel0, lm24PUU8CopiedAlloc4_readScalar_u8,
      pure, EStateM.pure]
  have hwrite : annealWriteImmediateLM2_2 (.scalar (.fromScalarInt lm24PUU8Msc55))
      destPlace (lm24PUBb6Miri2 3) = .ok () m3' := by
    with_unfolding_all rfl
  have huse : usesMemCopy ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ = false := rfl
  have hval : annealValidateOpLM2_4PaddedZst lm24PUBody.layouts
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) =
      .ok () (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) ⟨2, #[]⟩ (lm24PUBb6Miri2 3) =
    .ok () m3' := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    dsimp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      annealRvalueHooks]
    rw [EStateM.bind_eq_ok hval]
    simp only [huse, Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hread]
    exact hwrite
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) ⟨2, #[]⟩ (lm24PUBb6Miri2 3) =
    .ok () m3' := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨2, #[]⟩ true (lm24PUBb6Miri2 3) = .ok destPlace (lm24PUBb6Miri2 3) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hread]
    exact hwrite
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨2, #[]⟩
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) = true := by
    with_unfolding_all rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))))
      (lm24PUBb6Miri2 3) = (m3', .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨2, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) (lm24PUBb6Miri2 3) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))))
      (lm24PUBb6Miri2 3) = (m3', .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨2, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) (lm24PUBb6Miri2 3) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f3) (topFrame' := f3')
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 3) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f3) (topFrame' := f3')
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 3) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

private theorem lm24PU_bb6_step4 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri4).2 = .error (.undefinedBehavior "read of uninitialized memory field") := by
  let f4 := { lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 4⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 3 none (.ofAllocationToken 0), translateTy lm24U32Ty lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨3, #[]⟩ true lm24PUBb6Miri4 = .ok destPlace lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 2 lm24U32Ty]⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri4 =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 2 lm24U32Ty]⟩))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri4 =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  obtain ⟨bad, hread_sc⟩ := lm24PUU8CopiedAlloc4_readScalar_u32
  have hread : annealReadImmediateLM2_2
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    have hfind : lm24PUBb6Machine2.memory.live.find? (fun (k, _) => k == lm24SecondAllocId) =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }) := by
      with_unfolding_all rfl
    have hbase : lm24PUBb6Machine2.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
      with_unfolding_all rfl
    have hrel0 : Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
    have hsz0 : ((translateTy lm24U32Ty lm24PULayouts).layout.size == Miri.ABI.Size.ZERO) = false := rfl
    have hfields_sc : (translateTy lm24U32Ty lm24PULayouts).layout.fields = .Primitive := rfl
    have hsz_sc : (translateTy lm24U32Ty lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
    have hrepr : (translateTy lm24U32Ty lm24PULayouts).layout.backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes 4) false)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * 4)) - 1) })) := rfl
    change annealReadIndirectImmediate lm24Arr2MemPlace
      (translateTy lm24U32Ty lm24PULayouts) lm24PUBb6Miri4 = _
    unfold annealReadIndirectImmediate
    rw [show lm24Arr2MemPlace.ptr.provenance = some (.concrete lm24SecondAllocId witnessTag) from rfl,
      hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri4, hbase, hfind, lm24Arr2MemPlace, hrel0, hread_sc,
      throw, throwThe]
    rfl
  have huse : usesMemCopy ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ = false := rfl
  have hval_err : annealValidateOpLM2_4PaddedZst lm24PUBody.layouts
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 =
      .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) ⟨3, #[]⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    dsimp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      annealRvalueHooks]
    exact EStateM.bind_eq_error hval_err
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) ⟨3, #[]⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨3, #[]⟩ true lm24PUBb6Miri4 = .ok destPlace lm24PUBb6Miri4 from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    exact EStateM.bind_eq_error hread
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨3, #[]⟩
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) = true := by
    with_unfolding_all rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))))
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨3, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) lm24PUBb6Miri4 = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))))
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨3, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) lm24PUBb6Miri4 = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_error
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f4) rfl rfl rfl (blockIdx := 6) (stmtIdx := 4) rfl rfl hstmt
  · have h := miri_step_at_statement_error
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f4) rfl rfl rfl (blockIdx := 6) (stmtIdx := 4) rfl rfl hstmt_base
    exact congrArg Prod.snd h
/-- **Kernel-checked 5-step execution of `bb6` in `lm24PUBody` (`G3`: partially
initialized padded-union whole copy + `[(); 4][2 of 4]` read on partially
initialized storage + `u8` read + `u32` read UB)**:
1. `_1 = PU { a: 0x55_u8 }` initializes byte `0` of `_1` to `0x55`, leaving
   bytes `[1, 4)` uninitialized;
2. `_4 = copy _1` copies the partially initialized `PU` into `_4`
   (`lm24PU_copy_u8Alloc4_eq`, preserving byte `0 = 0x55` and bytes `[1, 4)`
   uninitialized in `lean-miri`'s `InitMask`);
3. `_7 = copy (_4.0[2 of 4]: ())` reads element `2 < 4` of the `[(); 4]` ZST arm
   on partially initialized `_4`, succeeding in both Anneal (`zstUnitVal`) and
   `lean-miri`;
4. `_2 = copy (_4.1: u8)` reads back `0x55_u8` from byte `0` of `_4` in both;
5. `_3 = copy (_4.2: u32)` reads the wider `u32` arm of `_4` across uninitialized
   bytes `[1, 4)`, faulting with `.ub` in both machines. -/
theorem lm24_padded_zst_partial_init_whole_copy_and_elem_index_steps :
    let s₀ := lm24PUInitAnneal 6
    let s₁ := lm24PUAnnealState 6 1
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₂ := lm24PUAnnealState 6 2
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₃ := lm24PUAnnealState 6 3
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .init zstUnitVal, .uninit]
    let s₄ := lm24PUAnnealState 6 4
      [.uninit, lm24PUU8Slot 0x55, .init (.scalar ⟨0x55, 1⟩), .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .init zstUnitVal, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    StateRelLM2_4PaddedZst lm24PUBody s₀ (lm24PUInitMiri 6) ∧
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .step s₄ ∧
    stepMirFn lm24PUBody s₄ = .fail .ub ∧
    ∃ m₁ m₂ m₃ m₄ m₅ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 6) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 6)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₄ =
        (m₅, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₄).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨lm24PUInit_stateRel 6, rfl, rfl, rfl, rfl, rfl,
    lm24PUBb6Miri1, lm24PUBb6Miri2 2, lm24PUBb6Miri2 3, lm24PUBb6Miri4, lm24PUBb6Miri4,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    lm24PU_bb6_step1.1,
    lm24PU_bb6_step1.2,
    by with_unfolding_all rfl,
    lm24PU_bb6_step3.1,
    lm24PU_bb6_step3.2,
    lm24PU_bb6_step4.1,
    lm24PU_bb6_step4.2⟩

/-! ### General Step Simulation Theorems for Padded ZST Unions (`G3`) -/

/-- **`lean-miri` side of an uninhabited zero-variant union field read (`G3`, `kani#5159`)**:
For any `StateRelLM2_4PaddedZst body s m` and statement
`⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩` where `voidTy`
encodes a zero-variant empty ADT (`100 ≤ encodeTyId voidTy < 1000`,
`voidTl.variants = .empty`, `voidTl.fields = .arbitrary [] []`), with `r ≠ u`
and the union local `u` memory-backed (`.live (.indirect mp_u)` with
`mp_u.metadata = .none`), `Step.step (annealStepHooksLM2_4PaddedZst ..) () m`
projects field `j` via vendored `Miri.Interpreter.projectField` and then runs
vendored `Miri.Interpreter.ValidityVisitor.validatePlace` inside `copyOp`,
faulting with `"validation: zero-variant enum value"`. Anneal's fault is the
hypothesis `hstep_a`, not a conclusion; the concrete witness
`lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps` evaluates it on
`lm24PUBody` and `step_padded_zst_union_uninhabited_field_read_ub_two_sided`
proves both sides. -/
theorem step_padded_zst_union_uninhabited_field_read_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    {bb : BasicBlockData} {r u j n : Nat} {voidTy : Ty} {voidTl : TypeLayout} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hun_u : isUnionLocal body.localDecls body.layouts u = true)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj_lt : j < n)
    (hvoid_lo : 100 ≤ encodeTyId voidTy)
    (hvoid_hi : encodeTyId voidTy < 1000)
    (hvoid_lookup : body.layouts.lookup (encodeTyId voidTy - 100) = some voidTl)
    (hvoid_var : voidTl.variants = .empty)
    (hvoid_fields : voidTl.fields = .arbitrary .nil .nil)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hmeta : mp_u.metadata = .none)
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hstep_a : stepMirFn body s = MirStepNode.fail .ub) :
    StepRelLM2_4PaddedZst body m (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _, _⟩
  obtain ⟨_, mls_r, _, hlt_r, _, _, hmls_r_eq, hloc_r⟩ := hframe.lookup_local hdecl_r
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨uC, hmls_u⟩ := hu_ind topFrame hframes
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_r := hloc_r.layout_eq
  have hcache_u := hloc_u.layout_eq
  let layR := translateTy rDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame r hlt_r layR
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, layR⟩
  have hevalPlace : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
      ⟨r, #[]⟩ true m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r hdecl_r (by rw [hmls_r_eq]; exact hcache_r)
  have hframes₀ : m₀.stack.frames = #[topFrame₀] := rfl
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), uC⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hru] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₀' : AnnealStepState := { m₀ with stack := ⟨#[topFrame₁]⟩ }
  have hres_u : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m₀ =
      .ok (topFrame₁, layU) m₀' :=
    annealResolveAndCacheLocalLayout_eq hframes₀ hlt_u₀ hdecl_u
      (by rw [hmls_u₀]; exact hcache_u)
  have hget_u₁ : topFrame₁.getLocalOperand u = .ok (.indirect mp_u) :=
    frame_getLocalOperand_live topFrame₁
      (by rw [cacheFrameLocalLayout_getLocal, hmls_u₀])
  let voidLay : Miri.Interpreter.LocalLayout :=
    { ty := encodeTyId voidTy, layout := translateTypeLayout voidTl }
  have hloN : (100 : Nat) ≤ (encodeTyId voidTy : Nat) := hvoid_lo
  have hhiN : (encodeTyId voidTy : Nat) < 1000 := hvoid_hi
  obtain ⟨voidIdx, hvoidEq⟩ : ∃ k : Nat, encodeTyId voidTy = k + 100 :=
    ⟨encodeTyId voidTy - 100, (Nat.sub_add_cancel hloN).symm⟩
  have hvoidLo' : 100 ≤ voidIdx + 100 := Nat.le_add_left 100 voidIdx
  have hvoidHi' : voidIdx + 100 < 1000 := by rw [← hvoidEq]; exact hhiN
  have hvoidSub' : voidIdx + 100 - 100 = voidIdx := Nat.add_sub_cancel voidIdx 100
  have hvoidLook' : body.layouts.lookup voidIdx = some voidTl := by
    have := hvoid_lookup; rw [hvoidEq, hvoidSub'] at this; exact this
  have hnotArr : (annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
      body.layouts (encodeTyId voidTy)).isSome = false := by
    unfold annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
    have hlt : ¬ (encodeTyId voidTy ≥ 1000) := Nat.not_le.mpr hhiN
    simp [hlt]
  have hlayVoid : layoutOfEncodedTyId (encodeTyId voidTy) body.layouts = voidLay := by
    dsimp only [voidLay]
    rw [hvoidEq]
    unfold layoutOfEncodedTyId
    simp only [hvoidSub', hvoidLook']
  have hprojVoid : Miri.Interpreter.projectField
      (annealUnionProjectionCx topFrame₁ body.layouts m₀'.machine (encodeTyId voidTy))
      ⟨.indirect mp_u, layU⟩ j = .ok ⟨.indirect mp_u, voidLay⟩ := by
    have hoff : (Miri.ABI.FieldsShape.Union n).offset j = .ok Miri.ABI.Size.ZERO := by
      unfold Miri.ABI.FieldsShape.offset Miri.ABI.FieldsShape.count
      have : ¬ j ≥ n := by omega
      simp [this, pure, Except.pure]
    have hsized : voidLay.layout.isSized = true := by
      cases hbr : voidTl.backendRepr <;>
        simp [voidLay, translateTypeLayout, hbr, translateBackendRepr, Miri.ABI.LayoutData.isSized,
          Miri.ABI.BackendRepr.isSized, Miri.ABI.BackendRepr.isUnsized]
    have hfields' : layU.layout.fields = .Union n := hfields
    unfold Miri.Interpreter.projectField
    simp only [annealUnionProjectionCx, annealProjectionCx, hfields', hlayVoid, hoff,
      Except.mapError, hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    unfold Miri.Interpreter.OpTy.offsetWithMeta
    simp only [bind, Except.bind, projectionMemoryOffset_zero,
      memPlace_offset_zero_eq mp_u hmeta, pure, Except.pure]
  have hop_ok : ∀ known,
      annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
        (translateOperand (.copy ⟨u, [.field j voidTy]⟩)) known m₀ =
      .ok ⟨.indirect mp_u, voidLay⟩ m₀' := by
    intro known
    dsimp only [translateOperand]
    rw [(annealEvalOperandLM2_4PaddedZst_eq_of_non_zstArray_field body.localDecls body.layouts
      (translatePlace ⟨u, [.field j voidTy]⟩) j (encodeTyId voidTy) known rfl hnotArr).1]
    unfold annealEvalOperandLM2_4
    dsimp only
    rw [show (translatePlace ⟨u, [.field j voidTy]⟩).localId = u from rfl,
        show (translatePlace ⟨u, [.field j voidTy]⟩).projection.toList =
          [.Field j (encodeTyId voidTy)] from rfl]
    simp only [hun_u, ↓reduceIte]
    unfold annealEvalUnionField
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      stack_currentFrame?_singleton m₀.stack topFrame₀ hframes₀,
      Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hres_u, hget_u₁,
      hprojVoid, pure, EStateM.pure]
  have hclassVoid : annealUnionValidityClassify body.layouts (encodeTyId voidTy) m₀' =
      .ok (.aggregate false false true) m₀' := by
    rw [hvoidEq]
    unfold annealUnionValidityClassify
    simp only [hvoidLo', hvoidHi', and_self, ↓reduceIte, hvoidSub', hvoidLook', hvoid_var,
      pure, EStateM.pure]
  have hval_err : annealValidateOpLM2_4PaddedZst body.layouts ⟨.indirect mp_u, voidLay⟩ m₀' =
      .error (.undefinedBehavior "validation: zero-variant enum value") m₀' := by
    unfold annealValidateOpLM2_4PaddedZst Miri.Interpreter.ValidityVisitor.validatePlace
    simp only [annealUnionValidityHooks, Bool.false_eq_true, ↓reduceIte,
      pure, Pure.pure, EStateM.pure, bind, Bind.bind, EStateM.bind]
    unfold Miri.Interpreter.ValidityVisitor.visit
    simp only [annealUnionValidityHooks, bind, Bind.bind, EStateM.bind]
    rw [hclassVoid]
    simp only [voidLay, translateTypeLayout, hvoid_fields, hvoid_var,
      translateFieldsShape, translateVariantsShape,
      pure, Pure.pure, EStateM.pure, bind, Bind.bind, EStateM.bind]
    rfl
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (.copy ⟨u, [.field j voidTy]⟩))) = true := by
    simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
      translatePlace, hun_u]
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩) m =
      (m₀', .error (.undefinedBehavior "validation: zero-variant enum value")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace]
    dsimp only [translateRvalue, annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4,
      annealRvalueHooksLM2_2, annealRvalueHooks]
    rw [EStateM.bind_eq_ok (hop_ok _)]
    rw [EStateM.bind_eq_error hval_err]
  have hstep_m := miri_step_at_statement_error
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt
  rw [hstep_a, hstep_m]
  exact .ub m₀' "validation: zero-variant enum value"

/-- **`lean-miri` side of well-formed `[(); N][offset of minLen]` element reads (`G3`)**.
As in `step_padded_zst_union_uninhabited_field_read_ub`, Anneal's fault in item 1
is the hypothesis `hstep_a`, and item 2 states only the `lean-miri` operand
read:
For any `StateRelLM2_4PaddedZst body s m` (with `LiveAllocsNodup m.machine`) and
well-formed statement
`⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩`
(`offset < minLen`, `N, minLen, offset < 2^64`) where `_u` is a memory-backed
padded ZST union (`WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx`,
`unionZstArrayElemCount? body.layouts (encodeTyId zstArrTy) = some N`, `mp_u.metadata = .none`):
1. **Out-of-bounds (`N < minLen`)**:
   vendored `Miri.Interpreter.projectField` + `Miri.Interpreter.projectConstantIndex`
   (inside `annealEvalUnionZstElem`) faults with
   `s!"bounds check failed: index {UInt64.ofNat N} >= len {UInt64.ofNat minLen}"`,
   and when `stepMirFn body s = MirStepNode.fail .ub`, satisfies `StepRelLM2_4PaddedZst.ub`;
2. **In-bounds (`minLen ≤ N`)**:
   vendored `Miri.Interpreter.projectField` + `projectConstantIndex` + `projectIndex`
   evaluates the element read to
   `⟨.indirect mp_u, { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩`,
   and `annealReadImmediate_zstLayoutData` reads `Immediate.uninit` in 0 bytes
   without inspecting `mp_u`'s initialization mask! -/
theorem step_padded_zst_union_elem_index_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : BasicBlockData} {r u S n N f_z zstFlIdx offset minLen : Nat}
    {zstArrTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩
        (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hfz_lt : f_z < n)
    (hcnt : annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
      body.layouts (encodeTyId zstArrTy) = some N)
    (hWf : offset < minLen)
    (hN64 : N < 2 ^ 64)
    (hMin64 : minLen < 2 ^ 64)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hmeta : mp_u.metadata = .none)
    (hprov : mp_u.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) :
    (N < minLen →
      stepMirFn body s = MirStepNode.fail .ub →
      StepRelLM2_4PaddedZst body m (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m)) ∧
    (minLen ≤ N →
      ∀ known,
        ∃ m',
          (do
            let opTy ← annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
              (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
              known
            annealReadImmediateLM2_2 opTy) m =
          .ok ⟨.uninit,
            { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩ m') := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _, _⟩
  have hun_u : isUnionLocal body.localDecls body.layouts u = true :=
    isUnionLocal_of_wellTypedPaddedZst hdecl_u hwt
  obtain ⟨_, mls_r, _, hlt_r, _, _, hmls_r_eq, hloc_r⟩ := hframe.lookup_local hdecl_r
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨uC, hmls_u⟩ := hu_ind topFrame hframes
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_r := hloc_r.layout_eq
  have hcache_u := hloc_u.layout_eq
  let layR := translateTy rDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  -- Unpack `unionZstArrayElemCount? = some N`
  have hcnt_parts : encodeTyId zstArrTy ≥ 1000 ∧ encodeTyId zstArrTy % 100 = 51 ∧
      ∃ zstTl, body.layouts.lookup ((encodeTyId zstArrTy - 1000) / 100) = some zstTl ∧
        zstTl.fields = .array ⟨0⟩ N := by
    unfold annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount? at hcnt
    split at hcnt
    · rename_i hge
      have hge1 : encodeTyId zstArrTy ≥ 1000 := by
        have := Bool.and_eq_true_iff.mp hge; exact of_decide_eq_true this.1
      have hmod : encodeTyId zstArrTy % 100 = 51 := by
        have := Bool.and_eq_true_iff.mp hge; exact of_decide_eq_true this.2
      cases hl : body.layouts.lookup ((encodeTyId zstArrTy - 1000) / 100) with
      | none => simp only [hl] at hcnt; cases hcnt
      | some zstTl =>
        simp only [hl] at hcnt
        split at hcnt
        · cases hf : zstTl.fields with
          | array stride cnt =>
            rw [hf] at hcnt
            dsimp only at hcnt
            split at hcnt
            · rename_i hs0
              have hs0' : stride = ⟨0⟩ := by
                cases stride with | mk b => congr; exact of_decide_eq_true hs0
              injection hcnt with hN
              subst hN hs0'
              exact ⟨hge1, hmod, zstTl, rfl, hf⟩
            · cases hcnt
          | _ => rw [hf] at hcnt; cases hcnt
        · cases hcnt
    · cases hcnt
  obtain ⟨harr_ge, harr_mod, zstTl, hzst_lookup, hzst_fields⟩ := hcnt_parts
  let zstArrLay : Miri.Interpreter.LocalLayout :=
    { ty := encodeTyId zstArrTy, layout := translateTypeLayout zstTl }
  have hlayArr : layoutOfEncodedTyIdPaddedZst (encodeTyId zstArrTy) body.layouts = zstArrLay := by
    unfold layoutOfEncodedTyIdPaddedZst
    simp only [harr_ge, ↓reduceIte, hzst_lookup]
    rfl
  have hprojField : ∀ tf mach,
      Miri.Interpreter.projectField
        (annealUnionPaddedZstProjectionCx tf body.layouts mach (encodeTyId zstArrTy))
        ⟨.indirect mp_u, layU⟩ f_z = .ok ⟨.indirect mp_u, zstArrLay⟩ := by
    intro tf mach
    have hoff : (Miri.ABI.FieldsShape.Union n).offset f_z = .ok Miri.ABI.Size.ZERO := by
      unfold Miri.ABI.FieldsShape.offset Miri.ABI.FieldsShape.count
      have : ¬ f_z ≥ n := by omega
      simp [this, pure, Except.pure]
    have hsized : zstArrLay.layout.isSized = true := by
      cases hbr : zstTl.backendRepr <;>
        simp [zstArrLay, translateTypeLayout, hbr, translateBackendRepr, Miri.ABI.LayoutData.isSized,
          Miri.ABI.BackendRepr.isSized, Miri.ABI.BackendRepr.isUnsized]
    have hfields' : layU.layout.fields = .Union n := hfields
    unfold Miri.Interpreter.projectField
    simp only [annealUnionPaddedZstProjectionCx, annealProjectionCx, hfields', hlayArr, hoff,
      Except.mapError, hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    unfold Miri.Interpreter.OpTy.offsetWithMeta
    simp only [bind, Except.bind, projectionMemoryOffset_zero,
      memPlace_offset_zero_eq mp_u hmeta, pure, Except.pure]
  have hlenArr : ∀ cx,
      Miri.Interpreter.OpTy.len cx ⟨.indirect mp_u, zstArrLay⟩ = .ok (UInt64.ofNat N) := by
    intro cx
    have hsized : zstArrLay.layout.isSized = true := by
      cases hbr : zstTl.backendRepr <;>
        simp [zstArrLay, translateTypeLayout, hbr, translateBackendRepr, Miri.ABI.LayoutData.isSized,
          Miri.ABI.BackendRepr.isSized, Miri.ABI.BackendRepr.isUnsized]
    unfold Miri.Interpreter.OpTy.len
    rw [hsized]
    simp [zstArrLay, translateTypeLayout, hzst_fields, translateFieldsShape]
    rfl
  let topFrame₀ := cacheFrameLocalLayout topFrame r hlt_r layR
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, layR⟩
  have hevalPlace : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
      ⟨r, #[]⟩ true m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r hdecl_r (by rw [hmls_r_eq]; exact hcache_r)
  have hframes₀ : m₀.stack.frames = #[topFrame₀] := rfl
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), uC⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hru] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₀' : AnnealStepState := { m₀ with stack := ⟨#[topFrame₁]⟩ }
  have hres_u : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m₀ =
      .ok (topFrame₁, layU) m₀' :=
    annealResolveAndCacheLocalLayout_eq hframes₀ hlt_u₀ hdecl_u
      (by rw [hmls_u₀]; exact hcache_u)
  have hget_u₁ : topFrame₁.getLocalOperand u = .ok (.indirect mp_u) :=
    frame_getLocalOperand_live topFrame₁
      (by rw [cacheFrameLocalLayout_getLocal, hmls_u₀])
  have hOff64 : offset < 2 ^ 64 := by omega
  have hNoOvf : (decide (offset ≥ 2 ^ 64) || decide (minLen ≥ 2 ^ 64)) = false := by
    simp [Nat.not_le.mpr hOff64, Nat.not_le.mpr hMin64]
  refine ⟨fun hoob hstep_a => ?_, fun hinb known => ?_⟩
  · have hlt64 : UInt64.ofNat N < UInt64.ofNat minLen := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt hMin64]
      exact hoob
    have hprojErr : annealProjectList
        (annealUnionPaddedZstProjectionCx topFrame₁ body.layouts m₀'.machine (encodeTyId zstArrTy))
        ⟨.indirect mp_u, layU⟩
        [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] =
        .error (.bounds (UInt64.ofNat minLen) (UInt64.ofNat N)) := by
      dsimp only [annealProjectList, Miri.Interpreter.project]
      rw [hprojField]
      dsimp only [bind, Except.bind, annealProjectList, Miri.Interpreter.project]
      rw [hNoOvf]
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Miri.Interpreter.projectConstantIndex
      rw [hlenArr]
      simp only [bind, Except.bind, hlt64, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
    let errMsg : String := s!"bounds check failed: index {UInt64.ofNat N} >= len {UInt64.ofNat minLen}"
    have hop_err : ∀ known,
        annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
          (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
          known m₀ =
        .error (.undefinedBehavior errMsg) m₀' := by
      intro known
      unfold annealEvalOperandLM2_4PaddedZst
      dsimp only [translateOperand]
      rw [show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).localId = u from rfl,
          show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).projection.toList =
            [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] from rfl]
      simp only [hun_u, ↓reduceIte, hcnt, Option.isSome_some]
      unfold annealEvalUnionZstElem
      simp only [get, getThe, MonadStateOf.get, EStateM.get,
        pure, EStateM.pure, bind, EStateM.bind,
        stack_currentFrame?_singleton m₀.stack topFrame₀ hframes₀,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hres_u, hget_u₁, hprojErr,
        annealLiftProjectionError, throw, throwThe]
      rfl
    have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
        (translateRvalue
          (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))) = true := by
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        translatePlace, hun_u]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨r, .nil⟩
          (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩) m =
        (m₀', .error (.undefinedBehavior errMsg)) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
      simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
      unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok hevalPlace]
      dsimp only [translateRvalue, annealRvalueHooksLM2_4PaddedZst]
      rw [EStateM.bind_eq_error (hop_err _)]
    have hstep_m := miri_step_at_statement_error
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt
    rw [hstep_a, hstep_m]
    exact .ub m₀' errMsg
  · have hmls_u_eq : topFrame.locals[u]'hlt_u = ⟨.live (.indirect mp_u), uC⟩ := by
      have h0 := Array.getElem?_eq_getElem hlt_u
      rw [hmls_u] at h0; exact (Option.some.inj h0).symm
    let tf_u := cacheFrameLocalLayout topFrame u hlt_u layU
    let m_u : AnnealStepState := { m with stack := ⟨#[tf_u]⟩ }
    have hres_m : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m =
        .ok (tf_u, layU) m_u :=
      annealResolveAndCacheLocalLayout_eq hframes hlt_u hdecl_u
        (by rw [hmls_u_eq]; exact hcache_u)
    have hget_u : tf_u.getLocalOperand u = .ok (.indirect mp_u) :=
      frame_getLocalOperand_live tf_u
        (by rw [cacheFrameLocalLayout_getLocal, hmls_u_eq])
    have hnotLt : ¬ (UInt64.ofNat N < UInt64.ofNat minLen) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt hMin64]
      omega
    have hnotGeMin : ¬ (UInt64.ofNat offset ≥ UInt64.ofNat minLen) := by
      show ¬ (UInt64.ofNat minLen ≤ UInt64.ofNat offset)
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hMin64, Nat.mod_eq_of_lt hOff64]
      omega
    have hnotGeN : ¬ (UInt64.ofNat offset ≥ UInt64.ofNat N) := by
      show ¬ (UInt64.ofNat N ≤ UInt64.ofNat offset)
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt hOff64]
      omega
    have helemLay : arrayElemLayoutOf body.layouts zstArrLay Miri.ABI.Size.ZERO =
        { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData } := by
      unfold arrayElemLayoutOf
      dsimp only [zstArrLay]
      have hge1 : encodeTyId zstArrTy ≥ 1000 := harr_ge
      have hmod51 : (encodeTyId zstArrTy - 1000) % 100 = 51 := by
        let n0 : Nat := encodeTyId zstArrTy
        have h1 : n0 ≥ 1000 := harr_ge
        have h2 : n0 % 100 = 51 := harr_mod
        change (n0 - 1000) % 100 = 51
        omega
      simp only [hge1, ↓reduceIte, hmod51]
      rfl
    have hcomp0 : Miri.Interpreter.IntegerOps.computeSizeInBytes
        Miri.ABI.Size.ZERO (UInt64.ofNat offset) (Miri.ABI.Size.ofBytes 0x7fffffffffffffff) =
        some Miri.ABI.Size.ZERO := by
      unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
      simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    have hfieldsArr : zstArrLay.layout.fields = .Array Miri.ABI.Size.ZERO (UInt64.ofNat N) := by
      simp [zstArrLay, translateTypeLayout, hzst_fields, translateFieldsShape, translateSize,
        translateSizeBytes, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    have hprojOk : annealProjectList
        (annealUnionPaddedZstProjectionCx tf_u body.layouts m_u.machine (encodeTyId zstArrTy))
        ⟨.indirect mp_u, layU⟩
        [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] =
        .ok ⟨.indirect mp_u,
          { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩ := by
      dsimp only [annealProjectList, Miri.Interpreter.project]
      rw [hprojField]
      dsimp only [bind, Except.bind, annealProjectList, Miri.Interpreter.project]
      rw [hNoOvf]
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Miri.Interpreter.projectConstantIndex
      rw [hlenArr]
      simp only [hnotLt, ↓reduceIte, Bool.false_eq_true, hnotGeMin, pure, Except.pure,
        bind, Except.bind]
      unfold Miri.Interpreter.projectIndex
      rw [hfieldsArr, hlenArr]
      simp only [hnotGeN, ↓reduceIte, hcomp0, annealUnionPaddedZstProjectionCx,
        annealProjectionCx, hfieldsArr, bind, Except.bind]
      rw [helemLay]
      unfold Miri.Interpreter.OpTy.offset Miri.Interpreter.OpTy.offsetWithMeta
      simp only [bind, Except.bind, projectionMemoryOffset_zero,
        memPlace_offset_zero_eq mp_u hmeta, pure, Except.pure]
      rfl
    have hop_ok : annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
        (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
        known m =
      .ok ⟨.indirect mp_u,
        { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩ m_u := by
      unfold annealEvalOperandLM2_4PaddedZst
      dsimp only [translateOperand]
      rw [show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).localId = u from rfl,
          show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).projection.toList =
            [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] from rfl]
      simp only [hun_u, ↓reduceIte, hcnt, Option.isSome_some]
      unfold annealEvalUnionZstElem
      simp only [get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, stack_currentFrame?_singleton m.stack topFrame hframes,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hres_m, hget_u, hprojOk,
        pure, EStateM.pure]
    have hread := annealReadImmediate_zstLayoutData (m := m_u) hnodup
      (tyId := encodeTyId { kind := .tuple [], layoutIdx := 0 }) hprov hlive hbase
    refine ⟨m_u, ?_⟩
    simp only [bind, EStateM.bind]
    rw [hop_ok]
    exact hread

/-- **`lean-miri` side of a 0-byte `[(); N]` field write (`G3`)**: the memory
copy is a no-op, and the given Anneal slots relate to the unchanged memory
under `PaddedZstUnionLocalRel`. That Anneal's step produces those slots is not
proved here; the concrete witnesses `lm24_padded_zst_field_write_move_and_u32_ub_steps`
and `lm24_padded_zst_overwrite_payload_retains_bytes_steps` evaluate it:
Writing a 0-byte `[(); N]` ZST local `z` (`ZstZeroMemRel m.machine mp_z`,
`zLay.layout.size = Miri.ABI.Size.ZERO`) into field `f_z` (`fLay.layout.size = Miri.ABI.Size.ZERO`)
of a memory-backed union `u` (`ValidScalarBytes S`, either `PaddedZstUnionUninitMemRel`
for an uninitialized union `_u.f_z = copy _z`, or `UnionMemRel` for an initialized
union `_u.f_z = copy _z` producing the `D13a` raw-byte overlay `zstOverlay`)
via `annealMemCopyOp`:
1. In `lean-miri`, `annealMemCopyOp` succeeds in-place (`.ok () m`), preserving
   both `PaddedZstUnionUninitMemRel` (establishing `PaddedZstUnionLocalRel.zstUninit`)
   and `UnionMemRel` (establishing `PaddedZstUnionLocalRel.zstOverlay`);
2. In Anneal, when `_u` holds `.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))`
   (`UnionLocalRel.union`) or `.uninit` (`PaddedZstUnionLocalRel.uninitIndirect`),
   updating `_u`'s slot to `.init (.aggregate 0 (List.replicate n .unit))` (from `.uninit`)
   or `.init (.aggregate 0 (List.replicate n .unit ++ [.aggregate 0 (encodeRawAbstractByteVals (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++ replicateUninitBytes (S - sc.sizeBytes)))]))` (from `.init`)
   establishes `PaddedZstUnionLocalRel` (`zstUninit` and `zstOverlay`). -/
theorem step_padded_zst_union_field_write_and_overlay_rel
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp_u mp_z : Miri.Interpreter.MemPlace AnnealProv}
    {cachedLayout : Option Miri.Interpreter.LocalLayout}
    (hc : ∀ l ∈ cachedLayout, l = translateTy uDecl.ty body.layouts)
    (hz : ZstZeroMemRel m.machine mp_z)
    {zLay fLay : Miri.Interpreter.LocalLayout}
    (hf0 : fLay.layout.size = Miri.ABI.Size.ZERO) :
    (PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u →
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_z, zLay⟩ ⟨.memory mp_u, fLay⟩ m =
        .ok () m ∧
      PaddedZstUnionLocalRel m.machine uDecl body.layouts
        (.init (.aggregate 0 (List.replicate n .unit)))
        ⟨.live (.indirect mp_u), cachedLayout⟩) ∧
    (∀ f0Ty sc,
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_z, zLay⟩ ⟨.memory mp_u, fLay⟩ m =
        .ok () m ∧
      PaddedZstUnionLocalRel m.machine uDecl body.layouts
        (.init (.aggregate 0
          (List.replicate n .unit ++
            [.aggregate 0
              (encodeRawAbstractByteVals
                (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
                  replicateUninitBytes (S - sc.sizeBytes)))])))
        ⟨.live (.indirect mp_u), cachedLayout⟩) := by
  cases hz with
  | mk srcAllocId srcTag srcBaseAddr srcLa hprov_z _ _ hlive_z hbase_z hptr_z hsz_z hlen_z _ =>
    have hlen_src : srcLa.allocation.len = srcLa.allocation.byteSize.bytes.toNat := by
      rw [hlen_z, hsz_z]; rfl
    refine ⟨fun hun => ?_, fun f0Ty sc hmem => ?_⟩
    · cases hun with
      | mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
        exact ⟨annealMemCopyOp_zero_into_union_field body.localDecls body.layouts hnodup
            hwt.size_valid hprov hlive hbase hptr hsz hlen hmut hprov_z hlive_z hbase_z hptr_z
            hlen_src hf0,
          .zstUninit S n N f_z zstFlIdx mp_u cachedLayout hc hwt hfields
            (.mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
              hp hal hex hnat hmask)⟩
    · cases hmem with
      | mk allocId tag baseAddr la msc hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
          hp hal hex hnat hkle hmask hsc hprim hf0imm hraw =>
        exact ⟨annealMemCopyOp_zero_into_union_field body.localDecls body.layouts hnodup
            hwt.size_valid hprov hlive hbase hptr hsz hlen hmut hprov_z hlive_z hbase_z hptr_z
            hlen_src hf0,
          .zstOverlay S n N f_z zstFlIdx f0Ty sc mp_u cachedLayout hc hwt hfields
            (.mk allocId tag baseAddr la msc hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
              hp hal hex hnat hkle hmask hsc hprim hf0imm hraw)⟩

/-- **`lean-miri` side of a 0-byte `[(); N]` aggregate field copy (`G3`)**: a
lemma about `annealAggregateHooksLM2_4PaddedZst.copyOpNoValidate`, with no
Anneal side:
For any memory-backed union `mp_u` satisfying `PaddedZstUnionUninitMemRel`
(and `LiveAllocsNodup m.machine`), writing a zero-sized `[(); N]` source operand
`src` (`src.layout.layout.size.bytes == 0`) into the zero-sized union field
destination `⟨.memory mp_u, fLay⟩` (`fLay.layout.size.bytes == 0`) via
`(annealAggregateHooksLM2_4PaddedZst body.localDecls body.layouts).copyOpNoValidate`
succeeds in-place (`.ok () m`) and establishes `PaddedZstUnionLocalRel.zstUninit`. -/
theorem step_padded_zst_union_aggregate_copyOpNoValidate_spec
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {cachedLayout : Option Miri.Interpreter.LocalLayout}
    (hc : ∀ l ∈ cachedLayout, l = translateTy uDecl.ty body.layouts)
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u)
    {src : Miri.Interpreter.OpTy AnnealProv} {fLay : Miri.Interpreter.LocalLayout}
    (hsrc0 : (src.layout.layout.size.bytes == 0) = true)
    (hdst0 : (fLay.layout.size.bytes == 0) = true) (b : Bool) :
    (annealAggregateHooksLM2_4PaddedZst body.localDecls body.layouts).copyOpNoValidate ()
      src ⟨.memory mp_u, fLay⟩ b m = .ok () m ∧
    PaddedZstUnionLocalRel m.machine uDecl body.layouts
      (.init (.aggregate 0 (List.replicate n .unit)))
      ⟨.live (.indirect mp_u), cachedLayout⟩ := by
  cases hmem with
  | mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    refine ⟨?_, .zstUninit S n N f_z zstFlIdx mp_u cachedLayout hc hwt hfields
      (.mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
        hp hal hex hnat hmask)⟩
    unfold annealAggregateHooksLM2_4PaddedZst
    dsimp only
    simp [hsrc0, hdst0, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId, hfind, pure, EStateM.pure]

/-- **`lean-miri` side of an uninitialized scalar payload read (`G3`)**: a
lemma about `annealReadImmediateLM2_2` on all-uninit union storage, together
with the all-uninit encoding of Anneal's ZST-initialized union value; it does
not state Anneal's read:
For any memory-backed union `mp_u` in `PaddedZstUnionUninitMemRel`
(and `LiveAllocsNodup m.machine`) and any primitive scalar field layout `fLay`
of width `w` (`ValidScalarBytes w`, `w ≤ S`,
`fLay.layout = scalarLayoutData (translateSizeBytes w) (translateAlignBytes w)`),
reading `⟨.indirect mp_u, fLay⟩` via `annealReadImmediateLM2_2` fails with
`.error (.undefinedBehavior "read of uninitialized memory field")`, while
encoding `.aggregate 0 (List.replicate n .unit)` in Anneal produces
`some (replicateUninitBytes S)`. -/
theorem step_padded_zst_union_uninit_payload_read_ub
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx w : Nat} {signed : Bool}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hw : ValidScalarBytes w) (hwS : w ≤ S)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u)
    {tyId : Miri.MIR.TyId} :
    encodeByLayoutIdxAux 8 body.layouts uDecl.ty.layoutIdx
      (.aggregate 0 (List.replicate n .unit)) = some (replicateUninitBytes S) ∧
    annealReadImmediateLM2_2
      ⟨.indirect mp_u,
        { ty := tyId, layout := scalarLayoutData w signed }⟩
      m = .error (.undefinedBehavior "read of uninitialized memory field") m := by
  refine ⟨encodeByLayoutIdxAux_union_allUnits hwt hfields 7, ?_⟩
  cases hmem with
  | mk allocId tag baseAddr la hprov _ _ hlive hbase hptr _ _ _ _ _ _ _ _ hmask =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel0 : Miri.ABI.Size.ofBytes (mp_u.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
      have hb : mp_u.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
      rw [hb, UInt64.sub_self]; rfl
    have hsz0 : ((scalarLayoutData w signed).size == Miri.ABI.Size.ZERO) = false := by
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hfields_sc : (scalarLayoutData w signed).fields = .Primitive := rfl
    have hsz_sc : (scalarLayoutData w signed).size = translateSizeBytes w := rfl
    have hrepr : (scalarLayoutData w signed).backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes w) signed)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * w)) - 1) })) := rfl
    rcases la with ⟨kind, alloc⟩
    have hbad : alloc.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w))) := by
      rw [hmask]
      rcases hwt.size_valid with rfl | rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl | rfl <;>
        (try omega) <;>
        rfl
    have hread_err := union_readScalar_uninit hbad
    change annealReadIndirectImmediate mp_u
      { ty := tyId, layout := scalarLayoutData w signed } m = _
    unfold annealReadIndirectImmediate
    rw [hprov, hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind,
      hrel0, hread_err, throw, throwThe]
    rfl


end LeanMiriSpec.Correspondence.Witness
