/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.FloatCastLM.RealStepDirect

/-!
# Memory-backed real-step float-cast simulation (`LeanMiriSpec.FloatCastLM.RealStepIndirect`)

Third layer (Part 8b, parallel sibling of `DetModeAndBoundaries` over `RealStepDirect`) of the
IEEE-754 float-cast correspondence; see the umbrella module `LeanMiriSpec.FloatCastLM` for the
architectural overview and the submodule map.

Real-step simulation for memory-backed locals:

* promoted (`allocMap`) and immediate destinations with `updateAllocMapOnWrite` Tree Borrows
  invalidation: `step_cast_float_{copy,move,constant}_anyLocal_simulation{_mode}` and the
  `FloatStepPreservesImm` chaining lemmas
  `step_cast_float_{copy,move,constant}_anyLocal_preserves` (with
  `StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?`);
* stack-allocated `LocalRel.indirect` float sources:
  `step_cast_float_{copy,move}_indirect_float_simulation{_mode}`;
* unpromoted indirect destinations: `annealWriteMemoryPlace_floatCastScalar_zero_offset_ok`,
  `StateRelLM3_1.advance_write_unpromoted_indirect_scalar`,
  `step_cast_float_{copy,move,constant}_indirect_dst_simulation{_mode}`, and the float-destination
  specializations `step_cast_float_{copy,move,constant}_indirect_floatDst_simulation{_mode}`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Part 8b. Promoted (`allocMap`) & stack-allocated (`LocalRel.indirect`) real-step simulation

In `StateRelLM3_1`, taking the raw address of an integer local (`_p = &raw (const|mut) _i`)
promotes `_i` into `allocMap` (`topFrame.locals[_i]? = some ⟨.live (.indirect (stackAllocPlace
e.allocId)), _⟩`), violating `IsImmediateFrameLocal`. Moreover, writing a `floatToInt` result
directly into promoted `_i` updates its backing stack allocation in `lean-miri` AND invalidates
conflicting Tree Borrows tags in Anneal (`updateAllocMapOnWrite allocMap dstIdx none`).
Similarly, `forceAllocation_preserves_StateRel` can promote `f32` / `f64` locals to
`LocalRel.indirect` stack allocations. The theorems below remove the `IsImmediateFrameLocal`
restriction across all three operand forms (`copy`, `move`, `constant`). -/

/-- Unified post-operand write finisher for **any** destination local `dstIdx` that is either
immediate (`IsImmediateFrameLocal tf_mid dstIdx`, where `updateAllocMapOnWrite` is the
identity) or promoted in `allocMap` (`∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx`, where
`annealWriteMemoryPlace` overwrites `e₀.allocId`'s stack allocation and Anneal invalidates
conflicting Tree Borrows tags via `updateAllocMapOnWrite allocMap dstIdx none`). -/
theorem finish_write_anyLocal_from_mid_hooks
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hdst_loc : IsImmediateFrameLocal tf_mid dstIdx ∨ (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx))
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok (.scalar sc') s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, halloc_m, _⟩ :=
    id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  by_cases hsd_dead : slot_dm = .dead
  · subst hsd_dead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm]
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  · rcases hdst_loc with himm_dst_mid | ⟨e₀, he₀, he₀_loc⟩
    · have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
        hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_dead himm_dst_mid
      rw [updateAllocMapOnWrite_eq_of_not_mem allocMap dstIdx none hnot_dst]
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      exact finish_write_immediate_from_mid_hooks hooks hframes hbody hloc hstate_mid
        hs_frame_eq hbb hstmt hdecl_dst himm_dst_mid hrv_anneal hm_write
        (fun cachedLay hc =>
          .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
            (Or.inr ⟨.scalar sc', rfl,
              .scalar sc' msc' hrel' hsz' (fun h => absurd h hnb) (fun h => absurd h hnc)⟩)))
    · subst he₀_loc
      obtain ⟨d₀, hd₀, hd₀_prim⟩ := halloc_m.target_decl e₀ he₀
      have hdst_prim : IsPrimScalarTy dstDecl.ty := by
        rw [hdecl_dst] at hd₀; cases hd₀; exact hd₀_prim
      obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_m.local_alloc_sync tf_mid rfl e₀ he₀).1 slot_dm hslot_dm hsd_dead
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_m.base_addr_valid e₀ he₀
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      have hbool_val : dstDecl.ty.kind = .bool → sc'.sizeBytes = 1 ∧ (sc'.bits = 0 ∨ sc'.bits = 1) :=
        fun h => absurd h hnb
      have hchar_val : dstDecl.ty.kind = .char → sc'.sizeBytes = 4 ∧ isValidCharCode sc'.bits = true :=
        fun h => absurd h hnc
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
          localAlloc.allocation := hsz' ▸ hshape_la
      obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
        hshape_sc.writeScalar_readScalar hrel'
      have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel'.size_eq, ← hsz']
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc') = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel' hbool_val hchar_val
      have hget_dm := frame_getLocal_of_getElem? tf_mid e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩) m =
          ({ stack := ⟨#[tf_mid]⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue
        rw [hw_ind, stackAllocPlace, hw_m]
      have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
        have hl := hfr_m.location_eq
        rw [hb_eq, hsi_eq] at hl
        exact hl
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
        rw [← hs_mem]; exact hbor_m
      have hprot_s : s.memory.activeProtectors = .nil := by
        rw [← hs_mem]; exact hprot_m
      have hstack_s : s.memory.callStack = .nil := by
        rw [← hs_mem]; exact hstack_m
      have ha_ok : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s_mid (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s_mid.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry }) := by
        have hadv_eq :
            advanceStmt s (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry } =
            advanceStmt s_mid (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s_mid.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry } := by
          rw [hs_frame_eq]; rfl
        rw [← hadv_eq]
        unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
        cases slot_dm with
        | dead => exact absurd rfl hsd_dead
        | uninit =>
          simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_s,
            invalidateConflictingBorrows_map_toBorrowEntry]
        | init _ =>
          simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_s,
            invalidateConflictingBorrows_map_toBorrowEntry]
      rw [ha_ok]
      refine .step _ _ ?_
      have hstep_rel := hstate_mid.advance_write_deref_scalar rfl
        (fun x => x.updateOnWrite e₀.localIdx none)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        he₀ hdecl_dst hdst_prim hslot_dm hsd_dead hfind_la hkind_la halign_la
        hrel' hsz' hbool_val hchar_val halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'
      rw [hb_eq, hsi_eq] at hstep_rel
      exact hstep_rel

/-- Compositional frame-immediacy & `nextAllocId` preservation across a Miri step:
whenever the step succeeds with `(m', .ok true)`, `nextAllocId` is unchanged (float casts
never allocate stack slots) and every local that satisfied `IsImmediateFrameLocal` before
the step still satisfies `IsImmediateFrameLocal` after the step. This closes the multi-step
compositionality gap where `StepRelLM3_1` alone would forget `IsImmediateFrameLocal`. -/
def FloatStepPreservesImm (m : AnnealStepState)
    (mStep : AnnealStepState × Except Miri.Interpreter.StepError Bool) : Prop :=
  ∀ m', mStep = (m', .ok true) →
    m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
    ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k

private theorem floatCast_set_immediate
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} (hlt : dstIdx < tf.locals.size)
    (val : Miri.Interpreter.Immediate AnnealProv) (lay : Option Miri.Interpreter.LocalLayout)
    (loc' : Miri.Interpreter.FrameLocation) :
    ∀ {k}, IsImmediateFrameLocal tf k →
      IsImmediateFrameLocal
        { tf with locals := tf.locals.set dstIdx ⟨.live (.immediate val), lay⟩ hlt, location := loc' }
        k := by
  intro k hk mls hmls mp hmp
  dsimp only at hmls
  rw [Array.getElem?_set] at hmls
  by_cases hkd : dstIdx = k
  · simp only [hkd, ↓reduceIte] at hmls
    injection hmls with hm; rw [← hm] at hmp; cases hmp
  · simp only [hkd, ↓reduceIte] at hmls
    exact hk mls hmls mp hmp

theorem finish_write_anyLocal_preserves
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    (himm_mid : ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf_mid k)
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hdst_loc : IsImmediateFrameLocal tf_mid dstIdx ∨ (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx))
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    FloatStepPreservesImm m (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_m, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, _, hlt_dm, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    have hl := hfr_m.location_eq; rw [hb_eq, hsi_eq] at hl; exact hl
  by_cases hsd_dead : slot_dm = .dead
  · subst hsd_dead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · rcases hdst_loc with himm_dst_mid | ⟨e₀, he₀, he₀_loc⟩
    · have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
        cases hloc_dm with
        | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
        | base hb =>
          cases hb with
          | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
          | dead _ _ => exact absurd rfl hsd_dead
          | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
      obtain ⟨oldImm, hmd_imm⟩ := hold_imm
      have hdm_live : tf_mid.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
        rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
      have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
      have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
          ({ m with stack := ⟨#[{ tf_mid with
              locals := tf_mid.locals.set dstIdx
                { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
                hlt_dm }]⟩ }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      intro m' hm'
      injection hm' with hm'_eq _
      subst hm'_eq
      refine ⟨rfl, ?_⟩
      intro tf₀ tf' htf₀ htf' k hk
      rw [hframes] at htf₀
      injection htf₀ with h0; injection h0 with h0'; subst h0'
      injection htf' with h1; injection h1 with h1'; subst h1'
      exact floatCast_set_immediate hlt_dm (.scalar (.fromScalarInt msc'))
        (tf_mid.locals[dstIdx]'hlt_dm).layout _ (himm_mid k hk)
    · subst he₀_loc
      obtain ⟨d₀, hd₀, hd₀_prim⟩ := halloc_m.target_decl e₀ he₀
      have hdst_prim : IsPrimScalarTy dstDecl.ty := by
        rw [hdecl_dst] at hd₀; cases hd₀; exact hd₀_prim
      obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_m.local_alloc_sync tf_mid rfl e₀ he₀).1 slot_dm hslot_dm hsd_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_m.base_addr_valid e₀ he₀
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
          localAlloc.allocation := hsz' ▸ hshape_la
      obtain ⟨alloc', hw_alloc, _, _, _, _⟩ := hshape_sc.writeScalar_readScalar hrel'
      have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel'.size_eq, ← hsz']
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc') = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel'
          (fun h => absurd h hnb) (fun h => absurd h hnc)
      have hget_dm := frame_getLocal_of_getElem? tf_mid e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks () (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩) m =
          ({ stack := ⟨#[tf_mid]⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue
        rw [hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      intro m' hm'
      injection hm' with hm'_eq _
      subst hm'_eq
      refine ⟨rfl, ?_⟩
      intro tf₀ tf' htf₀ htf' k hk mls hmls mp hmp
      rw [hframes] at htf₀
      injection htf₀ with h0; injection h0 with h0'; subst h0'
      injection htf' with h1; injection h1 with h1'; subst h1'
      exact himm_mid k hk mls hmls mp hmp

/-- **Copy-operand real-step simulation across immediate AND promoted (`allocMap`) locals**
(`_d = copy _s as T` in either NaN mode): both `_s` and `_d` may be either immediate
(`IsImmediateFrameLocal`) or address-taken / promoted in `allocMap` (`∃ e ∈ allocMap,
e.localIdx = _`). Dead or uninitialized sources (including uninitialized memory-backed
stack allocations) report UB in both machines; initialized sources write `ScalarRel`-related
cast results and update `allocMap` via `updateAllocMapOnWrite allocMap dstIdx none` (which
is the identity when `_d` is immediate and invalidates conflicting Tree Borrows tags when
`_d` is promoted). -/
theorem step_cast_float_copy_anyLocal_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  by_cases hss_dead : slot_s = .dead
  · subst hss_dead
    have hms : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · rcases hsrc_loc tf hframes with himm_s | ⟨es, hes, hes_loc⟩
    · have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
      rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
        ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
      · exact absurd hss hss_dead
      · subst hss
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have ha_ub : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
          unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
        have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
          (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast_un
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          rw [hm_stmt, htr_dst, htr_src]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
          rfl
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      · subst hss
        obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast hsz'
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
            ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
            body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
          rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
          have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
              s.memory.globals body.layouts s.memory.callerLocals body.localDecls
              s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
            unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
          rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
        exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
          hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write
    · -- `_s` is promoted in `allocMap` (`es.localIdx = srcIdx`).
      subst hes_loc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      obtain ⟨⟨lay_s, hlay_s⟩, hsc_only, hsh_s⟩ :=
        (halloc_a.local_alloc_sync tfa rfl es hes).1 slot_s hslot_s hss_dead
      obtain ⟨localAlloc_s, hfind_s, _, _, hshape_s⟩ := hsh_s srcDecl hdecl_src
      obtain ⟨hid_lt_s, _, hbase_s⟩ := halloc_a.base_addr_valid es hes
      have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
      have hmls_s' : tfa.locals[es.localIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s_eq]; exact hmls_s_ind
      have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
      obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_ind hbase_s hfind_s
        (halloc_a.live_key_unique es hes) (hsig.src_scalar.size_ne_zero body.layouts)
      have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
        hid_lt_s hbase_s hfind_s hshape_s.byteSize_eq
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
      cases hss : slot_s with
      | dead => exact absurd hss hss_dead
      | uninit =>
        obtain ⟨_, hread_err⟩ := hshape_s.uninit_readScalar_err (hun_s hss) false
        have hri_err : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .error (.undefinedBehavior "read of uninitialized memory")
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_err]
        have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
        rw [← hdstT] at hcast_err
        have ha_ub : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
          unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized memory")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      | init vs =>
        obtain ⟨sc, rfl⟩ := hsc_only vs hss
        obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
        have hri_ok : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_ok]
          dsimp only []
          rw [hsig.src_scalar.validateScalar_true msc]
          rfl
        have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity)
          (.fromScalarInt msc) hri_ok
        obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
        have hcast_ind :
            Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
              ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
              (translateCastKind kind) (encodeTyId castTy)
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } =
            annealWriteImmediate (.scalar (.fromScalarInt msc'))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
        rw [← hdstT] at hsz'
        have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy) s.memory
            body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
          rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
          have hop : evalOperand s.frame.locals (.copy ⟨es.localIdx, .nil⟩) s.memory.borrows
              s.memory.globals body.layouts s.memory.callerLocals body.localDecls
              s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
            unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss]
          rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
        exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
          hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write

/-- **Copy-operand real-step simulation across immediate AND promoted (`allocMap`) locals**
under the NaN refinement witness (`floatNondeterministic := true`,
`chooseNaN := annealChooseQuietedNaN`). -/
theorem step_cast_float_copy_anyLocal_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hsrc_loc hdst_loc hptr8

/-- **Move-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
(`_d = move _s as T` in either NaN mode): deinitializes immediate `_s` in both machines and
writes into either an immediate `_d` or a promoted `allocMap` local `_d`. -/
theorem step_cast_float_move_anyLocal_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_s := himm_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp) himm_sb hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hslot_s)
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    have hdst_mid : IsImmediateFrameLocal (deinitFrameLocal tfb srcIdx hlt_sb) dstIdx ∨
        (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
      rcases hdst_loc tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hdst_mid hrel' hsz' hrv_a hm_write

/-- **Move-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
under the NaN refinement witness. -/
theorem step_cast_float_move_anyLocal_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hdst_loc hptr8

/-- **Constant-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
(`_d = const c as T` in either NaN mode). -/
theorem step_cast_float_constant_anyLocal_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hlaysz hagree
    (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hrv_a : evalRvalue s.frame.locals (.cast kind (.constant c) castTy) s.memory
      body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  have hdst_tfa : IsImmediateFrameLocal tfa dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl (himm_d.cache_layout hlt_d _)
    · exact Or.inr hed
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfa hrel' hsz' hrv_a hm_write

/-- **Constant-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
under the NaN refinement witness. -/
theorem step_cast_float_constant_anyLocal_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hdst_loc hptr8

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `constant` float casts**:
any successful `_d = const c as T` step preserves `IsImmediateFrameLocal` for every local
and leaves `nextAllocId` unchanged. -/
theorem step_cast_float_constant_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only; rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hlaysz hagree
    (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  have hdst_tfa : IsImmediateFrameLocal tfa dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl (himm_d.cache_layout hlt_d _)
    · exact Or.inr hed
  exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_a rfl
    (fun _ hk => hk.cache_layout hlt_d _) hbb hstmt hdecl_dst hdst_scalar hdst_tfa
    hrel' hsz' hm_write

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `copy` float casts**:
any successful `_d = copy _s as T` step (from immediate or promoted `_s` into immediate or
promoted `_d`) preserves `IsImmediateFrameLocal` for every local and leaves `nextAllocId`
unchanged. -/
theorem step_cast_float_copy_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  by_cases hss_dead : slot_s = .dead
  · subst hss_dead
    have hms : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · rcases hsrc_loc tf hframes with himm_s | ⟨es, hes, hes_loc⟩
    · have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
      rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
        ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
      · exact absurd hss hss_dead
      · subst hss
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
          (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast_un
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact fun _ h => nomatch h
      · subst hss
        obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast hsz'
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
            ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
        exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_b rfl
          (fun _ hk => (hk.cache_layout hlt_d _).cache_layout hlt_sa _)
          hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hm_write
    · subst hes_loc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      obtain ⟨⟨lay_s, hlay_s⟩, hsc_only, hsh_s⟩ :=
        (halloc_a.local_alloc_sync tfa rfl es hes).1 slot_s hslot_s hss_dead
      obtain ⟨localAlloc_s, hfind_s, _, _, hshape_s⟩ := hsh_s srcDecl hdecl_src
      obtain ⟨hid_lt_s, _, hbase_s⟩ := halloc_a.base_addr_valid es hes
      have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
      have hmls_s' : tfa.locals[es.localIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s_eq]; exact hmls_s_ind
      have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
      obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_ind hbase_s hfind_s
        (halloc_a.live_key_unique es hes) (hsig.src_scalar.size_ne_zero body.layouts)
      have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
        hid_lt_s hbase_s hfind_s hshape_s.byteSize_eq
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
      cases hss : slot_s with
      | dead => exact absurd hss hss_dead
      | uninit =>
        obtain ⟨_, hread_err⟩ := hshape_s.uninit_readScalar_err (hun_s hss) false
        have hri_err : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .error (.undefinedBehavior "read of uninitialized memory")
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_err]
        have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
        rw [← hdstT] at hcast_err
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized memory")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact fun _ h => nomatch h
      | init vs =>
        obtain ⟨sc, rfl⟩ := hsc_only vs hss
        obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
        have hri_ok : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_ok]
          dsimp only []
          rw [hsig.src_scalar.validateScalar_true msc]; rfl
        have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity)
          (.fromScalarInt msc) hri_ok
        obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
        have hcast_ind :
            Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
              ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
              (translateCastKind kind) (encodeTyId castTy)
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } =
            annealWriteImmediate (.scalar (.fromScalarInt msc'))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
        rw [← hdstT] at hsz'
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
        exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_b rfl
          (fun _ hk => (hk.cache_layout hlt_d _).cache_layout hlt_sa _)
          hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hm_write

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `move` float casts**:
any successful `_d = move _s as T` step (deinitializing immediate `_s` and writing into
immediate or promoted `_d`) preserves `IsImmediateFrameLocal` for every local and leaves
`nextAllocId` unchanged. -/
theorem step_cast_float_move_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have himm_s := himm_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · subst hss
    obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp) himm_sb hlt_sb
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    have hdst_mid : IsImmediateFrameLocal (deinitFrameLocal tfb srcIdx hlt_sb) dstIdx ∨
        (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
      rcases hdst_loc tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
    exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_mid rfl
      (fun _ hk => ((hk.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      hbb hstmt hdecl_dst hdst_scalar hdst_mid hrel' hsz' hm_write

/-- **Copy-operand real-step simulation for stack-allocated (`LocalRel.indirect`) `f32`/`f64`
and integer locals** (such as locals promoted via `forceAllocation_preserves_StateRel`, even
when absent from `allocMap`): both `.uninit` (`"read of uninitialized memory"` UB) and
initialized scalar values step in `StepRelLM3_1` lockstep into any immediate or promoted `_d`. -/
theorem step_cast_float_copy_indirect_float_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have hlay_tfa : ∃ lay_s, tfa.locals[srcIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds
      simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_0 ⊢
      injection hlay_0 with hm0
      rw [hm0]
      exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]
      exact ⟨lay_0, hlay_0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  have hmls_dummy : mls_s = ⟨.live (.indirect (stackAllocPlace dummyEntry.allocId)), lay_s⟩ :=
    hmls_s_ind
  obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry)
    hmls_dummy hbase hfind huniq (hsig.src_scalar.size_ne_zero body.layouts)
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
    hid_lt hbase hfind hshape.byteSize_eq
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hss : slot_s with
  | dead =>
    have hnd : slot_s ≠ .dead := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => cases hmls_s_ind
      | base hb =>
        cases hb with
        | dead _ _ => cases hmls_s_ind
        | immediate _ _ _ _ _ => cases hmls_s_ind
        | indirect _ _ _ _ hne _ => exact hne
    exact absurd hss hnd
  | uninit =>
    obtain ⟨_, hread_err⟩ := hshape.uninit_readScalar_err (hun_s hss) false
    have hri_err : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .error (.undefinedBehavior "read of uninitialized memory")
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_err]
    have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
    rw [← hdstT] at hcast_err
    have ha_ub : evalStmt s
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized memory")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  | init vs =>
    obtain ⟨sc, rfl⟩ := hsc_src vs (hss ▸ hslot_s)
    obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
    have hri_ok : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_ok]
      dsimp only []
      rw [hsig.src_scalar.validateScalar_true msc]
      rfl
    have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
      (.fromScalarInt msc) hri_ok
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
    have hcast_ind :
        Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
    rw [← hdstT] at hsz'
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_float_simulation_mode`. -/
theorem step_cast_float_copy_indirect_float_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_float_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hid_lt hbase hfind huniq hshape hind_src hsc_src hdst_loc hptr8

/-- **Float-typed locals are never promoted into `allocMap`**: every `e ∈ allocMap` targets an
`IsPrimScalarTy` (`bool`, `char`, integer) local (`AllocMapRel.target_decl`), so any `f32`/`f64`
local (`ieeeFormatOfTy? decl.ty = some f`) is disjoint from `allocMap`. -/
theorem StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {idx : Local} {decl : LocalDecl} {f : IeeeFormat}
    (hdecl : get? body.localDecls idx = some decl)
    (hf : ieeeFormatOfTy? decl.ty = some f) :
    ∀ e ∈ allocMap, e.localIdx ≠ idx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  intro e he heq
  subst heq
  obtain ⟨d₀, hd₀, hprim⟩ := halloc.target_decl e he
  rw [hdecl] at hd₀; injection hd₀ with hd_eq; subst hd_eq
  rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;>
    rcases hprim with hb | hb | ⟨_, hb⟩ | ⟨_, hb⟩ <;>
    (rw [hk] at hb; cases hb)

/-- **Deinitializing any unpromoted live local (`∀ e ∈ allocMap, e.localIdx ≠ srcIdx`)** —
whether `IsImmediateFrameLocal` or stack-allocated `LocalRel.indirect` — preserves
`StateRelLM3_1` when `annealEvalOperand (.Move ...)` replaces `tf.locals[srcIdx]` with
`.live (.immediate .uninit)`. (By contrast, moving out of a promoted `e ∈ allocMap` local would
break `AllocMapRel.local_alloc_sync`, which requires `tf.locals[e.localIdx]` to remain
`.indirect (stackAllocPlace e.allocId)`.) -/
theorem StateRelLM3_1.deinit_unpromoted_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_1 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁; injection h₁ with htf; subst htf
  obtain ⟨_, mls_s, _, _, _, _, hmls_s_eq, hloc_s⟩ := hfr.lookup_local hdecl_src
  have hnew_s : LocalRelLM3_1 m.machine allocMap srcDecl body.layouts .uninit
      { tf.locals[srcIdx]'hlt_s with value := .live (.immediate .uninit) } :=
    .base (.immediate .uninit .uninit (tf.locals[srcIdx]'hlt_s).layout
      (by rw [hmls_s_eq]; exact hloc_s.cachedLayout_eq)
      (Or.inl ⟨rfl, rfl⟩))
  have hfr' := hfr.update_local hdecl_src .uninit (.live (.immediate .uninit)) hnew_s
  refine .mk (deinitFrameLocal tf srcIdx hlt_s) rfl hretCont hretPlace hfr'
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h₁; injection h₁ with h₂; subst h₂
    have hne_s : srcIdx ≠ e.localIdx := Ne.symm (hnot_src e he)
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    have hget_ne :
        get? (s.frame.locals.set srcIdx .uninit) e.localIdx =
          get? s.frame.locals e.localIdx := by
      rw [get?_eq_getElem?, List.getElem?_set_ne hne_s, ← get?_eq_getElem?]
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · dsimp only [] at hslot'
      rw [hget_ne] at hslot'
      obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
      refine ⟨⟨lay, ?_⟩, hsc, hshape⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne_s]
      exact hlay
    · dsimp only [] at hdead'
      rw [hget_ne] at hdead'
      exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = srcIdx
    · subst hk
      right
      refine ⟨.uninit, (tf.locals[k]'hlt_s).layout, ?_⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_self]
    · left
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- **Move-operand real-step simulation from an unpromoted stack-allocated `LocalRel.indirect`
local** (`_d = move _s as T` in either NaN mode, e.g. force-allocated `f32` / `f64` or unpromoted
integer locals where `∀ e ∈ allocMap, e.localIdx ≠ srcIdx`):
* `annealEvalOperand (.Move ...)` replaces `tf.locals[srcIdx]` with `.live (.immediate .uninit)`
  while returning `.indirect (stackAllocPlace allocId)`, which `Cast.cast` then reads from
  `m.machine.memory` (`StepRelLM3_1.ub` if `_s` was `.uninit`, normal lockstep if initialized);
* handles **both** distinct destinations (`dstIdx ≠ srcIdx`, immediate or promoted in `allocMap`)
  and self-moves (`dstIdx = srcIdx`, where `_s` transitions cleanly from `.indirect` to
  `.immediate` before `annealWriteImmediate` writes the cast result!). -/
theorem step_cast_float_move_indirect_float_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : dstIdx ≠ srcIdx → ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  let tfc := deinitFrameLocal tfb srcIdx hlt_sb
  have hdst_tfc : IsImmediateFrameLocal tfc dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    by_cases hds : dstIdx = srcIdx
    · subst hds
      left
      intro mls hmls mp hmp
      dsimp only [tfc, deinitFrameLocal] at hmls
      rw [Array.getElem?_set_self] at hmls
      injection hmls with hm
      rw [← hm] at hmp
      cases hmp
    · rcases hdst_loc hds tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
  have hlay_tfa : ∃ lay_s, tfa.locals[srcIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds
      simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_0 ⊢
      injection hlay_0 with hm0
      rw [hm0]
      exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]
      exact ⟨lay_0, hlay_0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  have hmls_dummy : mls_s = ⟨.live (.indirect (stackAllocPlace dummyEntry.allocId)), lay_s⟩ :=
    hmls_s_ind
  obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry)
    hmls_dummy hbase hfind huniq (hsig.src_scalar.size_ne_zero body.layouts)
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
    hid_lt hbase hfind hshape.byteSize_eq
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfc]⟩ })
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hss : slot_s with
  | dead =>
    have hnd : slot_s ≠ .dead := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => cases hmls_s_ind
      | base hb =>
        cases hb with
        | dead _ _ => cases hmls_s_ind
        | immediate _ _ _ _ _ => cases hmls_s_ind
        | indirect _ _ _ _ hne _ => exact hne
    exact absurd hss hnd
  | uninit =>
    obtain ⟨_, hread_err⟩ := hshape.uninit_readScalar_err (hun_s hss) false
    have hri_err : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
        .error (.undefinedBehavior "read of uninitialized memory")
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_err]
    have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
    rw [← hdstT] at hcast_err
    have ha_ub : evalStmt s
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfc]⟩ },
          .error (.undefinedBehavior "read of uninitialized memory")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  | init vs =>
    obtain ⟨sc, rfl⟩ := hsc_src vs (hss ▸ hslot_s)
    obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
    have hri_ok : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_ok]
      dsimp only []
      rw [hsig.src_scalar.validateScalar_true msc]
      rfl
    have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
      (.fromScalarInt msc) hri_ok
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
    have hcast_ind :
        Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
    rw [← hdstT] at hsz'
    have hstate_mid := hstate_b.deinit_unpromoted_local rfl hdecl_src hnot_src hlt_sb
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, hss, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfc hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_move_indirect_float_simulation_mode`. -/
theorem step_cast_float_move_indirect_float_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : dstIdx ≠ srcIdx → ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_float_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hid_lt hbase hfind huniq hshape hind_src hnot_src hsc_src
    hdst_loc hptr8

private theorem float_list_filter_ne_find? {β : Type}
    (l : List (Miri.Memory.AllocId × β)) {id₀ id₁ : Miri.Memory.AllocId}
    (hne : id₀ ≠ id₁) :
    (l.filter (fun x => x.1 != id₀)).find? (fun x => x.1 == id₁) =
      l.find? (fun x => x.1 == id₁) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk : k = id₁
    · subst hk
      have hne' : (k != id₀) = true := bne_iff_ne.mpr (Ne.symm hne)
      simp [List.filter, List.find?, hne']
    · have hk' : (k == id₁) = false := beq_false_of_ne hk
      by_cases hk0 : (k != id₀) = true
      · simp [List.filter, List.find?, hk0, hk', ih]
      · simp [List.filter, List.find?, hk0, hk', ih]

private theorem float_live_find_filter_push_ne {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) (newLa : β) :
    ((live.filter (fun x => x.1 != id₀)).push (id₀, newLa)).find? (fun x => x.1 == id) =
      live.find? (fun x => x.1 == id) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    float_list_filter_ne_find? live.toList hne, Array.find?_toList]
  cases live.find? (fun x => x.1 == id) with
  | some _ => rfl
  | none => simp [beq_false_of_ne hne]

theorem IsFloatCastScalarTy.align_pow2_le_29 {ty : Ty} (hty : IsFloatCastScalarTy ty)
    (ly : LayoutTable) :
    (translateTy ty ly).layout.align.abi.pow2 ≤ 29 := by
  rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> decide
  · rw [translateTy_of_floatIntTargetOfTy? ht ly]
    cases t <;> rename_i w <;> cases w <;> decide

/-- Zero-offset memory write into a stack allocation for **any** `IsFloatCastScalarTy`
(`f32`, `f64`, and all 12 integer widths, extending `SimLM3_1.annealWriteMemoryPlace_zero_offset_scalar_ok`
beyond `IsPrimScalarTy` to floats). -/
theorem annealWriteMemoryPlace_floatCastScalar_zero_offset_ok
    {ty : Ty} {ly : LayoutTable} (hty : IsFloatCastScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hmut : localAlloc.allocation.mutability = .Mut)
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size)
    {msc : Miri.Memory.ScalarInt}
    (hmsc_sz : msc.size = (translateTy ty ly).layout.size)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size)
      (.fromScalarInt msc) localAlloc.allocation = .ok () alloc') :
    annealWriteMemoryPlace (.scalar (.fromScalarInt msc))
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      .ok () { st with machine := { st.machine with
        memory := { st.machine.memory with
          live := (st.machine.memory.live.filter (fun x => x.1 != allocId)).push
            (allocId, ⟨localAlloc.kind, alloc'⟩) } } } := by
  have hmeta :
      Miri.Memory.sizeAsI64 (translateTy ty ly).layout.size =
        .ok ((translateTy ty ly).layout.size.bytes.toNat : Int) ∧
      0 < (translateTy ty ly).layout.size.bytes.toNat ∧
      ((translateTy ty ly).layout.size.bytes.toNat : Int) < 2 ^ 63 := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]
      cases f <;> exact ⟨rfl, by decide, by decide⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> exact ⟨rfl, by decide, by decide⟩
  obtain ⟨hsz, hgt0, hlt63⟩ := hmeta
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind hgt0 hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  have hset := Miri.Memory.MemoryState.setLiveAllocation_of_find
    st.machine.memory allocId localAlloc alloc' hfind
  have hsc_sz : ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size !=
      (translateTy ty ly).layout.size) = false := by
    rw [Miri.Memory.Scalar.fromScalarInt_size, hmsc_sz, bne_self_eq_false]
  have hmut_bne : (localAlloc.allocation.mutability != Miri.Memory.Mutability.Mut) = false := by
    rw [hmut]; rfl
  exact annealWriteMemoryPlace_of_check_ok_scalar _ _ _ st allocId localAlloc _ _ alloc' _
    hsz hchk hmut_bne rfl hfind hsc_sz (hty.validateScalar_true msc) hw hset

/-- **Overwriting an unpromoted `LocalRel.indirect` stack local (`∀ e ∈ allocMap, e.localIdx ≠ dstIdx`)
preserves `StateRelLM3_1`**: covers force-allocated `f32`/`f64` destinations (where
`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?` discharges `hnot_dst` automatically) as well
as unpromoted indirect integer destinations. -/
theorem StateRelLM3_1.advance_write_unpromoted_indirect_scalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {slot_d : LocalSlot} (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    {allocId : Miri.Memory.AllocId}
    {lay_d : Option Miri.Interpreter.LocalLayout}
    (hlay_d : tf.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) =
      some (allocId, localAlloc))
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel_sc : ScalarRel sc msc)
    (hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hshape_alloc' : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc')
    (hinit_alloc' : alloc'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hread_alloc' : alloc'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (.fromScalarInt msc)) :
    StateRelLM3_1 body
      (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory)
      { stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩
        machine := { m.machine with
          memory := { m.machine.memory with
            live := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
              (allocId, ⟨localAlloc.kind, alloc'⟩) } } }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  let newLive := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
    (allocId, ⟨localAlloc.kind, alloc'⟩)
  let newMem : AnnealMemory := { m.machine.memory with live := newLive }
  let mach' : AnnealMachine := { m.machine with memory := newMem }
  have hset_mem : m.machine.memory.setLiveAllocation allocId alloc' = .ok newMem :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find m.machine.memory allocId localAlloc
      alloc' hfind_la
  have hpow_d := hdst_scalar.align_pow2_le_29 body.layouts
  obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
  have hlt_af_d : dstIdx < s.frame.locals.length := by
    cases h : s.frame.locals[dstIdx]? with
    | none => rw [get?_eq_getElem?, h] at hslot_d; cases hslot_d
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hloc_d0 := hfr.locals_rel dstIdx dstDecl slot_d
    ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ hdecl_dst hslot_d hlay_d
  have hnew_mp : MemPlaceRel mach' dstDecl.ty body.layouts (some (.scalar sc))
      (stackAllocPlace allocId) := by
    refine .mk allocId Miri.Memory.BorTag.one (annealStackBaseAddr allocId)
      Miri.ABI.Size.ZERO ⟨localAlloc.kind, alloc'⟩
      rfl rfl rfl ?_ hbase ?_ ?_ hshape_alloc'.mutability_eq ?_ ?_ ?_ ?_ ?_
      (fun _ _ _ _ hs => nomatch hs)
    · exact Array.mem_toList_iff.mpr (Array.mem_push_self ..)
    · simp only [Miri.ABI.Size.ZERO, UInt64.toNat_zero, Nat.add_zero]
      exact (annealStackBaseAddr allocId).toBitVec.isLt
    · simp [stackAllocPlace, Miri.ABI.Size.ZERO]
    · exact annealStackBaseAddr_isAligned allocId _ hpow_d
    · simp [Miri.ABI.Size.ZERO, hshape_alloc'.byteSize_eq, hsz_dst]
    · intro h; cases h
    · intros; rw [hsz_dst]; exact hinit_alloc'
    · intro sc' hs'
      injection hs' with hv
      injection hv with hsc_eq
      subst hsc_eq
      exact ⟨hsz_dst, fun h => absurd h hnb, fun h => absurd h hnc,
        msc, hrel_sc, hsz_dst ▸ hread_alloc'⟩
  have hnew_d : LocalRelLM3_1 mach' allocMap dstDecl body.layouts (.init (.scalar sc))
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ :=
    .base (.indirect (.init (.scalar sc)) (stackAllocPlace allocId) lay_d
      hloc_d0.cachedLayout_eq (by simp) hnew_mp)
  have hfr' : FrameRelLM3_1 body mach' allocMap
      { s.frame with locals := s.frame.locals.set dstIdx (.init (.scalar sc)) } tf := by
    refine ⟨hfr.body_eq, hfr.location_eq, by rw [List.length_set, hfr.af_locals_len],
      hfr.mf_locals_size, ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    by_cases h_eq : dstIdx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot_i
      have hdecl_eq : decl_i = dstDecl := by
        rw [hdecl_dst] at hdecl_i; exact Option.some.inj hdecl_i.symm
      have hmls_eq : mls_i = ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ := by
        rw [hlay_d] at hmls_i; exact Option.some.inj hmls_i.symm
      subst hdecl_eq hslot_i hmls_eq
      exact hnew_d
    · simp only [h_eq, ↓reduceIte] at hslot_i
      rw [← get?_eq_getElem?] at hslot_i
      have hloc_i := hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
      apply hloc_i.of_setLiveAllocation_ne hfind_la hset_mem
      intro mp hv
      have hmls_ind : tf.locals[i]? = some ⟨.live (.indirect mp), mls_i.layout⟩ := by
        rcases mls_i with ⟨v0, l0⟩; dsimp only at hv; subst hv; exact hmls_i
      have hd := hdisj dstIdx i (stackAllocPlace allocId) mp lay_d mls_i.layout h_eq
        hlay_d hmls_ind
      exact fun heq => hd (by simpa [stackAllocPlace, Option.bind,
        Miri.Memory.Provenance.getAllocId] using heq.symm)
  have halloc_ne : ∀ x ∈ allocMap, allocId ≠ x.allocId := by
    intro x hx ha_eq
    have hx_ne : dstIdx ≠ x.localIdx := Ne.symm (hnot_dst x hx)
    obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
    obtain ⟨_, _, _, _, hslot_x, _, _, _⟩ := hfr.lookup_local
      (Classical.choose_spec (halloc.target_decl x hx)).1
    by_cases hxd : get? s.frame.locals x.localIdx = some .dead
    · rw [hslot_x] at hxd; injection hxd with hxd'
      have hnone := hdead_x (hslot_x.trans (congrArg some hxd'))
      rw [← ha_eq, hfind_la] at hnone; cases hnone
    · have hsx_ne : _ ≠ LocalSlot.dead := fun h => hxd (hslot_x.trans (congrArg some h))
      obtain ⟨⟨lay_x, hlay_x⟩, _, _⟩ := hlive_x _ hslot_x hsx_ne
      have hd := hdisj dstIdx x.localIdx (stackAllocPlace allocId) (stackAllocPlace x.allocId)
        lay_d lay_x hx_ne hlay_d hlay_x
      exact hd (by simp [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ha_eq])
  refine .mk _ rfl hretCont hretPlace hfr'.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, ?_, ?_⟩
  · intro x hx la₁ la₂ hla₁ hla₂
    have ha_ne : x.allocId ≠ allocId := (halloc_ne x hx).symm
    dsimp only [] at hla₁ hla₂
    simp only [Array.toList_push, List.mem_append, List.mem_singleton,
      Array.toList_filter, List.mem_filter] at hla₁ hla₂
    rcases hla₁ with ⟨hl₁, _⟩ | h1
    · rcases hla₂ with ⟨hl₂, _⟩ | h2
      · exact halloc.live_key_unique x hx la₁ la₂ hl₁ hl₂
      · exact absurd (Prod.mk.inj h2).1 ha_ne
    · exact absurd (Prod.mk.inj h1).1 ha_ne
  · intro tf' htf' x hx
    injection htf' with h₁; injection h₁ with h₂; subst h₂
    have hx_ne : x.localIdx ≠ dstIdx := hnot_dst x hx
    have ha_ne : allocId ≠ x.allocId := halloc_ne x hx
    obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
    have hget_ne :
        get? (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory).frame.locals
          x.localIdx = get? s.frame.locals x.localIdx := by
      dsimp only [advanceStmt]
      rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hx_ne), ← get?_eq_getElem?]
    have hfind_ne := float_live_find_filter_push_ne m.machine.memory.live ha_ne
      (⟨localAlloc.kind, alloc'⟩ : Miri.Memory.LocalAllocation AnnealProv
        (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · rw [hget_ne] at hslot'
      obtain ⟨⟨lay_x, hlay_x⟩, hsc_x, hsh_x⟩ := hlive_x slot' hslot' hne_d
      refine ⟨⟨lay_x, hlay_x⟩, hsc_x, fun decl_x hdecl_x => ?_⟩
      obtain ⟨la_x, hf_x, hk_x, hal_x, hs_x⟩ := hsh_x decl_x hdecl_x
      exact ⟨la_x, hfind_ne.trans hf_x, hk_x, hal_x, hs_x⟩
    · rw [hget_ne] at hdead'
      exact hfind_ne.trans (hdead_x hdead')

/-- Post-operand write finisher for any unpromoted stack-allocated `LocalRel.indirect`
destination `dstIdx` (`∀ e ∈ allocMap, e.localIdx ≠ dstIdx`). -/
theorem finish_write_unpromoted_indirect_from_mid_hooks
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {lay_d : Option Miri.Interpreter.LocalLayout}
    (hlay_d : tf_mid.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩)
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok (.scalar sc') s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    StepRelLM3_1 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, _, hstack_m, hprot_m, _, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, _, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hsd_ne_dead : slot_dm ≠ .dead := by
    intro hdead; subst hdead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    rw [hlay_d] at hmls_dm; injection hmls_dm with hm_eq; subst hm_eq
    cases hmd_dead
  have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
      localAlloc.allocation := hsz' ▸ hshape_la
  obtain ⟨alloc', hw_alloc, _, hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
    hshape_sc.writeScalar_readScalar hrel'
  have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
    rw [hrel'.size_eq, ← hsz']
  have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateTy dstDecl.ty body.layouts).layout.size)
      (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
    rw [← hmsc_sz]; exact hw_alloc
  have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hlay_d
  have hw_ind := annealWriteImmediate_indirect
    (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
  have hw_m := annealWriteMemoryPlace_floatCastScalar_zero_offset_ok hdst_scalar hid_lt hbase
    hfind_la hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hw_alloc_lay
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
  have hm_ok : Miri.Interpreter.Step.evalStatement
      hooks ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      ({ stack := ⟨#[tf_mid]⟩
         machine := { m.machine with
           memory := { m.machine.memory with
             live := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
               (allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
    rw [hm_write]; unfold Miri.Interpreter.runRvalue
    rw [hw_ind, stackAllocPlace, hw_m]
  have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    have hl := hfr_m.location_eq; rw [hb_eq, hsi_eq] at hl; exact hl
  rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
  have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
    rw [← hs_mem]; exact hbor_m
  have hprot_s : s.memory.activeProtectors = .nil := by
    rw [← hs_mem]; exact hprot_m
  have hstack_s : s.memory.callStack = .nil := by
    rw [← hs_mem]; exact hstack_m
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
  have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init (.scalar sc')))
        s_mid.memory) := by
    have hadv_eq :
        advanceStmt s (s_mid.frame.locals.set dstIdx (.init (.scalar sc'))) s.memory =
        advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init (.scalar sc'))) s_mid.memory := by
      rw [hs_frame_eq]; rfl
    rw [← hadv_eq]
    unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
    cases slot_dm with
    | dead => exact absurd rfl hsd_ne_dead
    | uninit =>
      simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
      congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
      cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
      congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
      cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
  rw [ha_ok]
  refine .step _ _ ?_
  have hstep_rel := hstate_mid.advance_write_unpromoted_indirect_scalar rfl hdecl_dst hdst_scalar
    hnot_dst hslot_dm hlay_d hbase hfind_la hrel' hsz' hshape_alloc' hinit_alloc' hread_alloc'
  rw [hb_eq, hsi_eq] at hstep_rel
  exact hstep_rel

/-- **Constant-operand real-step simulation into a stack-allocated (`LocalRel.indirect`)
unpromoted destination `_d`** (in particular force-allocated `f32`/`f64` destinations, where
`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?` discharges `hnot_dst` automatically). -/
theorem step_cast_float_constant_indirect_dst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hlay_tfa : tfa.locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)),
        some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
    injection hlay_0 with hm0
    rw [hm0]
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hlaysz hagree
    (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hrv_a : evalRvalue s.frame.locals (.cast kind (.constant c) castTy) s.memory
      body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_tfa hid_lt hbase hfind_la hshape_la
    hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_constant_indirect_dst_simulation_mode`. -/
theorem step_cast_float_constant_indirect_dst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hnot_dst hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **Copy-operand real-step simulation into a stack-allocated (`LocalRel.indirect`) unpromoted
destination `_d`** from an immediate source `_s` (`_d = copy _s as castTy`). -/
theorem step_cast_float_copy_indirect_dst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_tfb : ∃ lay_d, tfb.locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ := by
    have hlay_tfa : tfa.locals[dstIdx]? =
        some ⟨.live (.indirect (stackAllocPlace allocId)),
          some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_d]
      rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
      injection hlay_0 with hm0; rw [hm0]
    dsimp [tfb, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hsd : srcIdx = dstIdx
    · subst hsd
      simp only [↓reduceIte]
      have hget : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace allocId)),
            some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt_sa] at hlay_tfa
        exact Option.some.inj hlay_tfa
      rw [hget]
      exact ⟨_, rfl⟩
    · simp only [hsd, ↓reduceIte]; exact ⟨_, hlay_tfa⟩
  obtain ⟨lay_db, hlay_db⟩ := hlay_tfb
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_db hid_lt hbase hfind_la hshape_la
      hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_dst_simulation_mode`. -/
theorem step_cast_float_copy_indirect_dst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hnot_dst hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **Move-operand real-step simulation into a stack-allocated (`LocalRel.indirect`) unpromoted
destination `_d`** from an immediate source `_s` (`dstIdx ≠ srcIdx`; self-move `dstIdx = srcIdx`
is already covered by `step_cast_float_move_indirect_float_simulation`, where `annealEvalOperand`
transitions `_d` to `.immediate`). -/
theorem step_cast_float_move_indirect_dst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_dc : (deinitFrameLocal tfb srcIdx hlt_sb).locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)),
        some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp [deinitFrameLocal]
    rw [Array.getElem?_set_ne _ hne_ds.symm]
    dsimp [tfb, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hne_ds.symm]
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
    injection hlay_0 with hm0; rw [hm0]
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s_tfa).cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp) himm_sb hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hslot_s)
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_dc hid_lt hbase hfind_la
      hshape_la hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_move_indirect_dst_simulation_mode`. -/
theorem step_cast_float_move_indirect_dst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hne_ds hnot_dst hid_lt hbase hfind_la hshape_la
    hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = const c as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**: because `AllocMapRel.target_decl` restricts
`allocMap` to `IsPrimScalarTy` locals, `f32`/`f64` destinations (`floatToFloat` and `intToFloat`)
are automatically disjoint from `allocMap` (`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?`),
eliminating the `hnot_dst` premise completely. -/
theorem step_cast_float_constant_indirect_floatDst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_constant_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz hagree
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_constant_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_constant_indirect_floatDst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hdst_fmt hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = copy _s as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**. -/
theorem step_cast_float_copy_indirect_floatDst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_copy_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hagree himm_src
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_copy_indirect_floatDst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hdst_fmt
    (fun h => absurd h (by decide)) himm_src hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = move _s as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**. -/
theorem step_cast_float_move_indirect_floatDst_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_move_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hagree himm_src hne_ds
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_move_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_move_indirect_floatDst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hdst_fmt
    (fun h => absurd h (by decide)) himm_src hne_ds hid_lt hbase hfind_la hshape_la hind_dst hptr8

end LeanMiriSpec.Correspondence
