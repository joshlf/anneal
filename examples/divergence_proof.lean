import LeanMiriSpec.Correspondence.SimLM3_2
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
set_option maxHeartbeats 800000
private theorem annealReadImmediate_indirect_prim_eq₂
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    annealReadImmediate ⟨.indirect mp, translateTy ty ly⟩ =
      annealReadMemoryPlace mp (translateTy ty ly) := by
  have hf : (translateTy ty ly).layout.fields = .Primitive := by
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
      (try cases it) <;> (try cases ut) <;>
      (unfold translateTy; rw [hk]; rfl)
  funext st
  unfold annealReadImmediate
  dsimp only
  rw [hf]
theorem step_safeRef_deref_read_invalid_scalar_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → Operand} {span : String}
    (hopKind : opKind = Operand.copy ∨ opKind = Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? body.localDecls e.localIdx = some allocDecl ∧
        allocDecl.ty.kind = dstDecl.ty.kind ∧
              (translateTy dstDecl.ty body.layouts).layout.size = (translateTy allocDecl.ty body.layouts).layout.size ∧
        (∃ sc, get? s.frame.locals e.localIdx = some (.init (.scalar sc)) ∧
        ¬ AnnealScalarValid dstDecl.ty sc) ∧
        ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
        get? s.frame.locals dstIdx ≠ some .dead) :
    ∀ s', stepMirFn body s = MirStepNode.step s' →
      ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .error (.undefinedBehavior msg)) := by
  intro s' hstep
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  have himm_r := (himm tf hframes).2
  have himm_d := (himm tf hframes).1
  obtain ⟨slot_r, mls_r, _, hlt_af_r, hs_slot_r, hmls_r_opt, hm_slot_r, hrel_r⟩ := hfr.lookup_local hdecl_ref
  rcases hrel_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r_opt) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal, mptr, hp_eq, hptrRel, hmr_ptr⟩
  · rcases h with ⟨rfl, _⟩; rw [stepMirFn_eq_of_not_other body s hcal hphase] at hstep; simp only [hbb, hstmt] at hstep; unfold evalStmt evalRvalue at hstep; rcases hopKind with rfl | rfl <;> (unfold evalOperand readProjectedValue at hstep; dsimp only [] at hstep; rw [hs_slot_r] at hstep; dsimp only [] at hstep; contradiction)
  · rcases h with ⟨rfl, _⟩; rw [stepMirFn_eq_of_not_other body s hcal hphase] at hstep; simp only [hbb, hstmt] at hstep; unfold evalStmt evalRvalue at hstep; rcases hopKind with rfl | rfl <;> (unfold evalOperand readProjectedValue at hstep; dsimp only [] at hstep; rw [hs_slot_r] at hstep; dsimp only [] at hstep; contradiction)
  · rcases h with ⟨sc, msc, rfl, _⟩; rw [stepMirFn_eq_of_not_other body s hcal hphase] at hstep; simp only [hbb, hstmt] at hstep; unfold evalStmt evalRvalue at hstep; rcases hopKind with rfl | rfl <;> (unfold evalOperand readProjectedValue at hstep; dsimp only [] at hstep; rw [hs_slot_r] at hstep; dsimp only [] at hstep; contradiction)
  subst hp_eq
  rcases hptrRel with ⟨allocId, borTag, hprov, hid, hoff, haddr, ⟨e_ptr, he_ptr, htag_ptr, hea⟩⟩
  obtain ⟨hdecl_a, htarget_kind, hsize, ⟨sc, htarget, hvalid⟩, hzero, hperm, hdst_live⟩ := hlive_ref ptrVal hs_slot_r e_ptr he_ptr htag_ptr
  have hmsg : ∃ m', Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩) m =
      (m', .error (.undefinedBehavior "reading invalid value")) := by
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_df, hmls_d, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, tf.locals[dstIdx].layout = some l → l = translateTy dstDecl.ty body.layouts := by
      intro l hl
      rw [hmls_d_eq] at hl
      exact hloc_d.cachedLayout_eq l hl
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
    rw [hm_stmt]
    rcases hopKind with rfl | rfl
    · dsimp [translateRvalue, Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace]
      simp only [translatePlace, List.map_nil]
      rw [EStateM.bind_eq_ok hdst_eval]
      let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
      have hframes_a : { stack := { frames := #[tfa] }, machine := m.machine : AnnealStepState }.stack.frames = #[tfa] := rfl
      have hlt_r_a : refIdx < tfa.locals.size := by
        dsimp [tfa, cacheFrameLocalLayout]
        rw [Array.size_set]
        exact hlt_af_r
      have hmls_r_a : tfa.locals[refIdx]'hlt_r_a = tf.locals[refIdx]'hlt_af_r := by
        have hdne : dstIdx ≠ refIdx := by
          intro heq
          have hdecl_eq : dstDecl = refDecl := by
            subst heq
            rw [hdecl_dst] at hdecl_ref
            injection hdecl_ref
          rw [hdecl_eq] at hdst_prim
          rcases hdst_prim with h | h | ⟨w, h⟩ | ⟨w, h⟩
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
        dsimp [tfa, cacheFrameLocalLayout]
        have hne : dstIdx ≠ refIdx := hdne
        exact Array.getElem_set_ne hlt_d hlt_af_r hne
      have hm_slot_r_tfa : tfa.locals[refIdx]'hlt_r_a = ⟨mls_r.value, mls_r.layout⟩ := by
        rw [hmls_r_a, hm_slot_r]
      have hmls_r' : tfa.locals[refIdx]'hlt_r_a =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), mls_r.layout⟩ := by
        rw [hm_slot_r_tfa, hmr_ptr]
      have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
      have hfra := hstate_a.frame_rel_singleton rfl
      obtain ⟨_, mls_ra, _, _, _, _, hmls_ra_eq, hloc_ra⟩ := hfra.lookup_local hdecl_ref
      have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts := by
        intro l hl
        have hl' : mls_ra.layout = some l := by
          rw [← hmls_ra_eq]
          rw [hm_slot_r_tfa]
          exact hl
        exact hloc_ra.cachedLayout_eq l hl'
      have hop_ptr := annealEvalOperand_deref_live (opKind := .copy) (by exact Or.inl rfl)
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_r_a hdecl_ref hmls_r' hcache_r
      have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
        rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
      have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
          translateTy dstDecl.ty body.layouts :=
        hdst_prim.translateTy_layoutIdx body.layouts
      have ht_ne_some_dead : get? s.frame.locals e_ptr.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have htgt_kind : ∀ tgtDecl, get? body.localDecls e_ptr.localIdx = some tgtDecl → tgtDecl.ty.kind = dstDecl.ty.kind := by
        intro tgtDecl htgt_decl; rw [htgt_decl] at hdecl_a; injection hdecl_a with hdecl_eq; rw [hdecl_eq]; exact htarget_kind
      have hprov_eq : mptr.provenance = .concrete e_ptr.allocId borTag := by
        rw [← hea] at hprov; exact hprov
      have hmptr_off : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId + UInt64.ofNat ptrVal.offsetBytes) := by
        rw [← hea] at haddr; exact haddr
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate_a hdecl_ref href_ty
        hprim0 hprov_eq hmptr_off he_ptr hzero ht_ne_some_dead htgt_kind
        (translateTy refDecl.ty body.layouts) (st := { stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)]⟩, machine := m.machine }) rfl
      rw [hlay0_eq] at hder_ok
      have hop_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (Operand.copy ⟨refIdx, .cons .deref .nil⟩)) (some (translateTy dstDecl.ty body.layouts)) { stack := { frames := #[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)] }, machine := m.machine } = .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩, translateTy dstDecl.ty body.layouts⟩ { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]
        rfl
      obtain ⟨tf_a, hframes_tf_a, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      have hid_a := (halloc_a.base_addr_valid e_ptr he_ptr).1
      have hbase_a' := (halloc_a.base_addr_valid e_ptr he_ptr).2.2
      obtain ⟨hloc_sync, _⟩ := halloc_a.local_alloc_sync tfa rfl e_ptr he_ptr
      obtain ⟨_, _, hfind_decl⟩ := hloc_sync (.init (.scalar sc)) htarget (by intro h; contradiction)
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hfind_decl allocDecl hdecl_a
      have hsz_eq : localAlloc.allocation.byteSize = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hshape_la.byteSize_eq]
        exact hsize.symm
      have halloc_prim : IsPrimScalarTy allocDecl.ty := by
        rcases hdst_prim with h | h | ⟨w, h⟩ | ⟨w, h⟩
        · exact Or.inl (by rw [htarget_kind, h])
        · exact Or.inr (Or.inl (by rw [htarget_kind, h]))
        · exact Or.inr (Or.inr (Or.inl ⟨w, by rw [htarget_kind, h]⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨w, by rw [htarget_kind, h]⟩))
      have hlay_eq2 : translateTy allocDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
        have h1 : allocDecl.ty.kind = dstDecl.ty.kind := htarget_kind
        revert hdst_prim h1
        rcases allocDecl.ty with ⟨kind_a, lidx_a⟩
        rcases dstDecl.ty with ⟨kind_d, lidx_d⟩
        intro hdst_prim h1
        change kind_a = kind_d at h1
        subst h1
        rcases hdst_prim with h|h|⟨w,h⟩|⟨w,h⟩ <;> subst h <;> (try cases w) <;> rfl




      have hsz_eq2 : localAlloc.allocation.byteSize = (translateTy allocDecl.ty body.layouts).layout.size := by
        rw [hsz_eq]
        rw [hlay_eq2]
      have hread_mem_eq := annealReadMemoryPlace_zero_offset_eq halloc_prim hid_a hbase_a' hfind_la hsz_eq2 (borTag := borTag) (st := { stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)]⟩, machine := m.machine })
      obtain ⟨slot_t, mls_t, _, _, hs_slot_t, hmls_t_opt, _, hloc_t⟩ := hfra.lookup_local hdecl_a
      have hslot_t_eq : slot_t = .init (.scalar sc) := by
        have ht := htarget
        rw [hs_slot_t] at ht
        injection ht
      have hloc_t_1 : LocalRelLM3_1 m.machine allocMap allocDecl body.layouts (.init (.scalar sc)) mls_t := by
        subst hslot_t_eq
        cases hloc_t
        · case lm3_1 hloc_t_1 => exact hloc_t_1
      obtain ⟨⟨lay_a, hlay_a⟩, _, hfind_decl⟩ := hloc_sync (.init (.scalar sc)) htarget (by intro h; contradiction)
      have hmls_t_a : mls_t = ⟨.live (.indirect (stackAllocPlace e_ptr.allocId)), lay_a⟩ := by
        have htmp := hmls_t_opt
        rw [hlay_a] at htmp
        injection htmp with htmp_eq
        exact htmp_eq.symm
      obtain ⟨localAlloc2, hfind_la2, hkind_la, halign_la, hshape_la⟩ := hfind_decl allocDecl hdecl_a
      have hmm := LocalRelLM3_1.indirect_stackAllocPlace_spec hloc_t_1 hmls_t_a hbase_a' hfind_la (halloc_a.live_key_unique e_ptr he_ptr) (by
        rw [← hsize]
        exact hdst_prim.size_ne_zero)
      obtain ⟨hsz_msc, _, _, msc, hsc_rel, hread_msc⟩ := hmm.2 sc rfl
      have hvalid_alloc : ¬ AnnealScalarValid allocDecl.ty sc := by
        intro h
        apply hvalid
        dsimp only [AnnealScalarValid] at h ⊢
        rw [← htarget_kind]
        exact h
      have hval_false := annealValidateScalarForTyId_false_of_not_scalarValid body.layouts hsc_rel hsz_msc hvalid_alloc
      have hread_imm := annealReadImmediate_indirect_prim_eq₂ (ty := dstDecl.ty) (ly := body.layouts) hdst_prim ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩
      rw [EStateM.bind_eq_ok hop_ok]
      have hcomb : annealReadImmediate ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩, translateTy dstDecl.ty body.layouts⟩ { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } = .error (.undefinedBehavior "reading invalid value") { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } := by
        rw [hread_imm]
        rw [← hlay_eq2]
        rw [hread_mem_eq]
        rw [hread_msc]
        dsimp only []
        rw [hval_false]
        rfl
      exact ⟨_, by rw [EStateM.bind_eq_error hcomb]⟩
    · dsimp [translateRvalue, Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace]
      simp only [translatePlace, List.map_nil]
      rw [EStateM.bind_eq_ok hdst_eval]
      let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
      have hframes_a : { stack := { frames := #[tfa] }, machine := m.machine : AnnealStepState }.stack.frames = #[tfa] := rfl
      have hlt_r_a : refIdx < tfa.locals.size := by
        dsimp [tfa, cacheFrameLocalLayout]
        rw [Array.size_set]
        exact hlt_af_r
      have hmls_r_a : tfa.locals[refIdx]'hlt_r_a = tf.locals[refIdx]'hlt_af_r := by
        have hdne : dstIdx ≠ refIdx := by
          intro heq
          have hdecl_eq : dstDecl = refDecl := by
            subst heq
            rw [hdecl_dst] at hdecl_ref
            injection hdecl_ref
          rw [hdecl_eq] at hdst_prim
          rcases hdst_prim with h | h | ⟨w, h⟩ | ⟨w, h⟩
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
          · rw [h] at href_ty; contradiction
        dsimp [tfa, cacheFrameLocalLayout]
        have hne : dstIdx ≠ refIdx := hdne
        exact Array.getElem_set_ne hlt_d hlt_af_r hne
      have hm_slot_r_tfa : tfa.locals[refIdx]'hlt_r_a = ⟨mls_r.value, mls_r.layout⟩ := by
        rw [hmls_r_a, hm_slot_r]
      have hmls_r' : tfa.locals[refIdx]'hlt_r_a =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), mls_r.layout⟩ := by
        rw [hm_slot_r_tfa, hmr_ptr]
      have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
      have hfra := hstate_a.frame_rel_singleton rfl
      obtain ⟨_, mls_ra, _, _, _, _, hmls_ra_eq, hloc_ra⟩ := hfra.lookup_local hdecl_ref
      have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts := by
        intro l hl
        have hl' : mls_ra.layout = some l := by
          rw [← hmls_ra_eq]
          rw [hm_slot_r_tfa]
          exact hl
        exact hloc_ra.cachedLayout_eq l hl'
      have hop_ptr := annealEvalOperand_deref_live (opKind := .move) (by exact Or.inr rfl)
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_r_a hdecl_ref hmls_r' hcache_r
      have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
        rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
      have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
          translateTy dstDecl.ty body.layouts :=
        hdst_prim.translateTy_layoutIdx body.layouts
      have ht_ne_some_dead : get? s.frame.locals e_ptr.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have htgt_kind : ∀ tgtDecl, get? body.localDecls e_ptr.localIdx = some tgtDecl → tgtDecl.ty.kind = dstDecl.ty.kind := by
        intro tgtDecl htgt_decl; rw [htgt_decl] at hdecl_a; injection hdecl_a with hdecl_eq; rw [hdecl_eq]; exact htarget_kind
      have hprov_eq : mptr.provenance = .concrete e_ptr.allocId borTag := by
        rw [← hea] at hprov; exact hprov
      have hmptr_off : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId + UInt64.ofNat ptrVal.offsetBytes) := by
        rw [← hea] at haddr; exact haddr
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate_a hdecl_ref href_ty
        hprim0 hprov_eq hmptr_off he_ptr hzero ht_ne_some_dead htgt_kind
        (translateTy refDecl.ty body.layouts) (st := { stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)]⟩, machine := m.machine }) rfl
      rw [hlay0_eq] at hder_ok
      have hop_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (Operand.move ⟨refIdx, .cons .deref .nil⟩)) (some (translateTy dstDecl.ty body.layouts)) { stack := { frames := #[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)] }, machine := m.machine } = .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩, translateTy dstDecl.ty body.layouts⟩ { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]
        rfl
      obtain ⟨tf_a, hframes_tf_a, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      have hid_a := (halloc_a.base_addr_valid e_ptr he_ptr).1
      have hbase_a' := (halloc_a.base_addr_valid e_ptr he_ptr).2.2
      obtain ⟨hloc_sync, _⟩ := halloc_a.local_alloc_sync tfa rfl e_ptr he_ptr
      obtain ⟨_, _, hfind_decl⟩ := hloc_sync (.init (.scalar sc)) htarget (by intro h; contradiction)
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hfind_decl allocDecl hdecl_a
      have hsz_eq : localAlloc.allocation.byteSize = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hshape_la.byteSize_eq]
        exact hsize.symm
      have halloc_prim : IsPrimScalarTy allocDecl.ty := by
        rcases hdst_prim with h | h | ⟨w, h⟩ | ⟨w, h⟩
        · exact Or.inl (by rw [htarget_kind, h])
        · exact Or.inr (Or.inl (by rw [htarget_kind, h]))
        · exact Or.inr (Or.inr (Or.inl ⟨w, by rw [htarget_kind, h]⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨w, by rw [htarget_kind, h]⟩))
      have hlay_eq2 : translateTy allocDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
        have h1 : allocDecl.ty.kind = dstDecl.ty.kind := htarget_kind
        revert hdst_prim h1
        rcases allocDecl.ty with ⟨kind_a, lidx_a⟩
        rcases dstDecl.ty with ⟨kind_d, lidx_d⟩
        intro hdst_prim h1
        change kind_a = kind_d at h1
        subst h1
        rcases hdst_prim with h|h|⟨w,h⟩|⟨w,h⟩ <;> subst h <;> (try cases w) <;> rfl




      have hsz_eq2 : localAlloc.allocation.byteSize = (translateTy allocDecl.ty body.layouts).layout.size := by
        rw [hsz_eq]
        rw [hlay_eq2]
      have hread_mem_eq := annealReadMemoryPlace_zero_offset_eq halloc_prim hid_a hbase_a' hfind_la hsz_eq2 (borTag := borTag) (st := { stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)]⟩, machine := m.machine })
      obtain ⟨slot_t, mls_t, _, _, hs_slot_t, hmls_t_opt, _, hloc_t⟩ := hfra.lookup_local hdecl_a
      have hslot_t_eq : slot_t = .init (.scalar sc) := by
        have ht := htarget
        rw [hs_slot_t] at ht
        injection ht
      have hloc_t_1 : LocalRelLM3_1 m.machine allocMap allocDecl body.layouts (.init (.scalar sc)) mls_t := by
        subst hslot_t_eq
        cases hloc_t
        · case lm3_1 hloc_t_1 => exact hloc_t_1
      obtain ⟨⟨lay_a, hlay_a⟩, _, hfind_decl⟩ := hloc_sync (.init (.scalar sc)) htarget (by intro h; contradiction)
      have hmls_t_a : mls_t = ⟨.live (.indirect (stackAllocPlace e_ptr.allocId)), lay_a⟩ := by
        have htmp := hmls_t_opt
        rw [hlay_a] at htmp
        injection htmp with htmp_eq
        exact htmp_eq.symm
      obtain ⟨localAlloc2, hfind_la2, hkind_la, halign_la, hshape_la⟩ := hfind_decl allocDecl hdecl_a
      have hmm := LocalRelLM3_1.indirect_stackAllocPlace_spec hloc_t_1 hmls_t_a hbase_a' hfind_la (halloc_a.live_key_unique e_ptr he_ptr) (by
        rw [← hsize]
        exact hdst_prim.size_ne_zero)
      obtain ⟨hsz_msc, _, _, msc, hsc_rel, hread_msc⟩ := hmm.2 sc rfl
      have hvalid_alloc : ¬ AnnealScalarValid allocDecl.ty sc := by
        intro h
        apply hvalid
        dsimp only [AnnealScalarValid] at h ⊢
        rw [← htarget_kind]
        exact h
      have hval_false := annealValidateScalarForTyId_false_of_not_scalarValid body.layouts hsc_rel hsz_msc hvalid_alloc
      have hread_imm := annealReadImmediate_indirect_prim_eq₂ (ty := dstDecl.ty) (ly := body.layouts) hdst_prim ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩
      rw [EStateM.bind_eq_ok hop_ok]
      have hcomb : annealReadImmediate ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e_ptr.allocId), some (.concrete e_ptr.allocId borTag)⟩, .none, none⟩, translateTy dstDecl.ty body.layouts⟩ { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } = .error (.undefinedBehavior "reading invalid value") { stack := { frames := #[cacheFrameLocalLayout tfa refIdx hlt_r_a (translateTy refDecl.ty body.layouts)] }, machine := m.machine } := by
        rw [hread_imm]
        rw [← hlay_eq2]
        rw [hread_mem_eq]
        rw [hread_msc]
        dsimp only []
        rw [hval_false]
        rfl
      exact ⟨_, by rw [EStateM.bind_eq_error hcomb]⟩
  obtain ⟨m', hmsg_eq⟩ := hmsg
  refine ⟨m', _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hmsg_eq⟩