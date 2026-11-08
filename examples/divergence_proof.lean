import LeanMiriSpec.Correspondence.SimLM3_2

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

set_option maxHeartbeats 800000

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
        (translateTy dstDecl.ty body.layouts).layout.size = (translateTy allocDecl.ty body.layouts).layout.size ∧
        (∃ sc, get? s.frame.locals e.localIdx = some (.init (.scalar sc)) ∧
        ¬ AnnealScalarValid dstDecl.ty sc) ∧
        ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
        get? s.frame.locals dstIdx ≠ some .dead) :
    ∀ s', stepMirFn body s = MirStepNode.step s' →
      ∃ msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m, .error (.undefinedBehavior msg)) := by
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
  rcases hptrRel with ⟨allocId, borTag, hprov, hid, hoff, haddr, ⟨e, he, htag, hea⟩⟩
  obtain ⟨hdecl_a, hsize, ⟨sc, htarget, hvalid⟩, hzero, hperm, hdst_live⟩ := hlive_ref ptrVal hs_slot_r e he htag
  have hmsg : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩) m =
      (m, .error (.undefinedBehavior "reading invalid value")) := by
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
      simp only [translatePlace, List.map_nil, hdst_eval, bind, EStateM.bind, bind, EStateM.bind]
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
      sorry
    · dsimp [translateRvalue, Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace]
      simp only [translatePlace, List.map_nil, hdst_eval, bind, EStateM.bind, bind, EStateM.bind]
      sorry
  refine ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hmsg⟩

theorem test_eval_op {body : CapturedMir} {tf tfa : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
  {dstIdx refIdx : Local} {dstDecl : LocalDecl} {m : AnnealStepState}
  {ptrVal : ProvenancePtr}
  (heval_op : annealEvalOperand body.localDecls body.layouts
          (translateOperand (Operand.copy { local_ := refIdx, projection := [ProjectionElem.deref] }))
          (some (translateTy dstDecl.ty body.layouts))
          { stack := { frames := #[tfa] }, machine := m.machine } =
    .ok ⟨.indirect (Miri.Interpreter.MemPlace.mk (some ptrVal.prov) (Miri.Memory.Size.bytes ptrVal.offsetBytes) .none), translateTy dstDecl.ty body.layouts⟩ { stack := { frames := #[tfa] }, machine := m.machine }) :
  (match
      match
        annealEvalOperand body.localDecls body.layouts
          (translateOperand (Operand.copy { local_ := refIdx, projection := [ProjectionElem.deref] }))
          (some (translateTy dstDecl.ty body.layouts))
          { stack := { frames := #[tfa] },
            machine := m.machine } with
      | EStateM.Result.ok a s =>
        match annealReadImmediate a s with
        | EStateM.Result.ok a s =>
          annealWriteImmediate a.imm
            { ref := Miri.Interpreter.RuntimePlaceRef.local 0 dstIdx none tf.localsIdentity,
              layout := translateTy dstDecl.ty body.layouts }
            s
        | EStateM.Result.error e s => EStateM.Result.error e s
      | EStateM.Result.error e s => EStateM.Result.error e s with
    | EStateM.Result.ok value state => (state, Except.ok value)
    | EStateM.Result.error error state => (state, Except.error error)) = sorry := by
  rw [heval_op]
  sorry
