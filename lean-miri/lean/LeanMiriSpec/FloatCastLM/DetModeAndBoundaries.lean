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
# Deterministic NaN mode and boundaries (`LeanMiriSpec.FloatCastLM.DetModeAndBoundaries`)

Third layer (Parts 8c, 8d, and 9, parallel sibling of `RealStepIndirect` over `RealStepDirect`) of
the IEEE-754 float-cast correspondence; see the umbrella module `LeanMiriSpec.FloatCastLM` for the
architectural overview and the submodule map.

* **Part 8c. Deterministic NaN mode and NaN-choice refinement**:
  `step_cast_floatToFloat_{constant,copy,move}_deterministic_spec`,
  `step_cast_floatToFloat_{constant,copy,move}_nanChoice_simulation`,
  `step_cast_floatToFloat_{constant,copy,move}_deterministic_simulation`,
  `step_cast_floatToFloat_{constant,copy,move}_pure_index_simulation`, and
  `step_cast_floatToFloat_constant_pure_out_of_range`.
* **Part 8d. Tightness of `FloatCastDetAgrees`**:
  `step_cast_floatToFloat_{copy,constant,move}_deterministic_lockstep_iff`.
* **Part 9. Boundaries**: two-sided `bool` / `char` (`evalFloatCast_intToFloat_bool_char_none`,
  `cast_intToFloat_{bool,char}_miri_ok`) and `f16` / `f128` (`evalFloatCast_f16_f128_none`,
  `cast_f16_f128_unsupported`, the `step_cast_f16_f128_*` fail-closed, divergence, and lockstep
  characterizations).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Part 8c. Real-step characterization of deterministic NaN mode (`floatNondeterministic := false`) -/

/-- **Real-step deterministic NaN characterization (`_d = const c as dstTy`)** across **every**
`f32` / `f64` bit pattern (without assuming `FloatCastDetAgrees`):
* Anneal's `stepMirFn` steps normally, storing `evalFloatToFloatRoundTiesToEven src dst sc.bits`
  into `_d`.
* `lean-miri`'s `Step.step` under `annealStepHooksFloat ... false chooseNaN` steps normally,
  storing `preferredNaNBits dst` when `isNaNBits src sc.bits = true` and
  `evalFloatToFloatRoundTiesToEven src dst sc.bits` when `isNaNBits src sc.bits = false`.
In particular, the two machines agree bit-exactly iff `isNaNBits src sc.bits = false` or
`evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst`, and otherwise step
normally to distinct IEEE NaN payloads (`div_floatToFloat_deterministic_payloadNaN_step`). -/
theorem step_cast_floatToFloat_constant_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, _, hbor, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun h => hlive_dst (h ▸ hslot_d)
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
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
  obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
    hsrc hdst hrel hsz (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx := himm_d.cache_layout hlt_d _
  obtain ⟨slot_da, mls_da, _, hlt_da, hslot_da, hmls_da, _, hloc_da⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_dst
  have hsda_eq : slot_da = slot_d := by
    rw [hslot_d] at hslot_da; exact Option.some.inj hslot_da.symm
  subst slot_da
  have hold_imm : ∃ oldImm, mls_da.value = .live (.immediate oldImm) := by
    cases hloc_da with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfa _ hmls_da mp)
      | dead _ _ => exact absurd rfl hsd_ne
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
  have hda_live : tfa.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_da.layout⟩ := by
    rw [hmls_da]; rcases mls_da with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
  have hget_da := frame_getLocal_of_getElem? tfa dstIdx _ hda_live
  have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tfa]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_da hget_da
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[{ tfa with
          locals := tfa.locals.set dstIdx
            { tfa.locals[dstIdx]'hlt_da with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
            hlt_da }]⟩ }, .ok ()) := by
    rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast, hw_ok]
  have hloc_a : tfa.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    (hstate_a.frame_rel_singleton rfl).location_eq
  have hm_step := miri_step_at_statement_ok
    (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl hloc_a
  have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
    hstate_a.immediate_not_in_allocMap rfl hslot_d hsd_ne himm_d_tfa
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  have ha_step : stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hstack, hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit =>
      simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hstack hprot ⊢
      cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hstack hprot ⊢
      cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
  refine ⟨_, _, msc', hrel', ha_step, hm_step, rfl, ?_⟩
  simp [Array.getElem?_set_self]

/-- **Real-step deterministic NaN characterization (`_d = copy _s as dstTy`)** across **every**
initialized immediate `f32` / `f64` local `_s` (without assuming `FloatCastDetAgrees`):
* Anneal's `stepMirFn` steps normally, storing `evalFloatToFloatRoundTiesToEven src dst sc.bits`.
* `lean-miri`'s `Step.step` under `annealStepHooksFloat ... false chooseNaN` steps normally,
  storing `preferredNaNBits dst` when `isNaNBits src sc.bits = true` and
  `evalFloatToFloatRoundTiesToEven src dst sc.bits` when `isNaNBits src sc.bits = false`. -/
theorem step_cast_floatToFloat_copy_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, _, hbor, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun h => hlive_dst (h ▸ hslot_d)
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
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    injection hslot_s with hv_eq; injection hv_eq with hsc_eq; injection hsc_eq with hsc_eq'
    subst hsc_eq'
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
      hsrc hdst hrel hsz (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
      (himm_d.cache_layout hlt_d _).cache_layout hlt_sa _
    obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
      hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_dst
    have hsdb_eq : slot_db = slot_d := by
      rw [hslot_d] at hslot_db; exact Option.some.inj hslot_db.symm
    subst slot_db
    have hold_imm : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
      cases hloc_db with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfb _ hmls_db mp)
        | dead _ _ => exact absurd rfl hsd_ne
        | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
    obtain ⟨oldImm, hmd_imm⟩ := hold_imm
    have hdb_live : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
      rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_live
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
      (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[{ tfb with
            locals := tfb.locals.set dstIdx
              { tfb.locals[dstIdx]'hlt_db with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
              hlt_db }]⟩ }, .ok ()) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast, hw_ok]
    have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      (hstate_b.frame_rel_singleton rfl).location_eq
    have hm_step := miri_step_at_statement_ok
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
      hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl hloc_b
    have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
      hstate_b.immediate_not_in_allocMap rfl hslot_d hsd_ne himm_d_tfb
    have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have ha_step : stepMirFn body s =
        MirStepNode.step
          (advanceStmt s
            (s.frame.locals.set dstIdx
              (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
            s.memory) := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hstack, hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit =>
        simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
        congr 2; generalize s.memory = mem at hstack hprot ⊢
        cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
      | init _ =>
        simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
        congr 2; generalize s.memory = mem at hstack hprot ⊢
        cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
    refine ⟨_, _, msc', hrel', ha_step, hm_step, rfl, ?_⟩
    simp [Array.getElem?_set_self]

/-! ### Part 8c (cont.). Deterministic NaN mode as a simulation modulo NaN canonicalization

The `_deterministic_spec` theorems above pin only the destination value of each machine. The
theorems below upgrade them to full `StepRelLM3_1` simulations: `lean-miri`'s deterministic
step (`floatNondeterministic := false`, any `chooseNaN`) is simulated by the Anneal successor
that stores the **canonicalized** result (`preferredNaNBits dst` on NaN inputs, the trusted
conversion otherwise), while Anneal itself stores the trusted (payload-preserving) conversion.
Hence `lean-miri`'s deterministic mode is exactly Anneal with canonicalized NaN payloads, and
the two machines diverge on precisely the destination bits. -/

/-- **Value-split write finisher** (live immediate destination): like
`finish_write_immediate_from_mid_hooks`, but decoupling the value Anneal's `evalRvalue`
computes (`valA`) from the value `valM` that `lean-miri`'s write is related to. Anneal's
statement steps to the successor storing `valA`, and `lean-miri`'s `Step.step` is
`StepRelLM3_1`-simulated by the Anneal successor storing `valM`. -/
theorem finish_write_immediate_split_hooks
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
    (himm_dst_mid : IsImmediateFrameLocal tf_mid dstIdx)
    (hlive_dst : get? s_mid.frame.locals dstIdx ≠ some .dead)
    {valA valM : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok valA s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init valM)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s_mid.frame.locals.set dstIdx (.init valA)) s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s_mid.frame.locals.set dstIdx (.init valM)) s.memory))
        (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hsd_ne : slot_dm ≠ .dead := fun h => hlive_dst (h ▸ hslot_dm)
  have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
    cases hloc_dm with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
      | dead _ _ => exact absurd rfl hsd_ne
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
  have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
    hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_ne himm_dst_mid
  have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
    rw [← hs_mem]; exact hbor_m
  have hprot_s : s.memory.activeProtectors = .nil := by
    rw [← hs_mem]; exact hprot_m
  have hstack_s : s.memory.callStack = .nil := by
    rw [← hs_mem]; exact hstack_m
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
  have hdm_live : tf_mid.locals[dstIdx]? =
      some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
    rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
  have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
  have hw_ok := annealWriteImmediate_live (val := newImm)
    (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
  have hm_ok : Miri.Interpreter.Step.evalStatement hooks ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      ({ m with stack := ⟨#[{ tf_mid with
          locals := tf_mid.locals.set dstIdx
            { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) }
            hlt_dm }]⟩ }, .ok ()) := by
    rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
  have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    have hl := hfr_m.location_eq
    rw [hb_eq, hsi_eq] at hl
    exact hl
  have hadv_eq : ∀ v : Value,
      advanceStmt s (s_mid.frame.locals.set dstIdx (.init v)) s.memory =
        advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init v)) s_mid.memory := by
    intro v; rw [hs_frame_eq]; rfl
  refine ⟨?_, ?_⟩
  · unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
    cases slot_dm with
    | dead => exact absurd rfl hsd_ne
    | uninit =>
      simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
      congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
      cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
      congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
      cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
  · rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid, hadv_eq]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts (.init valM)
        { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) } := by
      rw [List.map_id]
      exact hnew_rel (tf_mid.locals[dstIdx]'hlt_dm).layout
        (by rw [hmls_dm_eq]; exact hloc_dm.cachedLayout_eq)
    have hstep_rel := hstate_mid.advance_write_immediate_perm_map rfl id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hdecl_dst hnot_dst (by rw [hmls_dm_eq]; exact hmd_imm) hnew_d
      hcal_m hstack_m hprot_m hcaller_m (by rw [List.map_id]; exact hbor_m) rfl
    rw [List.map_id, hb_eq, hsi_eq] at hstep_rel
    exact hstep_rel

/-- `LocalRelLM3_1` for a freshly written float-cast scalar destination. -/
theorem floatCast_dst_localRel {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {dstDecl : LocalDecl} {layouts : LayoutTable} (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt} (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (cachedLay : Option Miri.Interpreter.LocalLayout)
    (hc : ∀ l, cachedLay = some l → l = translateTy dstDecl.ty layouts) :
    LocalRelLM3_1 mach allocMap dstDecl layouts (.init (.scalar sc'))
      ⟨.live (.immediate (.scalar (.fromScalarInt msc'))), cachedLay⟩ := by
  obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
  exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
    (Or.inr ⟨.scalar sc', rfl,
      .scalar sc' msc' hrel' hsz' (fun h => absurd h hnb) (fun h => absurd h hnc)⟩))

/-- Destination layout size of a `floatToFloat` cast into `dst`. -/
theorem floatToFloat_dst_size {dstDecl : LocalDecl} {castTy : Ty} {dst : IeeeFormat}
    (layouts : LayoutTable) (hdst : ieeeFormatOfTy? castTy = some dst)
    (hdst_ty : dstDecl.ty.kind = castTy.kind) (bits : Nat) :
    (translateTy dstDecl.ty layouts).layout.size =
      translateSizeBytes (⟨bits, dst.byteWidth⟩ : MirAst.ScalarInt).sizeBytes := by
  have hdst' : ieeeFormatOfTy? dstDecl.ty = some dst := by
    unfold ieeeFormatOfTy? at hdst ⊢; rw [hdst_ty]; exact hdst
  rw [translateTy_of_ieeeFormatOfTy? hdst' layouts, translateSizeBytes_byteWidth,
    floatLayoutData_size]

/-- **Non-vacuity of the `hchoose` selector hypothesis**: every constant selector `pure i` with
`i < 4` is a valid state-preserving NaN selector on every candidate list `nanChoices` produces
(lengths `4` / `6`, `floatBits_nanChoices_nondet_list_eq`). -/
theorem chooseNaN_pure_valid (i : Nat) (hi : i < 4) :
    ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits), 4 ≤ cs.length →
      ∃ idx < cs.length,
        (fun (_ : Unit) (_ : List Miri.Interpreter.FloatBits) =>
          (pure i : Miri.Interpreter.RvalueM AnnealStepState Nat)) () cs st = .ok idx st :=
  fun _ _ hcs => ⟨i, by omega, rfl⟩

/-- The refinement witness `annealChooseQuietedNaN` (index `2`) is a valid NaN selector, so the
any-`chooseNaN` theorems specialize to it. -/
theorem annealChooseQuietedNaN_valid :
    ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits), 4 ≤ cs.length →
      ∃ idx < cs.length, annealChooseQuietedNaN () cs st = .ok idx st :=
  fun _ _ hcs => ⟨2, by omega, rfl⟩

/-- **Full NaN-choice refinement at the step level (`_d = copy _s as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_copy_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
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
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
      cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }
        (fun hnd => hchoose hnd _)
    rw [← hdstT] at hcast
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    exact hev

/-- **Full NaN-choice refinement at the step level (`_d = const c as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_constant_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
    cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
      (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }
      (fun hnd => hchoose hnd _)
  rw [← hdstT] at hcast
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
    hfr.location_eq hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hlive_dst
    hrv_a hm_write
    (floatCast_dst_localRel hdst_scalar hrel' (floatToFloat_dst_size body.layouts hdst hdst_ty _))
  refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact hev

/-- **Full NaN-choice refinement at the step level (`_d = move _s as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_move_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
      cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
        { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } (fun hnd => hchoose hnd _)
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hinit_src (by simp) himm_sb
      hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hinit_src, set?_eq_some_set hlt_af_s]; rfl
      rw [hop]
      dsimp only []
      rw [operandTy_move_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hlive_mid : get? (s.frame.locals.set srcIdx .uninit) dstIdx ≠ some .dead := by
      by_cases hds : srcIdx = dstIdx
      · subst hds
        rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s]
        simp
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?]
        exact hlive_dst
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hlive_mid
      hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    exact hev

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = copy _s as T`,
`floatToFloat`)**: for **every** initialized immediate `f32` / `f64` source bit pattern (NaN or
not, no `FloatCastDetAgrees` side condition) and **any** `chooseNaN`, Anneal's `stepMirFn` steps
to the successor storing the trusted conversion, while `lean-miri`'s `Step.step` under
`annealStepHooksFloat … false chooseNaN` is `StepRelLM3_1`-simulated by the same successor with
the destination replaced by the canonicalized result (`preferredNaNBits dst` on NaN inputs). -/
theorem step_cast_floatToFloat_copy_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_copy_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src
      hlive_dst himm
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = const c as T`,
`floatToFloat`)**: `lean-miri`'s deterministic step is `StepRelLM3_1`-simulated by Anneal's
successor with the destination canonicalized, for every constant bit pattern. -/
theorem step_cast_floatToFloat_constant_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_constant_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hsrc hdst hdst_ty hval hsz hcan
      hlive_dst himm_dst
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = move _s as T`,
`floatToFloat`)**: both machines deinitialize `_s`; Anneal stores the trusted conversion while
`lean-miri`'s deterministic step is `StepRelLM3_1`-simulated by the Anneal successor storing
the canonicalized result. -/
theorem step_cast_floatToFloat_move_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_move_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src
      hlive_dst himm
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Exact step-level constant-index NaN-choice simulation (`_d = copy _s as T`, `floatToFloat`)**:
for any state-preserving constant selector `chooseNaN` returning `i < 4` (`hsel`), `lean-miri`'s
`Step.step` under `annealStepHooksFloat ... true chooseNaN` is `StepRelLM3_1`-simulated by the
Anneal successor storing the **exact** `floatToFloatPureIndexBits src dst sc.bits i` (eliminating
the existential `outBits` of `step_cast_floatToFloat_copy_nanChoice_simulation`). -/
theorem step_cast_floatToFloat_copy_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
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
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msc', hrel', hcast⟩ :=
      cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Exact step-level constant-index NaN-choice simulation (`_d = const c as T`, `floatToFloat`)**:
stores `floatToFloatPureIndexBits src dst sc.bits i` for any `pure i` (`i < 4`). -/
theorem step_cast_floatToFloat_constant_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨msc', hrel', hcast⟩ :=
    cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
      (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
    hfr.location_eq hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hlive_dst
    hrv_a hm_write
    (floatCast_dst_localRel hdst_scalar hrel' (floatToFloat_dst_size body.layouts hdst hdst_ty _))
  refine ⟨?_, hsim⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Exact step-level constant-index NaN-choice simulation (`_d = move _s as T`, `floatToFloat`)**:
deinitializes `_s` and stores `floatToFloatPureIndexBits src dst sc.bits i` for any `pure i`
(`i < 4`). -/
theorem step_cast_floatToFloat_move_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨msc', hrel', hcast⟩ :=
      cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hinit_src (by simp) himm_sb
      hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hinit_src, set?_eq_some_set hlt_af_s]; rfl
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hlive_mid : get? (s.frame.locals.set srcIdx .uninit) dstIdx ≠ some .dead := by
      by_cases hds : srcIdx = dstIdx
      · subst hds; rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s]; simp
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?]; exact hlive_dst
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hlive_mid
      hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Tightness of the selector-validity premise at the step level (`_d = const c as T`,
`floatToFloat`)**: under `floatNondeterministic := true` with a state-preserving constant selector
whose index lies at or beyond the length of the NaN candidate list (e.g. `pure 4` on a quiet NaN),
Anneal steps normally while `lean-miri`'s `Step.step` fails with
`.invalidProgram "invalid floating NaN choice index"`, so no `StepRelLM3_1` relates the two steps:
the `hchoose` / `i < 4` premises of the NaN-choice simulations are necessary. -/
theorem step_cast_floatToFloat_constant_pure_out_of_range
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    {neg q : Bool} {payload : Nat} (hnan : decodeBits src sc.bits = .nan neg q payload)
    {cs : List Miri.Interpreter.FloatBits}
    (hcs : Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] true = .ok cs)
    (hi : cs.length ≤ i)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      (∃ m', Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m =
        (m', .error (.invalidProgram "invalid floating NaN choice index"))) ∧
      ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  have ha := (step_cast_floatToFloat_constant_deterministic_simulation hstate hphase chooseNaN
    hbb hstmt hdecl_dst hsrc hdst hdst_ty hval hsz hcan hlive_dst himm_dst).1
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  have hcast_err := cast_floatToFloat_pure_out_of_range body.layouts chooseNaN i hsel hsrc hdst
    hrel hsz hnan hcs hi (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }
  rw [← hdstT] at hcast_err
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfa]⟩ },
        .error (.invalidProgram "invalid floating NaN choice index")) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast_err]
  have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
    hm_err
  refine ⟨ha, ⟨_, hm_step⟩, fun hrel => ?_⟩
  rw [ha, hm_step] at hrel
  cases hrel

/-! ### Part 8d. Tightness of `FloatCastDetAgrees`: deterministic lockstep iff agreement

The `_mode` step theorems need `FloatCastDetAgrees` in deterministic NaN mode. The theorems
below show the side condition is not merely sufficient but **necessary**: on an initialized
`f32` / `f64` source, `StepRelLM3_1` lockstep between `stepMirFn` and `Step.step` under
`annealStepHooksFloat … false chooseNaN` holds **if and only if** the source is not a NaN or
its quieted conversion already is `preferredNaNBits dst`. -/

/-- Two `ScalarRel` relations sharing one `lean-miri` scalar and one byte width pin the same
Anneal bit pattern (`ScalarRel` is functional in the `lean-miri` → Anneal direction). -/
theorem ScalarRel.bits_eq_of_same_msc {a b w : Nat} {msc : Miri.Memory.ScalarInt}
    (ha : ScalarRel ⟨a, w⟩ msc) (hb : ScalarRel ⟨b, w⟩ msc) : a = b := by
  have hmod : scalarModulus w ≤ 2 ^ 128 := by
    rcases ha.validBytes with h | h | h | h | h <;> (dsimp only at h; subst h; decide)
  have ha_lt : a < 2 ^ 128 := Nat.lt_of_lt_of_le ha.canonical hmod
  have hb_lt : b < 2 ^ 128 := Nat.lt_of_lt_of_le hb.canonical hmod
  have hd : BitVec.ofNat 128 a = BitVec.ofNat 128 b := ha.data_eq.symm.trans hb.data_eq
  have hn := congrArg BitVec.toNat hd
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
    Nat.mod_eq_of_lt hb_lt] at hn

/-- `Scalar.fromScalarInt` is injective. -/
theorem scalar_fromScalarInt_inj {a b : Miri.Memory.ScalarInt}
    (h : (Miri.Memory.Scalar.fromScalarInt a : Miri.Memory.Scalar AnnealProv) =
      Miri.Memory.Scalar.fromScalarInt b) : a = b := by
  unfold Miri.Memory.Scalar.fromScalarInt at h
  injection h with h₁
  injection h₁

/-- Reading back the destination of a deterministic step: if `StateRelLM3_1` relates the
Anneal successor storing `⟨A, w⟩` into `_d` to a `lean-miri` state whose `_d` immediately
holds `fromScalarInt msc` with `ScalarRel ⟨M, w⟩ msc`, then `A = M`. -/
theorem stateRel_dst_scalar_bits_eq {body : CapturedMir} {s : MachineState}
    {locals₀ : List LocalSlot}
    {m' : AnnealStepState} {allocMap : List AllocMapEntry}
    {tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl} {A M w : Nat} {msc : Miri.Memory.ScalarInt}
    (hst : StateRelLM3_1 body
      (advanceStmt s (locals₀.set dstIdx (.init (.scalar ⟨A, w⟩))) s.memory) m' allocMap)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (htf' : m'.stack.frames = #[tf'])
    (hval : (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
      some (.live (.immediate (.scalar (.fromScalarInt msc)))))
    (hrelM : ScalarRel ⟨M, w⟩ msc) :
    A = M := by
  have hfr := hst.frame_rel_singleton htf'
  obtain ⟨slot, mls, hlt_af, _, hslot, hmls, _, hloc⟩ := hfr.lookup_local hdecl_dst
  have hslot_eq : slot = .init (.scalar ⟨A, w⟩) := by
    have hlt : dstIdx < locals₀.length := by
      have h := hlt_af
      simp only [advanceStmt, List.length_set] at h
      exact h
    have h := hslot
    simp only [advanceStmt] at h
    rw [get?_eq_getElem?, List.getElem?_set_self hlt] at h
    exact (Option.some.inj h).symm
  have hmls_val : mls.value = .live (.immediate (.scalar (.fromScalarInt msc))) := by
    rw [hmls] at hval
    exact Option.some.inj hval
  rcases hloc.floatCast_immediate_cases hdst_scalar
      (fun mp h => by rw [hmls_val] at h; cases h) with
    ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨sc₀, msc₀, hs, hrel₀, _, hm₀⟩
  · rw [hslot_eq] at hs; cases hs
  · rw [hslot_eq] at hs; cases hs
  · rw [hslot_eq] at hs
    injection hs with hs₁; injection hs₁ with hs₂; subst hs₂
    rw [hmls_val] at hm₀
    injection hm₀ with hm₁; injection hm₁ with hm₂; injection hm₂ with hm₃
    rw [← scalar_fromScalarInt_inj hm₃] at hrel₀
    exact ScalarRel.bits_eq_of_same_msc hrel₀ hrelM

/-- The `if`-canonicalized deterministic result equals the trusted conversion exactly when
the input is not a NaN or the quieted conversion already is `preferredNaNBits`. -/
theorem detBits_eq_iff_agrees (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst bits =
        (if Anneal.Mir.IeeeFloatCast.isNaNBits src bits then preferredNaNBits dst
          else evalFloatToFloatRoundTiesToEven src dst bits) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst bits = preferredNaNBits dst) := by
  cases hn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits <;> simp

/-- **Tightness of `FloatCastDetAgrees` (`_d = copy _s as T`, `floatToFloat`)**: in
deterministic NaN mode (`floatNondeterministic := false`, **any** `chooseNaN`), on an
initialized immediate `f32` / `f64` source `_s` and a live immediate `_d`, `stepMirFn` and
`Step.step` step in `StepRelLM3_1` lockstep **if and only if** the source is not a NaN or its
quieted conversion already is `preferredNaNBits dst`. -/
theorem step_cast_floatToFloat_copy_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval⟩ :=
      step_cast_floatToFloat_copy_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval hrelM)
  · intro hag
    refine step_cast_float_copy_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hdecl_src hsig hdst_ty ?_ himm hptr8
    intro _ sc' hsc' src' dst' _ hsrc' hdst'
    rw [hinit_src] at hsc'
    cases hsc'
    rw [hsrc] at hsrc'; rw [hdst] at hdst'
    injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
    exact hag

/-- **Tightness of `FloatCastDetAgrees` (`_d = const c as T`, `floatToFloat`)**: in
deterministic NaN mode (**any** `chooseNaN`), `stepMirFn` and `Step.step` step in
`StepRelLM3_1` lockstep **if and only if** the constant is not a NaN or its quieted
conversion already is `preferredNaNBits dst`. -/
theorem step_cast_floatToFloat_constant_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval'⟩ :=
      step_cast_floatToFloat_constant_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hsrc hdst hdst_ty hval hsz hcan hlive_dst himm_dst
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval' hrelM)
  · intro hag
    refine step_cast_float_constant_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hsig hdst_ty hval (hsz ▸ validScalarBytes_byteWidth src) hcan ?_ ?_
      himm_dst hptr8
    · rw [hsz, translateTy_of_ieeeFormatOfTy? hsrc body.layouts, translateSizeBytes_byteWidth,
        floatLayoutData_size]
    · intro _ src' dst' _ hsrc' hdst'
      rw [hsrc] at hsrc'; rw [hdst] at hdst'
      injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
      exact hag

/-- **Real-step deterministic NaN characterization (`_d = move _s as dstTy`)** across **every**
initialized immediate `f32` / `f64` source `_s` (without assuming `FloatCastDetAgrees`),
completing the `{constant, copy, move}` triad alongside
`step_cast_floatToFloat_{constant,copy}_deterministic_spec`. -/
theorem step_cast_floatToFloat_move_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s
            ((s.frame.locals.set srcIdx .uninit).set dstIdx
              (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨ha, _⟩ := step_cast_floatToFloat_move_deterministic_simulation hstate hphase
    chooseNaN hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
  obtain ⟨tf₀, hframes₀, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf₀ hframes₀
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  obtain ⟨_, mls0_d, _, hlt0_d, _, _, hmls0_d_eq, hloc0_d⟩ :=
    (hstate.frame_rel_singleton hframes₀).lookup_local hdecl_dst
  have hcache0_d : ∀ l, (tf₀.locals[dstIdx]'hlt0_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls0_d_eq]; exact hloc0_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes₀ hlt0_d hdecl_dst hcache0_d
  let tfa := cacheFrameLocalLayout tf₀ dstIdx hlt0_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes₀ hdecl_dst hlt0_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt0_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
      hsrc hdst hrel hsz (.local 0 dstIdx none tf₀.localsIdentity)
    have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
      hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
      chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
    let tfc := deinitFrameLocal tfb srcIdx hlt_sb
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf₀.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have himm_sb := (himm_s.cache_layout hlt0_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := (hstate_a.cache_layout rfl hdecl_src hlt_sa).deinit_immediate_local rfl
      hdecl_src hinit_src (by simp) himm_sb hlt_sb
    have himm_d_tfc : IsImmediateFrameLocal tfc dstIdx :=
      (((himm_d.cache_layout hlt0_d (translateTy dstDecl.ty body.layouts)).cache_layout hlt_sa
        (translateTy srcDecl.ty body.layouts)).deinit_local hlt_sb)
    obtain ⟨slot_dc, mls_dc, _, hlt_dc, hslot_dc, hmls_dc, _, hloc_dc⟩ :=
      hstate_mid.frame_rel_singleton rfl |>.lookup_local hdecl_dst
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hlive_mid : slot_dc ≠ .dead := by
      intro hdead; subst hdead
      by_cases hds : srcIdx = dstIdx
      · subst hds; rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s] at hslot_dc; cases hslot_dc
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?] at hslot_dc
        exact hlive_dst hslot_dc
    have hold_imm : ∃ oldImm, mls_dc.value = .live (.immediate oldImm) := by
      cases hloc_dc with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfc _ hmls_dc mp)
        | dead _ _ => exact absurd rfl hlive_mid
        | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
    obtain ⟨oldImm, hmd_imm⟩ := hold_imm
    have hdc_live : tfc.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
      rw [hmls_dc]; rcases mls_dc with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_live
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
      (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tf₀.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[{ tfc with
            locals := tfc.locals.set dstIdx
              { tfc.locals[dstIdx]'hlt_dc with
                value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
              hlt_dc }]⟩ }, .ok ()) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      (hstate_mid.frame_rel_singleton rfl).location_eq
    have hm_step := miri_step_at_statement_ok
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
      hframes₀ (hstate.frame_rel_singleton hframes₀).body_eq
      (hstate.frame_rel_singleton hframes₀).location_eq hbb hstmt hm_ok rfl hloc_c
    refine ⟨_, _, msc', hrel', ha, hm_step, rfl, ?_⟩
    simp [Array.getElem?_set_self]

/-- **Tightness of `FloatCastDetAgrees` (`_d = move _s as T`, `floatToFloat`)**: in
deterministic NaN mode (`floatNondeterministic := false`, **any** `chooseNaN`), on an
initialized immediate `f32` / `f64` source `_s` and a live immediate `_d`, `stepMirFn` and
`Step.step` step in `StepRelLM3_1` lockstep **if and only if** the source is not a NaN or its
quieted conversion already is `preferredNaNBits dst` (covering both `srcIdx ≠ dstIdx` and
self-move `srcIdx = dstIdx`). -/
theorem step_cast_floatToFloat_move_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval⟩ :=
      step_cast_floatToFloat_move_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s
          ((s.frame.locals.set srcIdx .uninit).set dstIdx
            (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval hrelM)
  · intro hag
    refine step_cast_float_move_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hdecl_src hsig hdst_ty ?_ himm hptr8
    intro _ sc' hsc' src' dst' _ hsrc' hdst'
    rw [hinit_src] at hsc'
    cases hsc'
    rw [hsrc] at hsrc'; rw [hdst] at hdst'
    injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
    exact hag

/-! ## Part 9. Boundaries -/

/-- **`bool` / `char` source boundary of `CastKind.intToFloat`**: Anneal's
`evalFloatCast` models only integer sources (`floatIntTargetOfTy?`), so a `bool` or
`char` source fails closed (`none`, hence `RvalueEvalResult.unsupported`), whereas
`lean-miri`'s `Cast.cast .IntToFloat` accepts `.boolean` / `.character` (rustc never
emits such a cast: `bool as f32` and `char as f32` are rejected by type checking). -/
theorem evalFloatCast_intToFloat_bool_char_none {srcTy castTy : Ty} (layouts : LayoutTable)
    (v : Value) (hsrc : srcTy.kind = .bool ∨ srcTy.kind = .char) :
    evalFloatCast .intToFloat (some srcTy) castTy layouts v = none := by
  have hnone : floatIntTargetOfTy? srcTy = none := by
    unfold floatIntTargetOfTy?; rcases hsrc with h | h <;> rw [h]
  unfold evalFloatCast
  cases v <;> simp [hnone]

/-- Vendored `Miri.Memory.ScalarInt.isUnicodeScalar` (`private`, `ScalarInt.lean:197-198`). -/
local macro "miriIsUnicodeScalar" : term =>
  `(miri_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.isUnicodeScalar)

theorem scalar_fromBool_toBool (b : Bool) :
    (Miri.Memory.Scalar.fromBool (Prov := AnnealProv) b).toBool = .ok b := by
  cases b <;> rfl

theorem scalar_fromChar_toChar (ch : Char) :
    (Miri.Memory.Scalar.fromChar (Prov := AnnealProv) ch).toChar = .ok ch := by
  rcases ch with ⟨v, hv⟩
  have hv_lt : v.toNat < 4294967296 := v.toBitVec.isLt
  have hu32 : UInt32.ofNat v.toNat = v := UInt32.ofNat_toNat
  have hbv : (BitVec.ofNat 128 v.toNat).toNat = v.toNat := Nat.mod_eq_of_lt (by omega)
  have his : miriIsUnicodeScalar v.toNat = true := by
    change (decide (v.toNat ≤ 0x10ffff) &&
        !(decide (0xd800 ≤ v.toNat) && decide (v.toNat ≤ 0xdfff))) = true
    unfold UInt32.isValidChar Nat.isValidChar at hv
    rcases hv with h1 | ⟨h1, h2⟩ <;> simp <;> omega
  unfold Miri.Memory.Scalar.fromChar Miri.Memory.Scalar.toChar
    Miri.Memory.Scalar.toScalarInt Miri.Memory.Scalar.tryToScalarInt
    Miri.Memory.Scalar.fromScalarInt Miri.Memory.ScalarInt.ofChar
    Miri.Memory.ScalarInt.ofUInt32 Miri.Memory.ScalarInt.toChar
    Miri.Memory.ScalarInt.toUInt32 Miri.Memory.ScalarInt.toUInt
    Miri.Memory.ScalarInt.toBits Char.toNat
  dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hu32, hbv, his, Bool.not_true]
  congr 1
  unfold Char.ofNat
  have hvn : v.toNat.isValidChar := hv
  simp only [hvn, ↓reduceDIte]
  congr 1

/-- **Miri side of the `bool` `IntToFloat` boundary**: while Anneal's `evalFloatCast`
returns `none` and `FloatOps.castIntToFloat` throws `.invalidProgram`, `Cast.cast .IntToFloat`
routes through `Cast.castFromIntLike` (`Cast.lean:98, 115`) and maps `false ↦ +0.0`,
`true ↦ 1.0`. -/
theorem cast_intToFloat_bool_miri_ok (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {dst : IeeeFormat}
    (hsrc : srcTy.kind = .bool) (hdst : ieeeFormatOfTy? targetTy = some dst)
    (b : Bool) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc',
      ScalarRel ⟨evalIntToFloatRoundTiesToEven false 8 (if b then 1 else 0) dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromBool b)), translateTy srcTy layouts⟩ .IntToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt false 8
    (if b then 1 else 0) dst
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalIntToFloatRoundTiesToEven false 8 (if b then 1 else 0) dst)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT : translateTy srcTy layouts =
      { ty := 1, layout := scalarLayoutData 1 false 0 1 } := by
    unfold translateTy encodeTyId; rw [hsrc]
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  have hfi0 : Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri dst)
      (Int.ofNat (0 : BitVec 128).toNat) =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalIntToFloatRoundTiesToEven false 8 0 dst)⟩ :=
    floatBits_fromInteger_intValueOfBits false 8 0 dst
  have hfi1 : Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri dst)
      (Int.ofNat (1 : BitVec 128).toNat) =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalIntToFloatRoundTiesToEven false 8 1 dst)⟩ :=
    floatBits_fromInteger_intValueOfBits false 8 1 dst
  have htb := scalar_fromBool_toBool b
  cases b <;>
  · simp only [↓reduceIte, Bool.false_eq_true] at hfrom htb ⊢
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      pure_bind, annealReadImmediate_scalar, cast_scalarOf_scalar,
      show castTypeInfoOfEncodedTyIdFloat 1 = .ok .boolean from rfl,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf]
    unfold Miri.Interpreter.Cast.castFromIntLike Miri.Interpreter.Cast.intLikeValue
    simp only [show (scalarLayoutData 1 false 0 1).backendRepr.isSigned = .ok false from rfl,
      show castTypeInfoOfEncodedTyIdFloat 1 = .ok .boolean from rfl,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true, ↓reduceIte,
      htb, hfi0, hfi1, hfrom, Except.mapError, cast_liftResult_ok, floatLayoutData_size,
      bne_self_eq_false]

/-- **Miri side of the `char` `IntToFloat` boundary**: while Anneal's `evalFloatCast`
returns `none` and `FloatOps.castIntToFloat` throws `.invalidProgram`, `Cast.cast .IntToFloat`
routes through `Cast.castFromIntLike` (`Cast.lean:99, 115`) and converts `ch.toNat`
(as a 32-bit unsigned Unicode scalar value) to `dst` via `roundTiesToEven`. -/
theorem cast_intToFloat_char_miri_ok (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {dst : IeeeFormat}
    (hsrc : srcTy.kind = .char) (hdst : ieeeFormatOfTy? targetTy = some dst)
    (ch : Char) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc',
      ScalarRel ⟨evalIntToFloatRoundTiesToEven false 32 ch.toNat dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromChar ch)), translateTy srcTy layouts⟩ .IntToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ := by
  have hch_lt32 : ch.toNat < 2 ^ 32 := ch.val.toBitVec.isLt
  have hch_lt128 : ch.toNat < 2 ^ 128 := by omega
  have hclt := Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt false 32 ch.toNat dst
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalIntToFloatRoundTiesToEven false 32 ch.toNat dst)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT : translateTy srcTy layouts =
      { ty := 2, layout := scalarLayoutData 4 false 0 0x10FFFF } := by
    unfold translateTy encodeTyId; rw [hsrc]
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hfi := floatBits_fromInteger_intValueOfBits false 32 ch.toNat dst
  have hiv : intValueOfBits false 32 ch.toNat = Int.ofNat (BitVec.ofNat 128 ch.toNat).toNat := by
    unfold intValueOfBits
    simp [Nat.mod_eq_of_lt hch_lt32, Nat.mod_eq_of_lt hch_lt128]
  rw [hiv] at hfi
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
    pure_bind, Bool.false_eq_true, annealReadImmediate_scalar, cast_scalarOf_scalar,
    show castTypeInfoOfEncodedTyIdFloat 2 = .ok .character from rfl,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf]
  unfold Miri.Interpreter.Cast.castFromIntLike Miri.Interpreter.Cast.intLikeValue
  simp only [show (scalarLayoutData 4 false 0 0x10FFFF).backendRepr.isSigned = .ok false from rfl,
    show castTypeInfoOfEncodedTyIdFloat 2 = .ok .character from rfl,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true, ↓reduceIte,
    scalar_fromChar_toChar ch, hfi, hfrom, Except.mapError, cast_liftResult_ok,
    floatLayoutData_size, bne_self_eq_false]

/-- `f16` and `f128` sources and targets fail closed in Anneal's `evalFloatCast`
(matching the overlay, where `castTypeInfoOfEncodedTyIdFloat` rejects TyIds `30` / `33`
with `StepError.unsupported`). -/
theorem evalFloatCast_f16_f128_none (kind : CastKind) {fTy : Ty} (otherTy : Ty)
    (layouts : LayoutTable) (v : Value)
    (hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128) :
    evalFloatCast kind (some fTy) otherTy layouts v = none ∧
      evalFloatCast kind (some otherTy) fTy layouts v = none := by
  have hnone : ieeeFormatOfTy? fTy = none := by
    unfold ieeeFormatOfTy?; rcases hf with h | h <;> rw [h]
  have hnoneI : floatIntTargetOfTy? fTy = none := by
    unfold floatIntTargetOfTy?; rcases hf with h | h <;> rw [h]
  constructor <;> unfold evalFloatCast <;> cases kind <;> cases v <;> simp [hnone, hnoneI]

/-- **Miri side of `f16` / `f128` fail-closed correspondence (`Cast.cast`)**:
1. When `srcTy` is `f16` (`TyId 30`) or `f128` (`TyId 33`), `Cast.cast` rejects the source
   in `h.typeInfo` with `StepError.unsupported` for **any** `srcOp` (even before reading it).
2. When `srcTy` is a modeled float or integer (`IsFloatCastScalarTy srcTy`) holding an
   initialized scalar `msc` of matching byte width and `castTy` is `f16` or `f128`,
   `Cast.cast` rejects `castTy` in `h.typeInfo` with `StepError.unsupported`. -/
theorem cast_f16_f128_unsupported (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    (∀ {kind : CastKind} {fTy castTy : Ty}
      (_hk : isFloatCastKind (translateCastKind kind) = true)
      (_hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128)
      (srcOp : Miri.Interpreter.Operand AnnealProv),
      ∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨srcOp, translateTy fTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
          ⟨destRef, translateTy castTy layouts⟩ st =
        .error (.unsupported msg) st) ∧
    (∀ {kind : CastKind} {srcTy fTy : Ty} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
      (_hk : isFloatCastKind (translateCastKind kind) = true)
      (_hsrc : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcTy = some t) ∨
        ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcTy = some f))
      (_hrel : ScalarRel sc msc)
      (_hsz : (translateTy srcTy layouts).layout.size = translateSizeBytes sc.sizeBytes)
      (_hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128),
      ∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId fTy)
          ⟨destRef, translateTy fTy layouts⟩ st =
        .error (.unsupported msg) st) := by
  refine ⟨?_, ?_⟩
  · intro kind fTy castTy hk hf srcOp
    have hty_err : ∃ msg, castTypeInfoOfEncodedTyIdFloat (translateTy fTy layouts).ty =
        .error (.unsupported msg) := by
      rcases hf with h | h <;> (unfold translateTy encodeTyId; rw [h]; exact ⟨_, rfl⟩)
    obtain ⟨msg, hmsg⟩ := hty_err
    have hdst_ty : (translateTy castTy layouts).ty = encodeTyId castTy := rfl
    cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
    · unfold Miri.Interpreter.Cast.cast
      dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
      simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, pure_bind,
        hmsg, estate_throw_bind_float]
      exact ⟨msg, rfl⟩
  · intro kind srcTy fTy sc msc _hk hsrc hrel hsz hf
    have hty_err : ∃ msg, castTypeInfoOfEncodedTyIdFloat (encodeTyId fTy) =
        .error (.unsupported msg) := by
      rcases hf with h | h <;> (unfold encodeTyId; rw [h]; exact ⟨_, rfl⟩)
    obtain ⟨msg, hmsg⟩ := hty_err
    have hdst_ty : (translateTy fTy layouts).ty = encodeTyId fTy := rfl
    rcases hsrc with ⟨rfl, t, ht⟩ | ⟨hfk, f, hfmt⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht layouts] at hsz ⊢
      unfold Miri.Interpreter.Cast.cast
      dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
      simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
        castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, annealReadImmediate_scalar,
        hmsg, estate_throw_bind_float]
      exact ⟨msg, rfl⟩
    · rw [translateTy_of_ieeeFormatOfTy? hfmt layouts] at hsz ⊢
      have hb := sizeBytes_of_float_layout hrel.validBytes hsz
      rcases hfk with rfl | rfl <;>
      · unfold Miri.Interpreter.Cast.cast
        dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
        simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
          castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, annealReadImmediate_scalar,
          floatOps_readBits_annealFloat nondet chooseNaN f hrel hb,
          hmsg, estate_throw_bind_float]
        exact ⟨msg, rfl⟩

/-- **Two-machine real-step fail-closed theorem on `f16` / `f128` sources**: on any
initialized `f16` or `f128` local `_s`, BOTH Anneal's `stepMirFn` (`MirStepNode.unsupported`)
and `lean-miri`'s `Step.step` under `annealStepHooksFloat` (`.error (.unsupported msg)`)
fail closed! -/
theorem step_cast_f16_f128_source_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {v : Value} (hinit : get? s.frame.locals srcIdx = some (.init v))
    (hno_uninit : valueContainsUninit v = false := by rfl) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  rw [hinit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
  have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
    cases hloc_s with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
      | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
  obtain ⟨opVal, hms_live⟩ := hlive_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
    rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
    (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).1 hk hf opVal
  rw [← hdst_enc] at hcast_err
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue evalOperand readProjectedValue
    dsimp only []; rw [hinit]; dsimp only []; rw [hno_uninit]; dsimp only []
    rw [operandTy_copy_local hdecl_src,
      (evalFloatCast_f16_f128_none kind castTy body.layouts v hf).1]
  exact ⟨ha_unsup, _, msg,
    miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`f16` / `f128` uninitialized-source failure-kind divergence**: on `_d = copy _s as T` with
an *uninitialized* `f16` / `f128` local `_s`, Anneal reports UB (`evalOperand` rejects the
uninitialized read before `evalFloatCast` is consulted), whereas `lean-miri` evaluates the
operand successfully and `Cast.cast` checks the source `typeInfo` (`enforceValidity`) before
reading it, failing closed with `StepError.unsupported`. Both machines fail, but no
`StepRelLM3_1` constructor relates `.fail .ub` to `.unsupported`, so the initialization premise
of `step_cast_f16_f128_source_fail_closed` cannot be dropped. -/
theorem step_cast_f16_f128_uninit_source_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (huninit : get? s.frame.locals srcIdx = some .uninit) :
    stepMirFn body s = MirStepNode.fail .ub ∧
      (∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg))) ∧
      ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  rw [huninit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
  have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
    cases hloc_s with
    | base hb =>
      cases hb with
      | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
      | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
  obtain ⟨opVal, hms_live⟩ := hlive_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
    rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
    (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).1 hk hf opVal
  rw [← hdst_enc] at hcast_err
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
    hm_err
  have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue evalOperand
    dsimp only []; rw [huninit]
  refine ⟨ha_ub, ⟨_, msg, hm_step⟩, fun hrel => ?_⟩
  rw [ha_ub, hm_step] at hrel
  cases hrel

/-- **Target `f16` / `f128` real-step fail-closed theorem (`_d = copy _s as castTy`)**: when
`_s` is an initialized immediate local of a modeled `f32`/`f64`/integer type matching `kind` and
`castTy` is `f16` or `f128`, BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri`
(`.error (.unsupported msg)`) fail closed! -/
theorem step_cast_f16_f128_target_copy_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_kind : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcDecl.ty = some t) ∨
      ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcDecl.ty = some f))
    (hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {sc : MirAst.ScalarInt} (hinit : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have hsrc_scalar : IsFloatCastScalarTy srcDecl.ty := by
    rcases hsrc_kind with ⟨_, t, ht⟩ | ⟨_, f, hfmt⟩
    · exact Or.inr ⟨t, ht⟩
    · exact Or.inl ⟨f, hfmt⟩
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz, hms⟩
  · rw [hss, hinit] at hslot_s; cases hslot_s
  · rw [hss, hinit] at hslot_s; cases hslot_s
  · rw [hss, hinit] at hslot_s; cases hslot_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).2
      hk hsrc_kind hrel hsz hf
    rw [← hdst_enc] at hcast_err
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
      chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by
        cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]
      unfold evalFloatCastRvalue evalOperand readProjectedValue
      dsimp only []; rw [hinit]; dsimp only []
      rw [operandTy_copy_local hdecl_src,
        (evalFloatCast_f16_f128_none kind srcDecl.ty body.layouts (.scalar sc) hf).2]
    exact ⟨ha_unsup, _, msg,
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **Source-vs-target evaluation-order contrast on uninitialized `_s` (`_d = copy _s as f16/f128`)**:
unlike `step_cast_f16_f128_uninit_source_divergence` (where an uninitialized `f16`/`f128` **source**
diverges because `Cast.cast` checks `h.typeInfo choice source.layout.ty` before reading), when the
**source** `_s` has a modeled `f32`/`f64`/integer type (`IsFloatCastScalarTy srcDecl.ty`) and the
**target** `castTy` is `f16` or `f128`, `Cast.cast` calls `h.readImmediate choice source`
(`annealReadImmediate`) **before** `h.typeInfo choice target.ty` across all three cast kinds
(`.floatToFloat`, `.floatToInt`, `.intToFloat`), so **both** machines report UB and
`StepRelLM3_1.ub` **holds**! -/
theorem step_cast_f16_f128_uninit_target_ub_lockstep
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_scalar : IsFloatCastScalarTy srcDecl.ty)
    (_hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (huninit : get? s.frame.locals srcIdx = some .uninit)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s = MirStepNode.fail .ub ∧
      StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have hdst_ty_id : (translateTy castTy body.layouts).ty = encodeTyId castTy := rfl
  rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨_, _, hss, _⟩
  · rw [hss, huninit] at hslot_s; cases hslot_s
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hcast_ub : Miri.Interpreter.Cast.cast
        (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
        ⟨.immediate .uninit, translateTy srcDecl.ty body.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ =
        throw (.undefinedBehavior "read of uninitialized local") := by
      rw [hdst_enc]
      rcases hsrc_scalar with ⟨f, hfmt⟩ | ⟨t, ht⟩
      · rw [translateTy_of_ieeeFormatOfTy? hfmt body.layouts]
        cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
        · unfold Miri.Interpreter.Cast.cast
          simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
            castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
            annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
      · rw [translateTy_of_floatIntTargetOfTy? ht body.layouts]
        cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
        · unfold Miri.Interpreter.Cast.cast
          simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
            castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
            annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
      chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ub]; rfl
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [huninit]
    refine ⟨ha_ub, ?_⟩
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · rw [hss, huninit] at hslot_s; cases hslot_s

/-- **Constant-operand `f16` / `f128` real-step fail-closed theorem (`_d = const c as castTy`)**:
whenever either `c.ty` is `f16` / `f128` or `c.ty` is a modeled float/integer scalar matching `kind`
and `castTy` is `f16` / `f128`, `evalMirConstImmediate` evaluates `c` (because `layoutOfEncodedTyId`
handles `TyId` `30`/`33` as well as all modeled scalar `TyId`s), and BOTH Anneal
(`MirStepNode.unsupported`) and `lean-miri` (`.error (.unsupported msg)`) fail closed! -/
theorem step_cast_f16_f128_constant_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hboundary : (c.ty.kind = .float .f16 ∨ c.ty.kind = .float .f128) ∨
      (((kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? c.ty = some t) ∨
        ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? c.ty = some f)) ∧
        (castTy.kind = .float .f16 ∨ castTy.kind = .float .f128))) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hlay_c : layoutOfEncodedTyId (encodeTyId c.ty) body.layouts = translateTy c.ty body.layouts := by
    rcases hboundary with (hf | hf) | ⟨(⟨_, t, ht⟩ | ⟨_, f, hfmt⟩), _⟩
    · cases hty : c.ty; rw [hty] at hf; dsimp only at hf; subst hf; rfl
    · cases hty : c.ty; rw [hty] at hf; dsimp only at hf; subst hf; rfl
    · exact layoutOfEncodedTyId_floatCastScalar (Or.inr ⟨t, ht⟩) body.layouts
    · exact layoutOfEncodedTyId_floatCastScalar (Or.inl ⟨f, hfmt⟩) body.layouts
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
        Bool.false_eq_true, ↓reduceIte, htry, hlay_c]
  have hcast_both : ∃ msg,
      Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } =
      .error (.unsupported msg) { m with stack := ⟨#[tfa]⟩ } := by
    rw [hdst_enc]
    rcases hboundary with hf_src | ⟨hsrc_kind, hf_dst⟩
    · exact (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }).1 hk hf_src _
    · exact (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }).2
        hk hsrc_kind hrel hlaysz hf_dst
  obtain ⟨msg, hcast_err⟩ := hcast_both
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.constant c) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfa]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.constant c) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.constant c) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    rcases hboundary with hf_src | ⟨_, hf_dst⟩
    · rw [(evalFloatCast_f16_f128_none kind castTy body.layouts (.scalar sc) hf_src).1]
    · rw [(evalFloatCast_f16_f128_none kind c.ty body.layouts (.scalar sc) hf_dst).2]
  exact ⟨ha_unsup, _, msg,
    miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **Move-operand source `f16` / `f128` 3-way step boundary (`_d = move _s as castTy`)**:
complete trichotomy over the `LocalSlot` state of an `f16` / `f128` source `_s`:
1. `.init v`: BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri` (`.error (.unsupported msg)`)
   fail closed;
2. `.uninit`: Anneal reports UB (`MirStepNode.fail .ub`) whereas `lean-miri` deinitializes `_s` and
   checks `Cast.cast` source `typeInfo` before `readImmediate`, failing closed with
   `.error (.unsupported msg)` (`¬ StepRelLM3_1`);
3. `.dead`: `annealEvalOperand_move_dead` fires *before* `Cast.cast`, so BOTH Anneal and `lean-miri`
   report UB in lockstep (`StepRelLM3_1.ub`)! -/
theorem step_cast_f16_f128_move_source_boundary
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts) :
    ((∃ v, get? s.frame.locals srcIdx = some (.init v) ∧ valueContainsUninit v = false) →
      stepMirFn body s = MirStepNode.unsupported ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
    (get? s.frame.locals srcIdx = some .uninit →
      stepMirFn body s = MirStepNode.fail .ub ∧
        (∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
        ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) ∧
    (get? s.frame.locals srcIdx = some .dead →
      stepMirFn body s = MirStepNode.fail .ub ∧
        StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.move ⟨srcIdx, .nil⟩) castTy span m
  refine ⟨fun ⟨v, hinit, hno_uninit⟩ => ?_, fun huninit => ?_, fun hdead => ?_⟩
  · rw [hinit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
        | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
    obtain ⟨opVal, hms_live⟩ := hlive_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity)
      { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).1 hk hf opVal
    rw [← hdst_enc] at hcast_err
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit)
    have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand readProjectedValue
      dsimp only []; rw [hinit]; dsimp only []; rw [hno_uninit, set?_eq_some_set hlt_af_s]; dsimp only []
      rw [operandTy_move_local hdecl_src,
        (evalFloatCast_f16_f128_none kind castTy body.layouts v hf).1]
    exact ⟨ha_unsup, _, msg,
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
  · rw [huninit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
        | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
    obtain ⟨opVal, hms_live⟩ := hlive_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity)
      { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).1 hk hf opVal
    rw [← hdst_enc] at hcast_err
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      hm_err
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [huninit]
    refine ⟨ha_ub, ⟨_, msg, hm_step⟩, fun hrel => ?_⟩
    rw [ha_ub, hm_step] at hrel
    cases hrel
  · rw [hdead] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hdead_s : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨hs, _⟩ | ⟨_, hs, _⟩ <;> cases hs
        | indirect _ _ _ _ hnd _ => exact absurd rfl hnd
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hdead_s; subst hdead_s; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [hdead]
    refine ⟨ha_ub, ?_⟩
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _

/-- **Move-operand target `f16` / `f128` step boundary (`_d = move _s as f16/f128`)**: on an
immediate modeled `f32`/`f64`/integer source `_s` matching `kind` and target `f16` / `f128`,
1. when `_s` holds an initialized scalar, BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri`
   (`.error (.unsupported msg)`) fail closed;
2. when `_s` is `.uninit` or `.dead`, BOTH Anneal (`MirStepNode.fail .ub`) and `lean-miri` report
   UB in lockstep (`StepRelLM3_1.ub`) because `Cast.cast` reads the source immediate *before*
   consulting `h.typeInfo choice target.ty`! -/
theorem step_cast_f16_f128_move_target_boundary
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_kind : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcDecl.ty = some t) ∨
      ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcDecl.ty = some f))
    (hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    ((∃ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc))) →
      stepMirFn body s = MirStepNode.unsupported ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
    ((get? s.frame.locals srcIdx = some .uninit ∨ get? s.frame.locals srcIdx = some .dead) →
      stepMirFn body s = MirStepNode.fail .ub ∧
        StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have hsrc_scalar : IsFloatCastScalarTy srcDecl.ty := by
    rcases hsrc_kind with ⟨_, t, ht⟩ | ⟨_, f, hfmt⟩
    · exact Or.inr ⟨t, ht⟩
    · exact Or.inl ⟨f, hfmt⟩
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hdst_ty_id : (translateTy castTy body.layouts).ty = encodeTyId castTy := rfl
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.move ⟨srcIdx, .nil⟩) castTy span m
  have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
      body.localDecls body.layouts =
      evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
        body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
  refine ⟨fun ⟨sc, hinit⟩ => ?_, fun hbad => ?_⟩
  · rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
      ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz, hms⟩
    · rw [hss, hinit] at hslot_s; cases hslot_s
    · rw [hss, hinit] at hslot_s; cases hslot_s
    · rw [hss, hinit] at hslot_s; cases hslot_s
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity)
        { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).2
        hk hsrc_kind hrel hsz hf
      rw [← hdst_enc] at hcast_err
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.unsupported msg)) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
      obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
        (by rw [← get?_eq_getElem?]; exact hinit)
      have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand readProjectedValue valueContainsUninit
        dsimp only []; rw [hinit, set?_eq_some_set hlt_af_s]; dsimp only []
        rw [operandTy_move_local hdecl_src,
          (evalFloatCast_f16_f128_none kind srcDecl.ty body.layouts (.scalar sc) hf).2]
      exact ⟨ha_unsup, _, msg,
        miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
  · rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
      ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨_, _, hss, _⟩
    · subst hss
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
        dsimp only []; rw [hslot_s]
      refine ⟨ha_ub, ?_⟩
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · subst hss
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hcast_ub : Miri.Interpreter.Cast.cast
          (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.immediate .uninit, translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ =
          throw (.undefinedBehavior "read of uninitialized local") := by
        rw [hdst_enc]
        rcases hsrc_scalar with ⟨f, hfmt⟩ | ⟨t, ht⟩
        · rw [translateTy_of_ieeeFormatOfTy? hfmt body.layouts]
          cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
          · unfold Miri.Interpreter.Cast.cast
            simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
              castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
              annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
        · rw [translateTy_of_floatIntTargetOfTy? ht body.layouts]
          cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
          · unfold Miri.Interpreter.Cast.cast
            simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
              castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
              annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ub]; rfl
      have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
        dsimp only []; rw [hslot_s]
      refine ⟨ha_ub, ?_⟩
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · rw [hss] at hslot_s
      rcases hbad with hun | hd
      · rw [hun] at hslot_s; cases hslot_s
      · rw [hd] at hslot_s; cases hslot_s

end LeanMiriSpec.Correspondence
