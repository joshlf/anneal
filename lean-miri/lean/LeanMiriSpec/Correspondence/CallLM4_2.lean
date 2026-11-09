/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.IntrinsicLM4_2
import LeanMiriSpec.Correspondence.NumericLM4_2

/-!
# Intrinsic Call Infrastructure for `LM-4.2`

Generic one-step correspondence lemmas for translated `TerminatorKind.call`s of
`AnnealIntrinsic`s between Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step` (under `annealStepHooks`), from
`StateRelLM3_1`-related states:

* operand evaluation before the immediate read (`annealEvalOperand_scalar_lm3_1`),
  writing a scalar result and returning to the call's target
  (`StateRelLM3_1.write_scalar_return`);
* one-step simulation of one- and two-argument intrinsic calls, parameterized by
  the intrinsic's own evaluation on both sides
  (`step_intrinsic_call_one_simulation`, `step_intrinsic_call_two_simulation`);
* the vendored dispatcher's handling of `rotate_left` / `rotate_right`
  (`intrinsics_eval_rotateLeft`, `intrinsics_eval_rotateRight`) and the
  resulting `lean-miri` step on intrinsics it leaves to their MIR fallback body
  (`step_intrinsic_call_two_unhandled`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Frame bookkeeping -/

/-- `StateRelLM3_1` survives advancing both machines to the next statement when
neither the locals of either machine nor Anneal's memory change. -/
theorem StateRelLM3_1.advance_same
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    StateRelLM3_1 body (advanceStmt s s.frame.locals)
      { m with stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace hfr.advance hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    exact halloc.local_alloc_sync tf hframes e he
  · intro i j mi mj li lj hne hi hj
    exact hdisj i j mi mj li lj hne hi hj

/-! ## 2. Call infrastructure -/

/-- `StateRelLM3_1` survives moving both machines to the same new location. -/
theorem StateRelLM3_1.relocate
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (b i : Nat) :
    StateRelLM3_1 body { s with frame := { s.frame with blockIdx := b, stmtIdx := i } }
      { m with stack := ⟨#[{ tf with location := .mir ⟨b, i⟩ }]⟩ } allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace
    ⟨hfr.body_eq, rfl, hfr.af_locals_len, hfr.mf_locals_size, hfr.locals_rel⟩
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    exact halloc.local_alloc_sync tf hframes e he
  · intro i j mi mj li lj hne hi hj
    exact hdisj i j mi mj li lj hne hi hj

/-- `annealReturnToBlock (some b)` moves the single frame to statement `0` of
block `b`. -/
theorem annealReturnToBlock_some {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (b : Nat) :
    annealReturnToBlock (some b) m =
      .ok () { m with stack := ⟨#[{ tf with location := .mir ⟨b, 0⟩ }]⟩ } := by
  unfold annealReturnToBlock Miri.Interpreter.ControlFlow.returnToBlock
    Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
  rw [stack_currentFrame?_singleton m.stack tf hframes, hframes]
  rfl

/-- The callee constant of a translated intrinsic call evaluates without
changing a single-frame state. -/
theorem annealEvalOperand_fnItemConst_ok (ld : List LocalDecl) (ly : LayoutTable)
    (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none m =
      .ok ⟨.immediate .uninit, layoutOfEncodedTyId (annealFnItemTyId k argTy) ly⟩ m := by
  rw [annealEvalOperand_fnItemConst]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some, Bool.false_eq_true,
    ↓reduceIte, pure, EStateM.pure]

/-- **Operand evaluation without the immediate read.** `annealEvalOperand` on a
well-typed primitive scalar operand, from `StateRelLM3_1`-related states, as in
`evalOperand_scalar_lm3_1_simulation` but before `annealReadImmediate`: a dead
local fails in both machines, an uninitialized local fails in Anneal and
evaluates to `Immediate.uninit` in `lean-miri` (whose later read fails), and an
initialized local or constant evaluates to related scalars. Only the layout
cache of the frame changes. -/
theorem annealEvalOperand_scalar_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty) :
    (∃ m' msg,
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok ⟨.immediate .uninit, translateTy ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ sc msc tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hsame : { m with stack := ⟨#[tf]⟩ } = m := stepState_with_same_singleton m tf hframes
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a :
        evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand
      dsimp only
      rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    right; right
    refine ⟨sc, msc, tf, heval_a, ?_, by rw [hsame]; exact hstate,
      .scalar sc msc hrel hlaysz hbool hchar, fun _ => rfl⟩
    rw [hsame]; exact heval_m
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hcache := hloc.cachedLayout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    have hvals : ∀ k : Nat,
        ((cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)).locals[k]?).map
          Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value := by
      intro k
      simp only [cacheFrameLocalLayout]
      by_cases hki : idx = k
      · subst hki
        rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
        rfl
      · rw [Array.getElem?_set_ne _ hki]
    cases hloc with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso
      rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
      | dead _ _ =>
        left
        refine ⟨{ m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt_mf
            (translateTy decl.ty body.layouts)]⟩ }, "read of dead local", ?_, ?_⟩
        · simp [evalOperand, hslot]
        · rw [htr]
          exact annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache
      | immediate _ imm _ _ hval =>
        have hstate' := hstate.cache_layout hframes hdecl hlt_mf
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · right; left
          refine ⟨_, ?_, ?_, hstate', hvals⟩
          · simp [evalOperand, hslot]
          · rw [htr]
            exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz_sc, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar hprim
          right; right
          refine ⟨sc, msc, _, ?_, ?_, hstate', .scalar sc msc hrel hsz_sc hbool hchar, hvals⟩
          · simp [evalOperand, readProjectedValue, hslot]
          · rw [htr]
            exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache

/-- Immediacy of a frame local depends only on the local values. -/
theorem IsImmediateFrameLocal.of_values_eq
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hvals : ∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
      (tf.locals[k]?).map Miri.Interpreter.LocalState.value)
    {j : Nat} (h : IsImmediateFrameLocal tf j) : IsImmediateFrameLocal tf' j := by
  intro mls hmls mp hmp
  have hv := hvals j
  rw [hmls] at hv
  cases hj : tf.locals[j]? with
  | none => rw [hj] at hv; cases hv
  | some mls₀ =>
    rw [hj] at hv
    injection hv with hv'
    exact h mls₀ hj mp (hv'.symm.trans hmp)

/-- **Write an intrinsic's scalar result and return to the call's target.**
From `StateRelLM3_1`-related states, writing the related scalars `r` / `mr` to
an immediate primitive-scalar destination local and moving to statement `0` of
`targetBb` either fails in both machines (dead destination) or succeeds in both
with `StateRelLM3_1`-related results. -/
theorem StateRelLM3_1.write_scalar_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hprim : IsPrimScalarTy dstDecl.ty)
    (himm : IsImmediateFrameLocal tf dstIdx)
    {r : MirAst.ScalarInt} {mr : Miri.Memory.ScalarInt}
    (hrelI : ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)))
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    (∃ msg m', writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) = .ub ∧
        (do
          annealWriteImmediate (.scalar (.fromScalarInt mr)) ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .error (.undefinedBehavior msg) m') ∨
    (∃ locals' tf',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) = .ok locals' ∧
        (do
          annealWriteImmediate (.scalar (.fromScalarInt mr)) ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .ok true { m with stack := ⟨#[tf']⟩ } ∧
        tf'.location = .mir ⟨targetBb, 0⟩ ∧
        StateRelLM3_1 body
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }
          { m with stack := ⟨#[tf']⟩ } allocMap) := by
  obtain ⟨tf₀, hframes₀, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have himm' := himm mls hmls
  have hget : tf.getLocal dstIdx = .ok mls := frame_getLocal_of_getElem? tf dstIdx mls hmls
  cases hloc with
  | rawPtr _ _ _ _ _ _ hty_raw _ =>
    exfalso
    rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
    | dead lay _ =>
      left
      refine ⟨"write to dead local", m, ?_, ?_⟩
      · simp [writePlaceValue, hslot]
      · rw [EStateM.bind_eq_error (annealWriteImmediate_dead hframes hget)]
    | immediate _ oldImm lay hlay hval =>
      have hne_dead : slot ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> nofun
      have hnot_dst := StateRelLM3_1.immediate_not_in_allocMap hstate hframes hslot hne_dead himm
      have hwrite_a : writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) =
          .ok (s.frame.locals.set dstIdx (.init (.scalar r))) := by
        have hset : set? s.frame.locals dstIdx (.init (.scalar r)) =
            some (s.frame.locals.set dstIdx (.init (.scalar r))) := set?_eq_some_set hlt_af _
        unfold writePlaceValue
        dsimp only
        rw [hslot, hset]
        cases slot with
        | dead => exact absurd rfl hne_dead
        | uninit => rfl
        | init _ => rfl
      let tfw : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { tf with
          locals := tf.locals.set dstIdx
            { tf.locals[dstIdx]'hlt_mf with value := .live (.immediate (.scalar (.fromScalarInt mr))) }
            hlt_mf }
      have hwrite_m := annealWriteImmediate_live (val := .scalar (.fromScalarInt mr))
        (id0 := id0) (dstLay := dstLay) hframes hlt_mf hget
      have hret := annealReturnToBlock_some (m := { m with stack := ⟨#[tfw]⟩ }) (tf := tfw) rfl
        targetBb
      right
      refine ⟨_, { tfw with location := .mir ⟨targetBb, 0⟩ }, hwrite_a, ?_, rfl, ?_⟩
      · rw [EStateM.bind_eq_ok hwrite_m, EStateM.bind_eq_ok hret]
        rfl
      · have hnew : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
            (.init (.scalar r))
            { tf.locals[dstIdx]'hlt_mf with
              value := .live (.immediate (.scalar (.fromScalarInt mr))) } := by
          rw [List.map_id]
          rw [hmls_eq]
          exact .base (.immediate _ _ lay hlay (Or.inr ⟨_, rfl, hrelI⟩))
        have hadv := StateRelLM3_1.advance_write_immediate_perm_map hstate hframes id
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hdecl hnot_dst
          (hlt_d := hlt_mf) (oldImm := oldImm) (by rw [hmls_eq]) hnew
          (mem' := s.memory) hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
        rw [List.map_id] at hadv
        exact hadv.relocate rfl targetBb 0

/-- `translateCalleeOperand` recognizes every `AnnealIntrinsic` by its
canonical `DefPath`. -/
theorem AnnealIntrinsic.ofDefPath?_defPath (k : AnnealIntrinsic) :
    AnnealIntrinsic.ofDefPath? k.defPath = some k := by
  cases k <;> rfl

/-- A well-typed scalar operand translates to a non-`Move` operand. -/
theorem WellTypedScalarOperand.translate_ne_move {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty} (h : WellTypedScalarOperand body tf op ty) :
    ∀ p, translateOperand op ≠ .Move p := by
  intro p hp
  cases h with
  | constScalar c _ _ _ _ _ _ _ _ =>
    simp only [translateOperand, reduceCtorEq] at hp
  | copyLocal idx _ _ _ _ =>
    simp only [translateOperand, reduceCtorEq] at hp

/-- The translation of a call of intrinsic `k` with generic argument `argKind`,
a root-local destination, and a target. -/
theorem translateTerminator_intrinsic_call
    {term : Terminator} {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind]) :
    translateTerminator term =
      { sourceInfo := defaultSourceInfo
        kind := .Call
          (.Constant (annealFnItemConst k (encodeTyId { kind := argKind, layoutIdx := 0 })))
          (args.map fun a =>
            ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
          ⟨dstIdx, #[]⟩ (some targetBb) (translateUnwindAction unwind) .Normal
          defaultSpanRef } := by
  unfold translateTerminator
  rw [hterm]
  simp only [translateTerminatorKind, translateCalleeOperand, hc,
    AnnealIntrinsic.ofDefPath?_defPath]
  rfl

/-- The location check of `Call.evalCallTerminator` and
`ControlFlow.evalTerminator` passes when the call moves to another location. -/
theorem frameLocation_beq_false {b i b' : Nat} (h : b' ≠ b ∨ i ≠ 0) :
    (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩ == .mir ⟨b, i⟩) = false := by
  cases hb : (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩ == .mir ⟨b, i⟩) with
  | false => rfl
  | true =>
    have heq := beq_iff_eq.mp hb
    injection heq with heq'
    injection heq' with h₁ h₂
    rcases h with h | h
    · exact absurd h₁ h
    · exact absurd h₂.symm h

/-- The location check of `ControlFlow.evalTerminator` passes when the call
moves to another location. -/
theorem option_frameLocation_beq_false {b i b' : Nat} (h : b' ≠ b ∨ i ≠ 0) :
    (some (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩) ==
      some (Miri.Interpreter.FrameLocation.mir ⟨b, i⟩)) = false := by
  cases hb : (some (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩) ==
      some (Miri.Interpreter.FrameLocation.mir ⟨b, i⟩)) with
  | false => rfl
  | true =>
    have heq := beq_iff_eq.mp hb
    injection heq with heq'
    injection heq' with heq''
    injection heq'' with h₁ h₂
    rcases h with h | h
    · exact absurd h₁ h
    · exact absurd h₂.symm h

/-- **One real step of a translated two-argument intrinsic call.** From
`StateRelLM3_1`-related states at a `TerminatorKind.call` of `AnnealIntrinsic`
`k` (whose arity is `2`) with well-typed primitive scalar arguments, an
immediate primitive-scalar root-local destination, and a target that moves the
frame, both machines take related steps, provided that:

* `hanneal`: Anneal evaluates the call by evaluating the arguments and then
  `annealCall` on their values;
* `hmiri_uninit₁` / `hmiri_uninit₂`: `Intrinsics.eval` reports undefined
  behavior on an uninitialized first argument, or on an uninitialized second
  argument after an initialized first one;
* `hsim`: on related initialized arguments, `annealCall` and `Intrinsics.eval`
  either both report undefined behavior, or both write related scalar results
  to the destination and return to the target.

Uninitialized and dead arguments and a dead destination are undefined behavior
in both machines. -/
theorem step_intrinsic_call_two_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} (hk : k.arity = 2) {argKind : RigidTy}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ty₁ ty₂ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstPrim : IsPrimScalarTy dstDecl.ty)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (annealCall : List Value → List LocalSlot → MirStepNode)
    (hanneal : evalTerminator s bb.terminator (some body) =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' => annealCall vs locals'
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported)
    (hmiri_uninit₁ : ∀ (v₂ : Miri.Interpreter.OpTy AnnealProv)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState), ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate .uninit, translateTy ty₁ body.layouts⟩, v₂] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hmiri_uninit₂ : ∀ (msc₁ : Miri.Memory.ScalarInt)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState), ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
          ⟨.immediate .uninit, translateTy ty₂ body.layouts⟩] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hsim : ∀ (sc₁ sc₂ : MirAst.ScalarInt) (msc₁ msc₂ : Miri.Memory.ScalarInt),
      ImmediateRel ty₁ body.layouts (.scalar sc₁) (.scalar (.fromScalarInt msc₁)) →
      ImmediateRel ty₂ body.layouts (.scalar sc₂) (.scalar (.fromScalarInt msc₂)) →
      ∀ (id0 : Miri.Interpreter.LocalsIdentity) (m' : AnnealStepState),
        (annealCall [.scalar sc₁, .scalar sc₂] s.frame.locals = MirStepNode.fail .ub ∧
          ∃ msg, Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            .error (.undefinedBehavior msg) m') ∨
        (∃ r mr,
          ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)) ∧
          annealCall [.scalar sc₁, .scalar sc₂] s.frame.locals =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb (.scalar r) ∧
          Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            (do
              annealWriteImmediate (.scalar (.fromScalarInt mr))
                ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩
              annealReturnToBlock (some targetBb)
              pure true) m')) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [hanneal, miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_two _ _ k _ hk _ _ ((hop₁ tf hframes).translate_ne_move)
      ((hop₂ tf hframes).translate_ne_move)]
  -- Destination place and callee.
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  -- First argument.
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, hstate₂, hvals₂⟩ | ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, hrel₁, hvals₂⟩
  · rw [EStateM.bind_eq_error hm₁]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, _, hm₂⟩ | ⟨tf₃, _, hm₂, _, _⟩ | ⟨sc₂, msc₂, tf₃, _, hm₂, _, _, _⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₁ ⟨.immediate .uninit, translateTy ty₂ body.layouts⟩
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₁
        ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, _, _⟩ |
        ⟨sc₂, msc₂, tf₃, ha₂, hm₂, hstate₃, hrel₂, hvals₃⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₂ msc₁
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hevals : evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok [.scalar sc₁, .scalar sc₂] s.frame.locals := by
        simp only [evalOperands, ha₁, ha₂]
      simp only [hevals]
      rcases hsim sc₁ sc₂ msc₁ msc₂ hrel₁ hrel₂ tf.localsIdentity
          { m with stack := ⟨#[tf₃]⟩ } with
        ⟨ha, msg, hev⟩ | ⟨r, mr, hrelR, ha, hev⟩
      · rw [EStateM.bind_eq_error hev, ha]
        exact .ub _ _
      · have himm₃ : IsImmediateFrameLocal tf₃ dstIdx :=
          IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ dstIdx (hdstImm tf hframes))
        rcases StateRelLM3_1.write_scalar_return hstate₃ rfl hdst hdstPrim himm₃ hrelR
            tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
          ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
        · rw [EStateM.bind_eq_error (hev.trans hwm), ha]
          simp only [intrinsicWriteReturn, hwa]
          exact .ub _ _
        · rw [EStateM.bind_eq_ok (hev.trans hwm), ha]
          simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
            Option.isSome_some]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq (m := { m with stack := ⟨#[tf₄]⟩ })
            (tf := tf₄) rfl)]
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
            (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
          rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
          simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
            stack_currentFrame?_singleton m.stack tf hframes, hframes,
            stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
              Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
            option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
          exact .step _ _ hstate₄
/-- **One real step of a translated one-argument intrinsic call**, as
`step_intrinsic_call_two_simulation`. -/
theorem step_intrinsic_call_one_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} (hk : k.arity = 1) {argKind : RigidTy}
    {c : ConstOperand} {op₁ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ty₁ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hprim₁ : IsPrimScalarTy ty₁)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstPrim : IsPrimScalarTy dstDecl.ty)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (annealCall : List Value → List LocalSlot → MirStepNode)
    (hanneal : evalTerminator s bb.terminator (some body) =
      match evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' => annealCall vs locals'
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported)
    (hmiri_uninit₁ : ∀ (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState),
      ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate .uninit, translateTy ty₁ body.layouts⟩] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hsim : ∀ (sc₁ : MirAst.ScalarInt) (msc₁ : Miri.Memory.ScalarInt),
      ImmediateRel ty₁ body.layouts (.scalar sc₁) (.scalar (.fromScalarInt msc₁)) →
      ∀ (id0 : Miri.Interpreter.LocalsIdentity) (m' : AnnealStepState),
        (annealCall [.scalar sc₁] s.frame.locals = MirStepNode.fail .ub ∧
          ∃ msg, Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            .error (.undefinedBehavior msg) m') ∨
        (∃ r mr,
          ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)) ∧
          annealCall [.scalar sc₁] s.frame.locals =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb (.scalar r) ∧
          Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            (do
              annealWriteImmediate (.scalar (.fromScalarInt mr))
                ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩
              annealReturnToBlock (some targetBb)
              pure true) m')) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [hanneal, miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_one _ _ k _ hk _ ((hop₁ tf hframes).translate_ne_move)]
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, _, _⟩ |
      ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, hrel₁, hvals₂⟩
  · rw [EStateM.bind_eq_error hm₁]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    obtain ⟨msg, hev⟩ := hmiri_uninit₁
      ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
      { m with stack := ⟨#[tf₂]⟩ }
    rw [EStateM.bind_eq_error hev]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have hevals : evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok [.scalar sc₁] s.frame.locals := by
      simp only [evalOperands, ha₁]
    simp only [hevals]
    rcases hsim sc₁ msc₁ hrel₁ tf.localsIdentity { m with stack := ⟨#[tf₂]⟩ } with
      ⟨ha, msg, hev⟩ | ⟨r, mr, hrelR, ha, hev⟩
    · rw [EStateM.bind_eq_error hev, ha]
      exact .ub _ _
    · have himm₂ : IsImmediateFrameLocal tf₂ dstIdx :=
        IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ dstIdx (hdstImm tf hframes))
      rcases StateRelLM3_1.write_scalar_return hstate₂ rfl hdst hdstPrim himm₂ hrelR
          tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
        ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
      · rw [EStateM.bind_eq_error (hev.trans hwm), ha]
        simp only [intrinsicWriteReturn, hwa]
        exact .ub _ _
      · rw [EStateM.bind_eq_ok (hev.trans hwm), ha]
        simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
          Option.isSome_some]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq (m := { m with stack := ⟨#[tf₄]⟩ })
          (tf := tf₄) rfl)]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
          (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
        rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
        simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, hframes,
          stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
            Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
          option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
        exact .step _ _ hstate₄

/-- Anneal's `evalTerminator` on a call of an inline `AnnealIntrinsic` other
than `exact_div` with no transparent body: evaluate the arguments, then
`evalInlineIntrinsicCall?`. -/
theorem evalTerminator_inline_intrinsic_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hcallee : findCallee? s.memory.callees k.defPath = none)
    (hk : k ≠ .exactDiv) :
    evalTerminator s term (some body) =
      match evalOperands s.frame.locals args s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match evalInlineIntrinsicCall? s k.defPath args vs locals' ⟨dstIdx, []⟩ targetBb
            body.localDecls body.layouts with
        | some node => node
        | none =>
          MirStepNode.extCall { defPath := k.defPath, args := vs, memory := s.memory }
            (resumeExternalCall s locals' ⟨dstIdx, []⟩ targetBb unwind)
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  have hne : stringEq k.defPath "core::intrinsics::exact_div" = false := by
    cases k <;> first | rfl | exact absurd rfl hk
  unfold evalTerminator
  rw [hterm]
  simp only [extractCalleeDefPath?, hc]
  cases evalOperands s.frame.locals args s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' => simp only [hcallee, hne] <;> rfl
  | ub => rfl
  | unsupported => rfl

/-- The `AnnealIntrinsic` of a one-operand integer bit intrinsic. -/
def AnnealIntrinsic.ofBit : IntegerBitIntrinsic → AnnealIntrinsic
  | .ctpop => .ctpop
  | .ctlz => .ctlz
  | .ctlzNonzero => .ctlzNonzero
  | .cttz => .cttz
  | .cttzNonzero => .cttzNonzero
  | .bswap => .bswap
  | .bitreverse => .bitreverse

theorem AnnealIntrinsic.ofBit_arity (op : IntegerBitIntrinsic) :
    (AnnealIntrinsic.ofBit op).arity = 1 := by
  cases op <;> rfl

theorem AnnealIntrinsic.ofBit_numeric (op : IntegerBitIntrinsic) :
    (AnnealIntrinsic.ofBit op).numeric? = some (toMiriIntegerIntrinsic op) := by
  cases op <;> rfl

theorem AnnealIntrinsic.ofBit_ne_exactDiv (op : IntegerBitIntrinsic) :
    AnnealIntrinsic.ofBit op ≠ .exactDiv := by
  cases op <;> nofun

theorem integerBitIntrinsicOfPath?_ofBit (op : IntegerBitIntrinsic) :
    integerBitIntrinsicOfPath? (AnnealIntrinsic.ofBit op).defPath = some op := by
  cases op <;> rfl

/-- The byte width of an integral type, as `intCastTargetBytes` reports it. -/
theorem IsIntegralTy.intCastTargetBytes_eq {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) :
    intCastTargetBytes ty.kind = some (integerKindByteWidth kind) := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]; cases it <;> rfl
  · rw [hk]; cases ut <;> rfl

/-! ## 3. `rotate_left` / `rotate_right`

`lean-miri`'s pinned dispatcher `Intrinsics.eval` has no arm for
`rotate_left` / `rotate_right`: the names are neither atomic, SIMD, numeric, nor
float intrinsics, and `annealIntrinsicHooks` provides no `mathHooks`, so
`Intrinsics.eval` returns `false` without changing the state. The call then
needs the intrinsic's MIR fallback body, which `annealCallHooks.findMirOrEvalFn`
rejects with `StepError.unsupported`.
-/

/-- `"rotate_left"` names no portable float intrinsic. -/
theorem rotateLeft_not_float :
    ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32), ("f64", .binary64),
      ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_left".endsWith suffix then
          some (("rotate_left".dropEnd suffix.length).toString, format)
        else none) = none := by
  have h16 : "rotate_left".endsWith "f16" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h32 : "rotate_left".endsWith "f32" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h64 : "rotate_left".endsWith "f64" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h128 : "rotate_left".endsWith "f128" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  simp only [List.findSome?, h16, h32, h64, h128, Bool.false_eq_true, ↓reduceIte]

/-- `Intrinsics.floatIntrinsic` does not handle `"rotate_left"`. -/
theorem floatIntrinsic_rotateLeft
    {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V)
    (choice : C) (args : Array (Miri.Interpreter.OpTy P)) (dest : V) :
    Miri.Interpreter.Intrinsics.floatIntrinsic h choice "rotate_left" args dest = pure false := by
  unfold Miri.Interpreter.Intrinsics.floatIntrinsic
  split
  · next base format hfl =>
    exfalso
    have h' := rotateLeft_not_float
    rw [show ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32),
      ("f64", .binary64), ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_left".endsWith suffix then
          some (("rotate_left".dropEnd suffix.length).toString, format)
        else none) = some (base, format) from hfl] at h'
    cases h'
  · rfl

/-- `"rotate_right"` names no portable float intrinsic. -/
theorem rotateRight_not_float :
    ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32), ("f64", .binary64),
      ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_right".endsWith suffix then
          some (("rotate_right".dropEnd suffix.length).toString, format)
        else none) = none := by
  have h16 : "rotate_right".endsWith "f16" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h32 : "rotate_right".endsWith "f32" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h64 : "rotate_right".endsWith "f64" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h128 : "rotate_right".endsWith "f128" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  simp only [List.findSome?, h16, h32, h64, h128, Bool.false_eq_true, ↓reduceIte]

/-- `Intrinsics.floatIntrinsic` does not handle `"rotate_right"`. -/
theorem floatIntrinsic_rotateRight
    {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V)
    (choice : C) (args : Array (Miri.Interpreter.OpTy P)) (dest : V) :
    Miri.Interpreter.Intrinsics.floatIntrinsic h choice "rotate_right" args dest = pure false := by
  unfold Miri.Interpreter.Intrinsics.floatIntrinsic
  split
  · next base format hfl =>
    exfalso
    have h' := rotateRight_not_float
    rw [show ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32),
      ("f64", .binary64), ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_right".endsWith suffix then
          some (("rotate_right".dropEnd suffix.length).toString, format)
        else none) = some (base, format) from hfl] at h'
    cases h'
  · rfl

/-- `Intrinsics.eval` leaves `rotate_left` to its MIR fallback body. -/
theorem intrinsics_eval_rotateLeft (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateLeft.name types args dest target = pure false := by
  have h : Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateLeft.name types args dest target =
      (do
        if !(← Miri.Interpreter.Intrinsics.floatIntrinsic (annealIntrinsicHooks ld ly) ()
            "rotate_left" args dest) then
          return false
        annealReturnToBlock target
        return true) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [h, floatIntrinsic_rotateLeft]
  rfl

/-- `Intrinsics.eval` leaves `rotate_right` to its MIR fallback body. -/
theorem intrinsics_eval_rotateRight (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateRight.name types args dest target = pure false := by
  have h : Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateRight.name types args dest target =
      (do
        if !(← Miri.Interpreter.Intrinsics.floatIntrinsic (annealIntrinsicHooks ld ly) ()
            "rotate_right" args dest) then
          return false
        annealReturnToBlock target
        return true) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [h, floatIntrinsic_rotateRight]
  rfl

/-- **`lean-miri` on a two-argument intrinsic that `Intrinsics.eval` leaves
unhandled.** From `StateRelLM3_1`-related states at a translated call of `k`
whose `Intrinsics.eval` returns `false` without changing the state, the real
`lean-miri` step reports undefined behavior for a dead argument (as Anneal's
argument evaluation does) and otherwise fails closed with
`StepError.unsupported` (the MIR fallback body is outside the fragment). It
never takes a successful step. -/
theorem step_intrinsic_call_two_unhandled
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {k : AnnealIntrinsic} (hk : k.arity = 2) {argKind : RigidTy}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    {ty₁ ty₂ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hunhandled : ∀ (args : Array (Miri.Interpreter.OpTy AnnealProv))
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }] args dest (some targetBb) m' =
        .ok false m') :
    (∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported msg))) ∨
    (∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) ∧
      evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_two _ _ k _ hk _ _ ((hop₁ tf hframes).translate_ne_move)
      ((hop₂ tf hframes).translate_ne_move)]
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  have hfinish : ∀ (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (m₃ : AnnealStepState),
      ∃ msg, (do
        let handled ← Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) () k.name
          #[encodeTyId { kind := argKind, layoutIdx := 0 }] #[v₁, v₂]
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          (some targetBb)
        if handled then pure ()
        else (annealUnsupportedLeaf
          "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
        if (some targetBb).isSome then
          if (← (annealPlaceHooks body.localDecls body.layouts).frameIndex) == 0 then
            if (← (annealPlaceHooks body.localDecls body.layouts).getFrame).location ==
                tf.location then
              throw (Miri.Interpreter.StepError.invalidProgram
                "evaluating this call made no progress")) m₃ =
        .error (.unsupported msg) m₃ := by
    intro v₁ v₂ m₃
    rw [EStateM.bind_eq_ok (hunhandled _ _ m₃)]
    exact ⟨_, rfl⟩
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, hstate₂, hvals₂⟩ |
      ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, _, hvals₂⟩
  · right
    refine ⟨m₂, msg, ?_, by simp only [evalOperands, ha₁]⟩
    rw [EStateM.bind_eq_error hm₁]
    rfl
  all_goals
    rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, _, hm₂, _, _⟩ | ⟨sc₂, msc₂, tf₃, _, hm₂, _, _, _⟩
    · right
      refine ⟨m₃, msg, ?_, by simp only [evalOperands, ha₁, ha₂]⟩
      rw [EStateM.bind_eq_error hm₂]
      rfl
    all_goals
      rw [EStateM.bind_eq_ok hm₂]
      left
      obtain ⟨msg, hfin⟩ := hfinish _ _ { m with stack := ⟨#[tf₃]⟩ }
      refine ⟨{ m with stack := ⟨#[tf₃]⟩ }, msg, ?_⟩
      rw [hfin]
      rfl

/-- Anneal's evaluation of two well-typed primitive scalar arguments from
`StateRelLM3_1`-related states: undefined behavior, or two scalars related to
`lean-miri` immediates of their types (and unchanged locals). -/
theorem evalOperands_two_scalar_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op₁ op₂ : MirAst.Operand} {ty₁ ty₂ : Ty}
    (hop₁ : WellTypedScalarOperand body tf op₁ ty₁) (hop₂ : WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂) :
    evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∨
    ∃ a b ma mb, evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok [.scalar a, .scalar b] s.frame.locals ∧
      ImmediateRel ty₁ body.layouts (.scalar a) (.scalar (.fromScalarInt ma)) ∧
      ImmediateRel ty₂ body.layouts (.scalar b) (.scalar (.fromScalarInt mb)) := by
  rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop₁ hprim₁ with
    ⟨_, _, ha₁, _⟩ | ⟨_, ha₁, _⟩ | ⟨a, ma, _, ha₁, _, _, hrel₁, _⟩
  · left; simp only [evalOperands, ha₁]
  · left; simp only [evalOperands, ha₁]
  · rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop₂ hprim₂ with
      ⟨_, _, ha₂, _⟩ | ⟨_, ha₂, _⟩ | ⟨b, mb, _, ha₂, _, _, hrel₂, _⟩
    · left; simp only [evalOperands, ha₁, ha₂]
    · left; simp only [evalOperands, ha₁, ha₂]
    · right
      exact ⟨a, b, ma, mb, by simp only [evalOperands, ha₁, ha₂], hrel₁, hrel₂⟩

/-- The size of an Anneal scalar related to an immediate of an integral type is
that type's byte width. -/
theorem ImmediateRel.integral_sizeBytes {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind) {layouts : LayoutTable} {a : MirAst.ScalarInt}
    {ma : Miri.Memory.ScalarInt}
    (h : ImmediateRel ty layouts (.scalar a) (.scalar (.fromScalarInt ma))) :
    a.sizeBytes = integerKindByteWidth kind := by
  cases h with
  | scalar _ _ hrel hsz _ _ =>
    have hvalid : ValidScalarBytes (integerKindByteWidth kind) := by
      unfold ValidScalarBytes; cases kind <;> simp [integerKindByteWidth]
    exact translateSizeBytes_inj hrel.validBytes hvalid (hsz.symm.trans (hint.size_eq layouts))

end LeanMiriSpec.Correspondence
