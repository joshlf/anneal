/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.Correspondence.MiriDiffWitnessesPart2

/-!
# `LM-4.3`: `miri-diff` Formal Witness Suite (Final Part)

Continuation of `MiriDiffWitnessesPart1` and `MiriDiffWitnessesPart2` in the
`LeanMiriSpec.Correspondence.MiriDiffWitnesses` namespace.
-/

namespace LeanMiriSpec.Correspondence.MiriDiffWitnesses

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.Correspondence.Safety

local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

local elab "kernel_decide" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let inst ← Lean.Meta.synthInstance (Lean.mkApp (Lean.mkConst ``Decidable) tgt)
  let decExpr := Lean.mkApp2 (Lean.mkConst ``decide) tgt inst
  let eqProof := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) decExpr
  mvarId.assign (Lean.mkApp3 (Lean.mkConst ``of_decide_eq_true) tgt inst eqProof)
  Lean.Elab.Tactic.replaceMainGoal []

/-! ### Checked addition: whole-program safety equivalence for the checked-addition witness
`checkedAddBody rhs` (for every `rhs < 65536`) through a body-specific
`StepClosedSim`: the closed invariant `ScalarFragmentInv` is strengthened with
the shape of the `(u16, bool)` local `_1` at the two program points that read
its fields. -/

/-! ### Reading a field of an immediate scalar pair -/

/-- Reading field `0` or `1` of an immediate scalar-pair local (with any cached
layout consistent with its declaration): Anneal returns the component and leaves
the locals unchanged; `lean-miri` returns the matching scalar after caching the
local's layout. -/
theorem pairField_read_simulation
    {body : CapturedMir} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {idx : Local} {decl : LocalDecl}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine af topFrame)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl : get? body.localDecls idx = some decl)
    (sc0 sc1 : MirAst.ScalarInt) (msc0 msc1 : Miri.Memory.ScalarInt)
    (hls : get? af.locals idx = some (LocalSlot.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
    {cl : Option Miri.Interpreter.LocalLayout}
    (hloc : topFrame.locals[idx]? = some
      ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
         layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (hcl : ∀ l ∈ cl, l = translateTy decl.ty body.layouts)
    (fidx : Nat) (fty : Ty)
    (hfidx : (fidx = 0 ∧ sc0.sizeBytes ≠ 0) ∨ (fidx = 1 ∧ sc1.sizeBytes ≠ 0))
    (hfty : fty = if fidx = 0 then
      { kind := (match decl.ty.kind with | .tuple (t::_) => t | _ => .tuple []), layoutIdx := 0 }
      else { kind := .bool, layoutIdx := 0 }) :
    let op := Operand.copy ⟨idx, [ProjectionElem.field fidx fty]⟩
    evalOperand af.locals op [] globals body.layouts =
      .ok (.scalar (if fidx = 0 then sc0 else sc1)) af.locals ∧
    ∃ hlt : idx < topFrame.locals.size,
      let topFrame' := cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      FrameRel body m.machine af topFrame' ∧
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m) =
        EStateM.Result.ok
          { imm := .scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1)),
            layout := ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩ }
          { m with stack := ⟨#[topFrame']⟩ } := by
  intro op
  obtain ⟨hlt, h_get⟩ := array_get_some_exists _ _ _ hloc
  have hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    intro l' hl'
    rw [h_get] at hl'
    exact hcl l' hl'
  constructor
  · dsimp only [op, evalOperand]
    rw [hls]
    dsimp only [readProjectedValue, List.brecOn, List.below]
    rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rfl
    · rfl
  · refine ⟨hlt, ?_, ?_, ?_⟩
    · intro j hj
      exact hj.cache_layout hlt _
    · exact hframe.cache_local_layout hdecl hlt
    · have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache
      have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
      rw [h_get] at hget_c
      have hgop := frame_getLocalOperand_live _ hget_c
      have hm_op : annealEvalOperand body.localDecls body.layouts (translateOperand op) known m =
          .ok ⟨.immediate (.scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1))),
            ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩⟩
            { m with stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
              (translateTy decl.ty body.layouts)]⟩ } := by
        with_unfolding_all
          unfold annealEvalOperand
          rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map,
              encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
              EStateM.get, Bind.bind, EStateM.bind, Pure.pure,
              stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres,
              hgop, beq_self_eq_true]
            rfl
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map,
              encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
              EStateM.get, Bind.bind, EStateM.bind, Pure.pure,
              stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres,
              hgop]
            rfl
      rw [EStateM.bind_eq_ok hm_op]
      unfold annealReadImmediate
      rfl

/-- `readAssertCondition` on an operand whose immediate read yields a `bool`
scalar returns the scalar's truth value. -/
theorem readAssertCondition_of_read
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Miri.MIR.Operand} {m m' : AnnealStepState}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {lay : Miri.ABI.TyAndLayout Miri.MIR.TyId}
    (hread : (annealEvalOperand localDecls layouts op none >>= annealReadImmediate) m =
      .ok ⟨.scalar (.fromScalarInt msc), lay⟩ m')
    (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = 1) (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    (annealTerminatorHooks localDecls layouts).readAssertCondition () op m =
      (m', .ok (decide (sc.bits ≠ 0))) := by
  dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
  unfold Miri.Interpreter.runRvalue
  rw [EStateM.bind_assoc_apply]
  rw [EStateM.bind_eq_ok hread]
  have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
    rw [hrel.size_eq, hsz]
    rfl
  have hmsc_data_eq : msc.data = sc.bits := hrel.data_eq
  rcases msc with ⟨msc_data, msc_size⟩
  subst hmsc_sz
  rcases hbits with h0 | h1
  · rw [h0] at hmsc_data_eq ⊢
    subst hmsc_data_eq
    dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
      Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
      Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
      Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
      Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
    rfl
  · rw [h1] at hmsc_data_eq ⊢
    subst hmsc_data_eq
    dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
      Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
      Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
      Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
      Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
    rfl

/-- The `lean-miri` side of an immediate `(T, bool)` local whose Anneal slot holds
an initialized scalar pair: an immediate `.scalarPair` with `ScalarRel`-related
components (the flag a `bool` scalar). -/
theorem pairLocal_miri_shape
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframe : FrameRel body mach af topFrame)
    {p : Local} {decl : LocalDecl} {t0 : RigidTy}
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_p : IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? af.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) :
    ∃ (msc0 msc1 : Miri.Memory.ScalarInt) (cl : Option Miri.Interpreter.LocalLayout),
      topFrame.locals[p]? = some
        ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
           layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) ∧
      (∀ l ∈ cl, l = translateTy decl.ty body.layouts) ∧
      ScalarRel sc0 msc0 ∧ ScalarRel sc1 msc1 ∧
      sc1.sizeBytes = 1 ∧ (sc1.bits = 0 ∨ sc1.bits = 1) := by
  obtain ⟨slot, mls, _, _, hslot, hmls, _, hlocrel⟩ := hframe.lookup_local hdecl
  rw [hls] at hslot
  injection hslot with hslot
  subst hslot
  cases hlocrel with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_p _ hmls mp)
  | immediate _ imm cl hcl hval =>
    rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
    · cases h
    · injection hv with hv
      subst hv
      cases himmRel with
      | scalarPair _ _ msc0 msc1 hrel0 hrel1 _ hbool2 =>
        obtain ⟨hsz1, hbits1⟩ := hbool2 t0 hpair
        exact ⟨msc0, msc1, cl, hmls, hcl, hrel0, hrel1, hsz1, hbits1⟩

/-- `Assert (copy (_p.1)) expected target unreachable` on the `bool` flag of an
initialized immediate `(T, bool)` local: both machines report UB (a failed
assertion), or both continue at `target` in `StateRel`-related states whose
`lean-miri` frame keeps every immediate local immediate; Anneal's locals are
unchanged. -/
theorem assert_pairFlag_step_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {p : Local} {decl : LocalDecl} {t0 : RigidTy} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind =
      .assert (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩) expected target
        .unreachable)
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_p : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? s.frame.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) :
    (∃ m' msg, stepMirFn body s = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg))) ∨
    (∃ (topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      m.stack.frames = #[topFrame] ∧
      stepMirFn body s =
        .step { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } } ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        ({ m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ }, .ok true) ∧
      StateRel body { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } }
        { m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ } ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  have hA := stepMirFn_at_terminator (body := body) hcal hphase hbb hstmt_none hstmt_len
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
          expected
          (.BoundsCheck
            (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
            (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)))
          target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  obtain ⟨msc0, msc1, cl, hloc, hcl, hrel0, hrel1, hsz1, hbits1⟩ :=
    pairLocal_miri_shape hframe hdecl hpair (himm_p topFrame hframes) hls
  obtain ⟨h_a, hlt, hmono, hframe', hread⟩ :=
    pairField_read_simulation hframes hframe s.memory.globals none hdecl sc0 sc1 msc0 msc1 hls hloc
      hcl 1 { kind := .bool, layoutIdx := 0 } (Or.inr ⟨rfl, by omega⟩) rfl
  have h_a' : evalOperand s.frame.locals (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)
      [] s.memory.globals body.layouts = .ok (.scalar sc1) s.frame.locals := h_a
  have hread' : (annealEvalOperand body.localDecls body.layouts
      (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)) none >>=
        annealReadImmediate) m =
      .ok ⟨.scalar (.fromScalarInt msc1),
        ⟨encodeTyId { kind := .bool, layoutIdx := 0 }, (translateTy decl.ty body.layouts).layout⟩⟩
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame p hlt
          (translateTy decl.ty body.layouts)]⟩ } := hread
  have h_m := readAssertCondition_of_read hread' hrel1 hsz1 hbits1
  have hM := evalTerminator_assert_ok (annealTerminatorHooks body.localDecls body.layouts) ()
    defaultSourceInfo (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
    expected
    (.BoundsCheck (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
      (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)))
    target .Unreachable m _ _ rfl h_m
  rw [← hm_term] at hM
  by_cases h_match : (expected == decide (sc1.bits ≠ 0)) = true
  · simp only [h_match, ↓reduceIte] at hM
    have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      (m' := { m with stack := ⟨#[{ cacheFrameLocalLayout topFrame p hlt
        (translateTy decl.ty body.layouts) with location := .mir ⟨target, 0⟩ }]⟩ })
      (r := .ok ())
      (by
        rw [hM]
        unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
        rw [stack_currentFrame?_singleton _
          (cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts)) rfl]
        rfl)
    have hA' : evalTerminator s bb.terminator (some body) =
        MirStepNode.step
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } } := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, hstack, h_a']
      dsimp only
      split
      · rfl
      · next h_contra =>
        rcases hbits1 with h0 | h1
        · revert h_match h_contra; simp only [h0]; intros; cases expected <;> contradiction
        · revert h_match h_contra; simp only [h1]; intros; cases expected <;> contradiction
    exact Or.inr ⟨topFrame, cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts),
      hframes, hA.trans hA', hM',
      StateRel.mk { cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts) with
          location := .mir ⟨target, 0⟩ } rfl hretCont ⟨retLay, hretPlace⟩
        ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
        hcal hstack hbor hprot hcaller (memoryAllocDisjoint_cache_layout hd_tf hlt _),
      hmono⟩
  · have h_if : (expected == decide (sc1.bits ≠ 0)) = false := by
      revert h_match; cases (expected == decide (sc1.bits ≠ 0)) <;> decide
    simp only [h_if, Bool.false_eq_true, ↓reduceIte] at hM
    have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      hM
    have hA' : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, hstack, h_a']
      dsimp only
      split
      · next h_contra =>
        rcases hbits1 with h0 | h1
        · revert h_if h_contra; simp only [h0]; intros; cases expected <;> contradiction
        · revert h_if h_contra; simp only [h1]; intros; cases expected <;> contradiction
      · rfl
    exact Or.inl ⟨_, "assert panic", hA.trans hA', hM'⟩

/-- `_d = copy (_p.0)` from an initialized immediate `(T, bool)` local `_p` into a
distinct immediate local `_d` whose layout fits the component: simulation
together with frame-immediacy preservation. -/
theorem step_assign_pairField0_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    {dstIdx p : Local} {dstDecl decl : LocalDecl} {t0 : RigidTy}
    (hkind : stmt.kind =
      .assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)))
    (hne : p ≠ dstIdx)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (himm_p : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? s.frame.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
    (hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc0.sizeBytes)
    (hbool_dst : dstDecl.ty.kind = .bool → sc0.sizeBytes = 1 ∧ (sc0.bits = 0 ∨ sc0.bits = 1))
    (hchar_dst : dstDecl.ty.kind = .char → sc0.sizeBytes = 4 ∧ isValidCharCode sc0.bits = true)
    (hnu : placeTouchesUnion body.localDecls body.layouts
      ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩ = false := by rfl)
    (hvalid : validateLoadedValue body.layouts body.localDecls
      (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩) (.scalar sc0) = true := by rfl) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
            .ok true →
          IsImmediateFrameLocal tf' j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  suffices StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ j, IsImmediateFrameLocal topFrame j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
          #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
          .ok true →
        IsImmediateFrameLocal tf' j) by
    refine ⟨this.1, fun tf₀ htf₀ j hj tf' htf' hok => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact this.2 j hj tf' htf' hok
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨msc0, msc1, cl, hloc, hcl, hrel0, _, _, _⟩ :=
    pairLocal_miri_shape hframe hdecl hpair (himm_p topFrame hframes) hls
  obtain ⟨_, mls_dst0, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := memoryAllocDisjoint_cache_layout hd_tf hlt_dst0 _
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_eq0]; exact hloc_dst0.layout_eq
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
  have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_dst hlt_dst0
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun _ hj => hj.cache_layout hlt_dst0 _
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  have hloc₀ : topFrame₀.locals[p]? = some
      ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
         layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ (Ne.symm hne)]
    exact hloc
  obtain ⟨h_a, hlt_p, hmono₁, hframe₁, hread⟩ :=
    pairField_read_simulation (m := m₀) rfl hframe₀ s.memory.globals
      (some (translateTy dstDecl.ty body.layouts)) hdecl sc0 sc1 msc0 msc1 hls hloc₀ hcl
      0 { kind := t0, layoutIdx := 0 } (Or.inl ⟨rfl, hrel0.sizeBytes_ne_zero⟩)
      (by rw [hpair]; rfl)
  have h_a' : evalOperand s.frame.locals (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)
      [] s.memory.globals body.layouts = .ok (.scalar sc0) s.frame.locals := h_a
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ p hlt_p (translateTy decl.ty body.layouts)
  have hread' : (annealEvalOperand body.localDecls body.layouts
      (translateOperand (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩))
      (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
      .ok ⟨.scalar (.fromScalarInt msc0),
        ⟨encodeTyId { kind := t0, layoutIdx := 0 }, (translateTy decl.ty body.layouts).layout⟩⟩
        { m with stack := ⟨#[topFrame₁]⟩ } := hread
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperand body.localDecls body.layouts
            (translateOperand (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩))
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
          fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
    rw [EStateM.bind_eq_ok hevalPlace_dst]
    exact EStateM.bind_assoc_apply _ _ _ m₀
  have ha_ok : evalStmt s stmt body.localDecls body.layouts =
      match get? s.frame.locals dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals dstIdx (.init (.scalar sc0)) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub := by
    unfold evalStmt; rw [hkind]; dsimp only
    have huse : evalRvalue s.frame.locals
        (.use (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)) s.memory
        body.localDecls body.layouts = .ok (.scalar sc0) s.frame.locals s.memory := by
      have h_ld : evalOperand s.frame.locals (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)
          [] s.memory.globals body.layouts [] body.localDecls = .ok (.scalar sc0) s.frame.locals := by
        have h0 := h_a'
        unfold evalOperand at h0 ⊢
        dsimp only at h0 ⊢
        rw [hls] at h0 ⊢
        dsimp only at h0 ⊢
        rw [hnu]
        exact h0
      unfold evalRvalue
      dsimp only
      rw [hbor, hcaller, hstack, h_ld]
      dsimp only
      rw [hvalid]
    rw [huse]
    dsimp only
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]; rfl
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc0)) destPlace)
        { m with stack := ⟨#[topFrame₁]⟩ } := by
    rw [hm_eval]
    apply runRvalue_eq_of_eq
    exact EStateM.bind_eq_ok hread'
  have himmRel' : ImmediateRel dstDecl.ty body.layouts (.scalar sc0) (.scalar (.fromScalarInt msc0)) :=
    .scalar sc0 msc0 hrel0 hsz_dst hbool_dst hchar_dst
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ := memoryAllocDisjoint_cache_layout hdisj₀ hlt_p _
  exact write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
    hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
    hframes hframe.body_eq hframe.location_eq (fun j hj => hmono₁ j (hmono₀ j hj))
    hbb hstmt hframe₁ hdisj₁ hdecl_dst
    (hmono₁ dstIdx (hmono₀ dstIdx (himm_dst topFrame hframes))) himmRel' ha_ok hm_write

/-! ### Body-specific closed invariant for `checkedAddBody` -/

/-- `bb0` of `checkedAddBody rhs`. -/
def checkedAddBb0 (rhs : Nat) : BasicBlockData :=
  blk [st (.storageLive 1),
      st (.assign (pl 1) (.binaryOp .addWithOverflow (.constant (Witness.constU16 65500))
        (.constant (Witness.constU16 rhs))))]
    (.assert (.copy { local_ := 1, projection := [.field 1 Witness.boolTy] }) false 1 .unreachable)

/-- `bb1` of `checkedAddBody rhs`. -/
def checkedAddBb1 : BasicBlockData :=
  blk [st (.assign (pl 0) (.use (.copy { local_ := 1, projection := [.field 0 Witness.u16Ty] }))),
      st (.storageDead 1)] .return_

theorem checkedAdd_blocks (rhs : Nat) :
    (checkedAddBody rhs).basicBlocks = [checkedAddBb0 rhs, checkedAddBb1] := rfl

/-- Shape of `_1` at the two program points of `checkedAddBody` that read its
fields (`bb0`'s `Assert` and `bb1[0]`): an initialized pair whose first
component is a 2-byte scalar. `ImmediateRel` alone does not pin that width. -/
def CheckedAddShape (s : MachineState) : Prop :=
  ((s.frame.blockIdx = 0 ∧ s.frame.stmtIdx = 2) ∨ (s.frame.blockIdx = 1 ∧ s.frame.stmtIdx = 0)) →
    ∃ sc0 sc1 : MirAst.ScalarInt,
      get? s.frame.locals 1 = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
      sc0.sizeBytes = 2

/-- The closed invariant for `checkedAddBody`: the `LM-1.1` invariant plus the
shape of `_1` where its fields are read. -/
def CheckedAddInv (rhs : Nat) (s : MachineState) (m : AnnealStepState) : Prop :=
  ScalarFragmentInv (checkedAddBody rhs) (fun _ => True) s m ∧ CheckedAddShape s

theorem checkedAdd_phase (rhs : Nat) : ∀ p, (checkedAddBody rhs).phase ≠ .other p := by
  intro p h
  simp [checkedAddBody, mkBody] at h

theorem get?_of_set?_eq_some {α : Type} {l l' : List α} {i : Nat} {v : α}
    (h : set? l i v = some l') : get? l' i = some v := by
  unfold set? at h
  split at h
  · next hlt =>
    injection h with h
    subst h
    rw [get?_eq_getElem?, List.getElem?_set_self hlt]
  · cases h

/-- After `_1 = AddWithOverflow(const 65500_u16, const rhs_u16)` the slot of
`_1` holds a pair whose first component is a 2-byte scalar. -/
theorem checkedAdd_add_shape {rhs : Nat} {s s' : MachineState}
    (hcal : s.memory.activeCallee = none) (hbor : s.memory.borrows = [])
    (hprot : s.memory.activeProtectors = []) (hcaller : s.memory.callerLocals = [])
    (hb : s.frame.blockIdx = 0) (hi : s.frame.stmtIdx = 1)
    (hstep : stepMirFn (checkedAddBody rhs) s = .step s') :
    ∃ sc0 sc1 : MirAst.ScalarInt,
      get? s'.frame.locals 1 = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
      sc0.sizeBytes = 2 := by
  rw [stepMirFn_eq_of_not_other _ s hcal (checkedAdd_phase rhs), hb, hi] at hstep
  obtain ⟨sc0, sc1, hrv, hsz⟩ : ∃ sc0 sc1 : MirAst.ScalarInt,
      evalRvalue s.frame.locals
        (.binaryOp .addWithOverflow (.constant (Witness.constU16 65500))
          (.constant (Witness.constU16 rhs))) s.memory
        (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts =
        .ok (.aggregate 0 [.scalar sc0, .scalar sc1]) s.frame.locals s.memory ∧
      sc0.sizeBytes = 2 := by
    apply Exists.intro
    apply Exists.intro
    constructor
    · unfold evalRvalue
      rw [hbor, hcaller]
      rfl
    · rfl
  change evalStmt s (st (.assign (pl 1) (.binaryOp .addWithOverflow
      (.constant (Witness.constU16 65500)) (.constant (Witness.constU16 rhs)))))
      (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts = .step s' at hstep
  unfold evalStmt at hstep
  dsimp only [st, pl] at hstep
  rw [hrv] at hstep
  dsimp only at hstep
  revert hstep
  rw [hprot]
  cases hget : get? s.frame.locals 1 with
  | none => intro h; exact absurd h MirStepNode_fail_ne_step
  | some slot =>
    cases slot with
    | dead => intro h; exact absurd h MirStepNode_fail_ne_step
    | uninit =>
      dsimp only
      cases hset : set? s.frame.locals 1 (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) with
      | none => intro h; exact absurd h MirStepNode_fail_ne_step
      | some locals₂ =>
        intro h
        have h' := MirStepNode_step_inj h
        subst h'
        exact ⟨sc0, sc1, get?_of_set?_eq_some hset, hsz⟩
    | init _ =>
      dsimp only
      cases hset : set? s.frame.locals 1 (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) with
      | none => intro h; exact absurd h MirStepNode_fail_ne_step
      | some locals₂ =>
        intro h
        have h' := MirStepNode_step_inj h
        subst h'
        exact ⟨sc0, sc1, get?_of_set?_eq_some hset, hsz⟩

/-- Statement steps of `checkedAddBody` advance the statement index. -/
theorem checkedAdd_stmt_location {rhs : Nat} {s s' : MachineState} {bb : BasicBlockData}
    {stmt : Statement}
    (hcal : s.memory.activeCallee = none)
    (hbb : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hk : stmt.kind = .nop ∨ (∃ l, stmt.kind = .storageLive l) ∨
      (∃ l, stmt.kind = .storageDead l) ∨ (∃ dstIdx rv, stmt.kind = .assign ⟨dstIdx, .nil⟩ rv))
    (hs : stepMirFn (checkedAddBody rhs) s = .step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  rw [stepMirFn_eq_of_not_other _ s hcal (checkedAdd_phase rhs)] at hs
  simp only [hbb, hstmt] at hs
  exact evalStmt_step_location hk hs

/-- `NonAddrTakenImmediate` after a continuing step, from frame-immediacy
preservation. -/
theorem nonAddrTakenImmediate_of_pres {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {m m' : AnnealStepState} {r : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hframes_ex : ∃ tf, m.stack.frames = #[tf])
    (himm : NonAddrTakenImmediate body nonAddrTaken m)
    (hpres : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf', r.1.stack.frames = #[tf'] → r.2 = .ok true → IsImmediateFrameLocal tf' j)
    (hr : r = (m', .ok true)) :
    NonAddrTakenImmediate body nonAddrTaken m' := by
  intro tf' htf' idx decl hdecl hna
  obtain ⟨tf, htf⟩ := hframes_ex
  subst hr
  exact hpres tf htf idx (himm tf htf idx decl hdecl hna) tf' htf' rfl

/-- Lift a `StepRel` of `checkedAddBody` to `Lockstep` for `CheckedAddInv`. -/
theorem checkedAdd_lockstep_of_stepRel {rhs : Nat} {s : MachineState} {m : AnnealStepState}
    (hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
      (Miri.Interpreter.Step.step
        (annealStepHooks (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts) () m))
    (hnext : ∀ s' m', stepMirFn (checkedAddBody rhs) s = .step s' →
      Miri.Interpreter.Step.step
        (annealStepHooks (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts) () m =
          (m', .ok true) →
      ValidFrameLocation (checkedAddBody rhs) s'.frame ∧ CheckedAddShape s' ∧
        NonAddrTakenImmediate (checkedAddBody rhs) (fun _ => True) m') :
    Lockstep (annealMiriHooks (checkedAddBody rhs)) (CheckedAddInv rhs)
      (ImmediateRetRel (checkedAddBody rhs)) m (stepMirFn (checkedAddBody rhs) s)
      ((annealMiriHooks (checkedAddBody rhs)).coreStep () m) :=
  StepRel.toLockstep hsim fun s' m' ha hm hrel =>
    ⟨⟨hrel, (hnext s' m' ha hm).1, (hnext s' m' ha hm).2.2⟩, (hnext s' m' ha hm).2.1⟩

/-- **Body-specific closed simulation** for `checkedAddBody rhs`: `CheckedAddInv`
is step-closed for every `rhs < 65536`. -/
theorem checkedAdd_stepClosedSim (rhs : Nat) (hrhs : rhs < 65536) :
    StepClosedSim (checkedAddBody rhs) (annealMiriHooks (checkedAddBody rhs))
      (CheckedAddInv rhs) (ImmediateRetRel (checkedAddBody rhs)) := by
  refine ⟨fun s m ⟨⟨hstate, hloc, himm⟩, hshape⟩ => ?_⟩
  have hphase := checkedAdd_phase rhs
  have hstate' := hstate
  rcases hstate' with ⟨topFrame, hframes, _, _, _, hcal, hstack, hbor, hprot, hcaller, _⟩
  have himmF : ∀ idx decl, get? (checkedAddBody rhs).localDecls idx = some decl →
      ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf idx :=
    fun idx decl hdecl tf htf => himm tf htf idx decl hdecl trivial
  have hu16 : IsPrimScalarTy Witness.u16Ty := Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hb : s.frame.blockIdx = 0 ∨ s.frame.blockIdx = 1 := by
    rcases h : s.frame.blockIdx with _ | _ | k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [h, checkedAdd_blocks] at hbb
      cases hbb
  rcases hb with hb | hb
  · -- `bb0`
    have hbb0 : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx =
        some (checkedAddBb0 rhs) := by rw [hb]; rfl
    rw [hbb0] at hbb
    injection hbb with hbb
    subst hbb
    have hi : s.frame.stmtIdx = 0 ∨ s.frame.stmtIdx = 1 ∨ s.frame.stmtIdx = 2 := by
      have : (checkedAddBb0 rhs).statements.length = 2 := rfl
      omega
    rcases hi with hi | hi | hi
    · -- `StorageLive(_1)`
      have hstmt : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx =
          some (st (.storageLive 1)) := by rw [hi]; rfl
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb0 hstmt
        (fun tf htf => .storageLive _ 1 Witness.u16BoolDecl rfl rfl (himmF 1 _ rfl tf htf))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb0 hstmt (Or.inr (Or.inl ⟨1, rfl⟩)) hs'
      refine ⟨⟨checkedAddBb0 rhs, by rw [hblk]; exact hbb0,
        by rw [hidx, hi]; show 0 + 1 ≤ 2; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `_1 = AddWithOverflow(const 65500_u16, const rhs_u16)`
      have hstmt : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx =
          some (st (.assign (pl 1) (.binaryOp .addWithOverflow
            (.constant (Witness.constU16 65500)) (.constant (Witness.constU16 rhs))))) := by
        rw [hi]; rfl
      have hc : ∀ n, n < 65536 → ∀ tf, WellTypedScalarOperand (checkedAddBody rhs) tf
          (.constant (Witness.constU16 n)) Witness.u16Ty :=
        fun n hn tf => .constScalar _ ⟨n, 2⟩ rfl hu16 (Or.inr (Or.inl rfl))
          (by rw [scalarModulus_eq_two_pow]; simpa using hn) rfl (fun h => by cases h)
          (fun h => by cases h)
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb0 hstmt
        (fun tf htf => .assign _ 1 Witness.u16BoolDecl _ rfl rfl (himmF 1 _ rfl tf htf)
          (.binaryOp _ _ _ Witness.u16Ty Witness.u16Ty _ (hc 65500 (by decide) tf) (hc rhs hrhs tf)
            (.intWithOverflow _ _ _ _ _ (Or.inl rfl) (.uint .u16 rfl) (.uint .u16 rfl)
              (Or.inl ⟨_, rfl⟩) rfl)))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb0 hstmt (Or.inr (Or.inr (Or.inr ⟨1, _, rfl⟩))) hs'
      obtain ⟨sc0, sc1, hls, hsz⟩ := checkedAdd_add_shape hcal hbor hprot hcaller hb hi hs'
      refine ⟨⟨checkedAddBb0 rhs, by rw [hblk]; exact hbb0,
        by rw [hidx, hi]; show 1 + 1 ≤ 2; decide⟩,
        fun _ => ⟨sc0, sc1, hls, hsz⟩,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
    · -- `assert(copy (_1.1) == false) -> bb1` (unwind: unreachable)
      have hstmt_none : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx = none := by
        rw [hi]; rfl
      have hstmt_len : s.frame.stmtIdx = length (checkedAddBb0 rhs).statements := by
        rw [hi]; rfl
      obtain ⟨sc0, sc1, hls, hsz0⟩ := hshape (Or.inl ⟨hb, hi⟩)
      rcases assert_pairFlag_step_cases hstate hphase hbb0 hstmt_none hstmt_len
          (p := 1) (decl := Witness.u16BoolDecl) (t0 := .uint .u16) rfl rfl rfl
          (fun tf htf => himmF 1 _ rfl tf htf) hls with
        ⟨m', msg, hA, hM⟩ | ⟨tf, tf', hframes', hA, hM, hrel, hmono⟩
      · have hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
            (Miri.Interpreter.Step.step (annealStepHooks (checkedAddBody rhs).localDecls
              (checkedAddBody rhs).layouts) () m) := by
          rw [hA, hM]; exact StepRel.ub m' msg
        refine checkedAdd_lockstep_of_stepRel hsim fun s' m'' hs' _ => ?_
        rw [hA] at hs'
        exact absurd hs' MirStepNode_fail_ne_step
      · have hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
            (Miri.Interpreter.Step.step (annealStepHooks (checkedAddBody rhs).localDecls
              (checkedAddBody rhs).layouts) () m) := by
          rw [hA, hM]; exact StepRel.step _ _ hrel
        refine checkedAdd_lockstep_of_stepRel hsim fun s' m'' hs' hm' => ?_
        rw [hA] at hs'
        have hs'' := MirStepNode_step_inj hs'
        subst hs''
        refine ⟨⟨checkedAddBb1, rfl, Nat.zero_le _⟩, fun _ => ⟨sc0, sc1, hls, hsz0⟩, ?_⟩
        intro tf₂ htf₂ idx decl hdecl _
        rw [hM] at hm'
        injection hm' with hm'
        subst hm'
        dsimp only at htf₂
        rw [hframes] at hframes'
        injection hframes' with h0
        injection h0 with h0 _
        subst h0
        injection htf₂ with h1
        injection h1 with h1 _
        subst h1
        exact hmono idx (himmF idx decl hdecl topFrame hframes)
  · -- `bb1`
    have hbb1 : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx = some checkedAddBb1 := by
      rw [hb]; rfl
    rw [hbb1] at hbb
    injection hbb with hbb
    subst hbb
    have hi : s.frame.stmtIdx = 0 ∨ s.frame.stmtIdx = 1 ∨ s.frame.stmtIdx = 2 := by
      have : checkedAddBb1.statements.length = 2 := rfl
      omega
    rcases hi with hi | hi | hi
    · -- `_0 = copy (_1.0)`
      have hstmt : get? checkedAddBb1.statements s.frame.stmtIdx =
          some (st (.assign (pl 0)
            (.use (.copy { local_ := 1, projection := [.field 0 Witness.u16Ty] })))) := by
        rw [hi]; rfl
      obtain ⟨sc0, sc1, hls, hsz0⟩ := hshape (Or.inr ⟨hb, hi⟩)
      have hsim := step_assign_pairField0_simulation_ext hstate hphase hbb1 hstmt
        (dstIdx := 0) (p := 1) (dstDecl := Witness.u16Decl) (decl := Witness.u16BoolDecl)
        (t0 := .uint .u16) rfl (by decide) rfl rfl rfl
        (fun tf htf => himmF 0 _ rfl tf htf) (fun tf htf => himmF 1 _ rfl tf htf) hls
        (by rw [hsz0]; rfl) (fun h => by cases h) (fun h => by cases h)
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb1 hstmt (Or.inr (Or.inr (Or.inr ⟨0, _, rfl⟩))) hs'
      refine ⟨⟨checkedAddBb1, by rw [hblk]; exact hbb1, by rw [hidx, hi]; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `StorageDead(_1)`
      have hstmt : get? checkedAddBb1.statements s.frame.stmtIdx = some (st (.storageDead 1)) := by
        rw [hi]; rfl
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb1 hstmt
        (fun tf htf => .storageDead _ 1 Witness.u16BoolDecl rfl rfl (by decide)
          (himmF 1 _ rfl tf htf))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb1 hstmt (Or.inr (Or.inr (Or.inl ⟨1, rfl⟩))) hs'
      refine ⟨⟨checkedAddBb1, by rw [hblk]; exact hbb1, by rw [hidx, hi]; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `return`
      have hstmt_none : get? checkedAddBb1.statements s.frame.stmtIdx = none := by
        rw [hi]; rfl
      have hstmt_len : s.frame.stmtIdx = length checkedAddBb1.statements := by
        rw [hi]; rfl
      have hsim := step_terminator_goto_return_simulation hstate hphase hbb1 hstmt_none hstmt_len
        rfl (Or.inr (Or.inl ⟨rfl, Witness.u16Decl, rfl, IsPrimScalarTy.size_ne_zero hu16,
          fun tf htf => himmF 0 _ rfl tf htf⟩))
      refine checkedAdd_lockstep_of_stepRel hsim fun s' m' hs' _ => ?_
      rw [stepMirFn_at_terminator hcal hphase hbb1 hstmt_none hstmt_len] at hs'
      unfold evalTerminator at hs'
      rw [show checkedAddBb1.terminator.kind = .return_ from rfl, hstack, hbor, hprot] at hs'
      dsimp only [hasFrameDeallocProtectorConflict, disableFrameBorrows] at hs'
      revert hs'
      cases get? s.frame.locals 0 with
      | none => exact fun h => absurd h MirStepNode_fail_ne_step
      | some slot =>
        cases slot with
        | dead => exact fun h => absurd h MirStepNode_fail_ne_step
        | uninit => exact fun h => absurd h MirStepNode_fail_ne_step
        | init retV =>
          dsimp only []
          cases valueContainsUninit retV with
          | true => exact fun h => absurd h MirStepNode_fail_ne_step
          | false => exact fun h => absurd h MirStepNode_retNormal_ne_step

/-- The entry states satisfy `CheckedAddInv`. -/
theorem checkedAdd_entry (rhs : Nat) :
    CheckedAddInv rhs (initMachineState (checkedAddBody rhs) [])
      (miriEntryState (checkedAddBody rhs)) := by
  refine ⟨⟨stateRel_entry _, ⟨checkedAddBb0 rhs, rfl, Nat.zero_le _⟩, entry_immediate _ _⟩, ?_⟩
  intro h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact absurd h (by show ¬ (0 = 2); decide)
  · exact absurd h (by show ¬ (0 = 1); decide)

/-- **Whole-program `TreeSafe ↔ System.Safe`** for the checked-addition witness,
for every `rhs < 65536`. -/
theorem checkedAdd_treeSafe_iff_miriSafe (rhs : Nat) (hrhs : rhs < 65536) :
    TreeSafe (mirCallTree (checkedAddBody rhs) []) ↔
      (miriSystem (annealMiriHooks (checkedAddBody rhs))).Safe
        (miriEntryState (checkedAddBody rhs)) :=
  treeSafe_iff_miriSafe (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)

/-- Bidirectional finite-step UB reachability for the checked-addition witness. -/
theorem checkedAdd_reachesUB_iff (rhs : Nat) (hrhs : rhs < 65536) :
    MirReachesUB (mirCallTree (checkedAddBody rhs) []) ↔
      ∃ e, (miriSystem (annealMiriHooks (checkedAddBody rhs))).ReachesOutcome
        (miriEntryState (checkedAddBody rhs)) (.undefinedBehavior e) :=
  reachesUB_iff_miriReachesUB (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)

/-- Partial-correctness equivalence for the checked-addition witness. -/
theorem checkedAdd_partialCorrect_iff (rhs : Nat) (hrhs : rhs < 65536) (postA : Value → Prop)
    (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, ImmediateRetRel (checkedAddBody rhs) retVal v → (postA retVal ↔ postM v)) :
    (miriSystem (annealMiriHooks (checkedAddBody rhs))).PartialCorrect
        (miriEntryState (checkedAddBody rhs)) postM ↔
      ∀ tr retVal mem, ReachesRet (mirCallTree (checkedAddBody rhs) []) tr (.normal (retVal, mem)) →
        postA retVal :=
  partialCorrect_iff_annealPostcondition (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)
    postA postM hpost

/-! ### Whole-program return witnesses -/

/-- **`arith_offset` returns from entry** (`LM-4.2`, `arithOffsetPosEntryBody`):
`StorageLive(_1.._3); _1 = 42_u64; goto bb1; bb1: _2 = &raw mut _1;
_0 = arith_offset(copy _2, 5_isize) -> bb2; bb2: return` runs in both machines from
`initMachineState` / `miriEntryState` to a normal root return of the raw pointer `40`
bytes past `_1` (`step_terminator_return_rawPtr_lm3_1_simulation`), with
`ImmediateRelLM3_1`-related return values. -/
theorem w3_arith_offset_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns arithOffsetPosEntryBody (annealMiriHooks arithOffsetPosEntryBody)
        (initMachineState arithOffsetPosEntryBody [])
        (miriEntryState arithOffsetPosEntryBody)
        (.ptr { allocId := 1, offsetBytes := 40 } 8) (.immediate imm0) ∧
      get? arithOffsetPosEntryBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_1
        [rawPtrAllocMapEntry arithOffsetPosEntryBody.localDecls
          arithOffsetPosEntryBody.layouts .mut 1 1 Witness.lm31AllocId1]
        decl0.ty arithOffsetPosEntryBody.layouts
        (.ptr { allocId := 1, offsetBytes := 40 } 8) imm0 := by
  obtain ⟨s₁, s₂, m₁, m₂, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, _, hret, hmret, hdecl0, hop,
    himm⟩ := retArithOffset_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 5) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hmret)
      (.refl _)))
    hmret rfl (by change (annealControlHooks.returnOperand () m₂).2 = _; rw [hop])

/-- **`write_bytes` then read back, whole program from entry, both machines return the
written bytes** (`retWriteBytesReadBody`): `StorageLive(_1.._3); _1 = const 42_u64;
goto bb1; bb1: _2 = &raw mut _1; _3 = write_bytes::<u64>(copy _2, 0xAB, 1) -> bb2;
bb2: _0 = copy (*_2); return`, run from `initMachineState` / `miriEntryState`.

* `lean-miri` fills `_1` with `0xAB` bytes through the raw pointer, reads them back
  through it, and its whole program is `System.Safe`, returns
  `0xABABABABABABABAB_u64` (`ImmediateRel`), and is partially correct only for that
  value (`retWriteBytesRead_prefix_miri`, then `retWriteBytesRead_ref_trace`, in
  lockstep with the pre-Stage-1 reference model).
* Stage-1 `stepMirFn` executes `write_bytes` inline
  (`Trusted.Rustc.V2026_06_01.MirSemantics.evalWriteBytesCall`, since
  `ws-repatriate-leaked-ground-semantics-to-tcb`) and Anneal's whole program is
  `TreeSafe` and returns the same `0xABABABABABABABAB_u64` (`AgreeReturns`). (Before
  that episode, Stage-1 handed the call to the environment and returned the
  unchanged `42_u64`.) -/
theorem w6_write_bytes_read_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns retWriteBytesReadBody (annealMiriHooks retWriteBytesReadBody)
        (initMachineState retWriteBytesReadBody []) (miriEntryState retWriteBytesReadBody)
        (.scalar ⟨0xABABABABABABABAB, 8⟩) (.immediate imm0) ∧
      get? retWriteBytesReadBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retWriteBytesReadBody.layouts (.scalar ⟨0xABABABABABABABAB, 8⟩) imm0 := by
  obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, _, _, hext, hm₂, _, _, _, hm₃, _, _, _,
    hmret, hdecl0, hop, himm⟩ := retWriteBytesRead_ref_trace
  -- `lean-miri`: the entry block, then the traced run to the root pop.
  have hpath : MiriPath (annealMiriHooks retWriteBytesReadBody)
      (miriEntryState retWriteBytesReadBody) m₃ :=
    (MiriPath.of_runLoopFuel retWriteBytesRead_prefix_miri).trans
      (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hmret) (.refl _))))
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_path_return hpath hmret rfl
    (by change (annealControlHooks.returnOperand () m₃).2 = _; rw [hop])
  -- Anneal: the whole program runs to the root return of the written bytes.
  obtain ⟨hAsafe, tr, mem, htr⟩ := anneal_returns_of_bits (body := retWriteBytesReadBody)
    (N := 30) (sz := 8) (b := 0xABABABABABABABAB) (s := initMachineState retWriteBytesReadBody [])
    (by kernel_decide)
  refine ⟨decl0, imm0, ⟨hAsafe, ⟨tr, mem, htr⟩, hsafe, hreach, fun v' hv' => ?_⟩, hdecl0, himm⟩
  have := huniq _ hv'
  injection this


end LeanMiriSpec.Correspondence.MiriDiffWitnesses
