/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.FloatCastLM.CodecAndCast

/-!
# Immediate-local real-step float-cast simulation (`LeanMiriSpec.FloatCastLM.RealStepDirect`)

Second layer (Part 8, immediate locals) of the IEEE-754 float-cast correspondence; see the
umbrella module `LeanMiriSpec.FloatCastLM` for the architectural overview and the submodule map.

Real-step simulation in `StateRelLM3_1` / `StepRelLM3_1` of `_d = (copy|move) _s as T` and
`_d = const c as T` between `stepMirFn` and `Miri.Interpreter.Step.step` under
`annealStepHooksFloat` when the destination is an immediate (non-promoted) local:
`evalRvalue_floatCast_eq`, `finish_write_immediate_from_mid_hooks`,
`step_cast_float_{copy,move,constant}_simulation_mode` (either NaN mode), and their
nondeterministic-mode corollaries `step_cast_float_{copy,move,constant}_simulation`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Part 8. Real-step simulation (`StateRelLM3_1` / `StepRelLM3_1`) -/

theorem estate_throw_bind_float {ε σ α β : Type} (e : ε) (f : α → EStateM ε σ β) :
    (throw e >>= f : EStateM ε σ β) = throw e := rfl

theorem annealReadImmediate_uninit_eq (lay : Miri.Interpreter.LocalLayout) :
    annealReadImmediate (⟨.immediate .uninit, lay⟩ : Miri.Interpreter.OpTy AnnealProv) =
      throw (.undefinedBehavior "read of uninitialized local") := rfl

/-- Every modeled float cast of an uninitialized immediate source reports
`read of uninitialized local` UB (after the source-validity type check succeeds). -/
theorem cast_floatCast_uninit (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨.immediate .uninit, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ =
      throw (.undefinedBehavior "read of uninitialized local") := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts, translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts, translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts, translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]

/-- **`OpTy`-generic error propagation in `Cast.cast`** (both `.immediate` and `.indirect`
operands): for any modeled float cast (`FloatCastSig`), if `annealReadImmediate` on the
source operand fails with `err` (e.g. `.immediate .uninit` or `.indirect mp` reading
uninitialized / dead / OOB / misaligned memory), `Cast.cast` fails with the exact same
error and state. -/
theorem cast_floatCast_of_readImmediate_err (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (srcOperand : Miri.Interpreter.Operand AnnealProv)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    {st st' : AnnealStepState} {err : Miri.Interpreter.StepError}
    (herr : annealReadImmediate ⟨srcOperand, translateTy srcTy layouts⟩ st = .error err st') :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨srcOperand, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ st =
      .error err st' := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr

/-- **`OpTy`-generic scalar reduction in `Cast.cast`** (both `.immediate` and `.indirect`
operands): whenever `annealReadImmediate` reads `⟨.scalar s, translateTy srcTy layouts⟩`
from `srcOperand` (such as a memory-backed `LocalRel.indirect` / promoted `allocMap` local
or a dereferenced `*ptr` place), `Cast.cast` reduces identically to `Cast.cast` on
`⟨.immediate (.scalar s), translateTy srcTy layouts⟩`. -/
theorem cast_floatCast_of_readImmediate_scalar (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (srcOperand : Miri.Interpreter.Operand AnnealProv)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    {st st' : AnnealStepState} (s : Miri.Memory.Scalar AnnealProv)
    (hok : annealReadImmediate ⟨srcOperand, translateTy srcTy layouts⟩ st =
      .ok ⟨.scalar s, translateTy srcTy layouts⟩ st') :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨srcOperand, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ st =
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨.immediate (.scalar s), translateTy srcTy layouts⟩ (translateCastKind kind)
        (encodeTyId castTy) ⟨destRef, translateTy castTy layouts⟩ st' := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl

/-- `annealReadImmediate` on an `.indirect` memory place of any float-cast scalar type
(`f32`, `f64`, or `i8..isize` / `u8..usize`) delegates directly to `annealReadMemoryPlace`. -/
theorem annealReadImmediate_indirect_floatCastScalar_eq {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty) (mp : Miri.Interpreter.MemPlace AnnealProv) :
    annealReadImmediate ⟨.indirect mp, translateTy ty ly⟩ =
      annealReadMemoryPlace mp (translateTy ty ly) := by
  have hf : (translateTy ty ly).layout.fields = .Primitive := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> rfl
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> rfl
  funext st
  unfold annealReadImmediate
  dsimp only
  rw [hf]

theorem IsFloatCastScalarTy.validateScalar_true {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty) (msc : Miri.Memory.ScalarInt) :
    annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) = true := by
  rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> rfl
  · rw [translateTy_of_floatIntTargetOfTy? ht ly]
    cases t <;> rename_i w <;> cases w <;> rfl

/-- Zero-offset memory read of a stack allocation for **any** `IsFloatCastScalarTy`
(`f32`, `f64`, and all 12 integer types, extending `SimLM3_1.annealReadMemoryPlace_zero_offset_eq`
beyond `IsPrimScalarTy` to floats). -/
theorem annealReadMemoryPlace_floatCastScalar_zero_offset_eq {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size) :
    annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      match localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size) false with
      | .ok sc =>
        if annealValidateScalarForTyId (translateTy ty ly).ty sc then
          .ok ⟨.scalar sc, translateTy ty ly⟩ st
        else
          .error (.undefinedBehavior "reading invalid value") st
      | .error (.invalidUninitBytes _) =>
        .error (.undefinedBehavior "read of uninitialized memory") st
      | .error (.readPointerAsInt _) | .error (.readPartialPointer _) =>
        .error (.unsupported "pointer-bytes-as-int memory read in scalar/pointer fragment") st
      | .error _ => .error (.invalidProgram "memory read error") st := by
  have hmeta :
      Miri.Memory.sizeAsI64 (translateTy ty ly).layout.size =
        .ok ((translateTy ty ly).layout.size.bytes.toNat : Int) ∧
      0 < (translateTy ty ly).layout.size.bytes.toNat ∧
      ((translateTy ty ly).layout.size.bytes.toNat : Int) < 2 ^ 63 ∧
      annealScalarReadProvenance (translateTy ty ly).layout.backendRepr = some false := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]
      cases f <;> exact ⟨rfl, by decide, by decide, rfl⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> exact ⟨rfl, by decide, by decide, rfl⟩
  obtain ⟨hsz, hgt0, hlt63, hprov_flag⟩ := hmeta
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind hgt0 hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  exact annealReadMemoryPlace_of_check_ok_aligned _ _ _ false st allocId Miri.ABI.Size.ZERO
    localAlloc _ hsz hchk hprov_flag rfl rfl hfind

theorem operandTy_copy_local {ld : List LocalDecl} {ly : LayoutTable} {idx : Local}
    {decl : LocalDecl} (hdecl : get? ld idx = some decl) :
    operandTy ld ly (.copy ⟨idx, .nil⟩) = some decl.ty := by
  unfold operandTy placeTy; simp only [hdecl]

theorem operandTy_move_local {ld : List LocalDecl} {ly : LayoutTable} {idx : Local}
    {decl : LocalDecl} (hdecl : get? ld idx = some decl) :
    operandTy ld ly (.move ⟨idx, .nil⟩) = some decl.ty := by
  unfold operandTy placeTy; simp only [hdecl]

/-- `evalRvalue` of a float cast reads its operand and applies `evalFloatCast` at the
operand's static type. -/
theorem evalRvalue_floatCast_eq {kind : CastKind} {srcTy castTy : Ty}
    (hsig : FloatCastSig kind srcTy castTy) (locals : List LocalSlot) (mem : Memory)
    (ld : List LocalDecl) (ly : LayoutTable) (op : MirAst.Operand) :
    evalRvalue locals (.cast kind op castTy) mem ld ly =
      evalFloatCastRvalue locals kind op castTy mem ld ly := by
  cases hsig <;> rfl

/-- Hook-generic version of `SimLM3_1`'s `finish_write_immediate_from_mid`: the shared
post-operand write step into an immediate local `dstIdx` from an operand-updated
`StateRelLM3_1` mid-state `(s_mid, tf_mid)`, for **any** `StepHooks` whose statement
evaluation reduces to the final `annealWriteImmediate` (here `annealStepHooksFloat`). -/
theorem finish_write_immediate_from_mid_hooks
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
    {val : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok val s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init val)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    StepRelLM3_1 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hd_dead_helper : slot_dm = .dead → mls_dm.value = .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step hooks () m) := by
    intro hsd_dead hmd_dead
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm, hsd_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  have hd_live_helper : ∀ oldImm, mls_dm.value = .live (.immediate oldImm) →
      slot_dm ≠ .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step hooks () m) := by
    intro oldImm hmd_imm hsd_ne
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
    have hm_ok : Miri.Interpreter.Step.evalStatement
        hooks ()
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
    rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step
          (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory) := by
      have hadv_eq : advanceStmt s (s_mid.frame.locals.set dstIdx (.init val)) s.memory =
          advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory := by
        rw [hs_frame_eq]; rfl
      rw [← hadv_eq]
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
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
    rw [ha_ok]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts (.init val)
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
  cases hloc_dm with
  | rawPtr _ _ _ _ _ _ _ _ => exact hd_live_helper _ rfl (by simp)
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
    | dead _ _ => exact hd_dead_helper rfl rfl
    | immediate _ oldImm _ _ hvd =>
      exact hd_live_helper oldImm rfl (by rcases hvd with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp)

/-- **Copy-operand real-step simulation** for every modeled float cast
(`_d = copy _s as T` with `CastKind.floatToFloat` / `floatToInt` / `intToFloat`) in either
NaN mode (`FloatNaNModeOk`): from any `StateRelLM3_1`-related state with immediate `_s`,
`_d`, Anneal's `stepMirFn` and `lean-miri`'s `Step.step` under `annealStepHooksFloat` step
in lockstep under `StepRelLM3_1` on every source state: `.dead` and `.uninit` sources are
UB in both machines, and an initialized source writes `ScalarRel`-related results (or UB
in both if `_d` is dead); deterministic mode additionally needs `FloatCastDetAgrees`. -/
theorem step_cast_float_copy_simulation_mode
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
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
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · -- `_s` is dead: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` is uninitialized: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
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
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok]
      rw [hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` holds a scalar: both machines write related cast results.
    subst hss
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
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
      rw [hop]
      dsimp only []
      rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok]
      rw [hcast]
    refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hrv_a hm_write (fun cachedLay hc => ?_)
    obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
    exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
      (Or.inr ⟨.scalar sc', rfl,
        .scalar sc' msc' hrel' hsz'
          (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))

/-- **Move-operand real-step simulation** for every modeled float cast
(`_d = move _s as T`), in either NaN mode: as `step_cast_float_copy_simulation_mode`, and
additionally both
machines deinitialize the moved-from `_s` (Anneal `LocalSlot.uninit`, `lean-miri`
`.live (.immediate .uninit)`) before writing `_d`; `.dead` / `.uninit` sources are UB in
both machines. -/
theorem step_cast_float_move_simulation_mode
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
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
  · -- `_s` is dead: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` is uninitialized: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` holds a scalar: both machines deinitialize `_s` and write related results.
    subst hss
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
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]; rfl
      rw [hop]
      dsimp only []
      rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hrv_a hm_write
      (fun cachedLay hc => ?_)
    obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
    exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
      (Or.inr ⟨.scalar sc', rfl,
        .scalar sc' msc' hrel' hsz'
          (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))

theorem layoutOfEncodedTyId_floatCastScalar {ty : Ty} (h : IsFloatCastScalarTy ty)
    (layouts : LayoutTable) : layoutOfEncodedTyId (encodeTyId ty) layouts = translateTy ty layouts := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [show encodeTyId ty = floatTyIdOf f from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hf layouts),
      translateTy_of_ieeeFormatOfTy? hf layouts]
    cases f <;> rfl
  · rw [show encodeTyId ty = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? ht layouts),
      translateTy_of_floatIntTargetOfTy? ht layouts]
    cases t <;> rename_i w <;> cases w <;> rfl

/-- **Constant-operand real-step simulation** for every modeled float cast
(`_d = const c as T` with a scalar constant `c : srcTy` of the source width), in either
NaN mode. -/
theorem step_cast_float_constant_simulation_mode
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm tf hframes
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
    rw [evalRvalue_floatCast_eq hsig]
    unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]
    dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, htr_dst]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hrv_a hm_write
    (fun cachedLay hc => ?_)
  obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
  exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
    (Or.inr ⟨.scalar sc', rfl,
      .scalar sc' msc' hrel' hsz'
        (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))


/-- **Copy-operand real-step simulation under the NaN refinement witness**
(`floatNondeterministic := true`, `chooseNaN := annealChooseQuietedNaN`): unconditional
bit-exact lockstep on **every** `f32` / `f64` / integer source state and bit pattern,
including every quiet, signaling, signed, or payload NaN. -/
theorem step_cast_float_copy_simulation
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm hptr8

/-- **Move-operand real-step simulation under the NaN refinement witness**. -/
theorem step_cast_float_move_simulation
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm hptr8

/-- **Constant-operand real-step simulation under the NaN refinement witness**. -/
theorem step_cast_float_constant_simulation
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
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) himm hptr8

end LeanMiriSpec.Correspondence
