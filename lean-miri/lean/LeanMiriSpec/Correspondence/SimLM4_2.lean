/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.CallLM4_2
import LeanMiriSpec.Correspondence.SaturatingLM4_2
import LeanMiriSpec.Correspondence.ExactDivLM4_2
import LeanMiriSpec.Correspondence.OffsetLM4_2
import LeanMiriSpec.Correspondence.WriteBytesLM4_2
import LeanMiriSpec.Correspondence.CopyLM4_2

/-!
# Intrinsic Simulation for `LM-4.2`

One-step correspondence between Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step` (under `annealStepHooks`) for the non-diverging
intrinsic statements and the inline intrinsic calls of `LM-4.2`:

* `step_intrinsic_assume_simulation`: `StatementKind.intrinsic (.assume op)`.
* `step_intrinsic_copyNonOverlapping_simulation`:
  `StatementKind.intrinsic (.copyNonOverlapping src dst count)` (with explicit
  `allocMap'` counterpart `step_intrinsic_copyNonOverlapping_simulation_explicit`
  and characterized divergences
  `step_intrinsic_copyNonOverlapping_uninit_src_divergence` and
  `step_intrinsic_copyNonOverlapping_perm_divergence`; proved in `CopyLM4_2`).
* `call_intrinsic_exact_div_simulation`: `core::intrinsics::exact_div`.
* `call_intrinsic_write_bytes_simulation`: `core::intrinsics::write_bytes`
  (with `call_intrinsic_write_bytes_simulation_explicit` and Tree Borrows
  permission divergence `call_intrinsic_write_bytes_perm_divergence`; proved in
  `WriteBytesLM4_2`).
* `call_intrinsic_offset_simulation`: `core::intrinsics::arith_offset` (to which
  `core::ptr::{const_ptr,mut_ptr}::wrapping_offset` lowers in `Runtime(PostCleanup)`
  MIR; proved in `OffsetLM4_2`).
* `call_intrinsic_bitops_simulation`: bundles
  `call_intrinsic_bitcount_simulation` (`ctpop`, `ctlz`, `ctlz_nonzero`, `cttz`,
  `cttz_nonzero`, `bswap`, `bitreverse`), `call_intrinsic_saturating_simulation`
  (`saturating_add`, `saturating_sub`), and `call_intrinsic_rotate_simulation`
  (`rotate_left` / `rotate_right`, a characterized divergence where `lean-miri`
  fails closed).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `NonDivergingIntrinsic.Assume` -/

/-- **`step_intrinsic_assume_simulation` (`LM-4.2`)**: one real step of
`StatementKind.intrinsic (.assume op)` in both machines, from any
`StateRelLM3_1`-related states, for a constant or a copied immediate local
`op` (`WellTypedScalarOperand`) of a one-byte primitive scalar type
(`bool`, or `u8` / `i8`, whose bit patterns `2..255` are invalid `bool`s).

Anneal's `evalStmt` steps exactly when the operand evaluates to the one-byte
scalar `1`, and `lean-miri`'s `Intrinsics.evalNondiverging` (`Assume`) succeeds
exactly when `Scalar.toBool` returns `true`. The two machines are related by
`StepRelLM3_1`:

* operand `1`: both advance to the next statement, related by `StateRelLM3_1`
  with the same `allocMap`;
* operand `0` (`false`): both report undefined behavior (`assume called with
  false`);
* operand with bit pattern `2..255`: both report undefined behavior
  (`Scalar.toBool` reports `invalidBool`);
* uninitialized or dead local operand: both report undefined behavior.

No outcome of either machine is assumed. -/
theorem step_intrinsic_assume_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {op : Operand} {span : String} {ty : Ty}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.intrinsic (.assume op), span⟩)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedScalarOperand body topFrame op ty)
    (hprim : IsPrimScalarTy ty)
    (hsz1 : (translateTy ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 1) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.intrinsic (.assume op), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperand body.localDecls body.layouts (translateOperand op) none >>=
            annealReadImmediate) >>= fun value =>
          (do
            let scalar ← liftScalarResult
              (value.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
            let cond ← liftScalarResult
              (scalar.toBool |>.mapError Miri.Interpreter.ScalarOps.scalarError)
            if !cond then throw (.undefinedBehavior "assume called with false") else pure ())) m := by
    rw [show translateStmt ⟨.intrinsic (.assume op), span⟩ =
        { sourceInfo := defaultSourceInfo, kind := .Intrinsic (.Assume (translateOperand op)) }
      from rfl, evalStatement_intrinsic_eq, evalNondiverging_assume_eq]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_assoc_apply]
  rcases evalOperand_scalar_lm3_1_simulation hstate hframes (hop tf hframes) hprim none with
    ⟨m', msg, ha, hm⟩ | ⟨sc, msc, tf', ha, hm, hstate', himm, _, _⟩
  · -- The operand read is undefined behavior in both machines.
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.intrinsic (.assume op), span⟩) m =
        (m', .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    have ha' : evalStmt s ⟨.intrinsic (.assume op), span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only
      rw [ha]
    rw [ha']
    exact .ub _ _
  · -- The operand is the one-byte scalar `sc` in Anneal and `msc` in `lean-miri`.
    cases himm with
    | scalar _ _ hrel hsz _ _ =>
    have hsc1 : sc.sizeBytes = 1 :=
      translateSizeBytes_inj hrel.validBytes (Or.inl rfl) (hsz.symm.trans hsz1)
    have htoBool := scalar_toBool_of_scalarRel hrel hsc1
    obtain ⟨tf₁, hframes₁, _, _, hfr₁, _, _, _, _, _, _, _⟩ := id hstate'
    injection hframes₁ with h₁
    injection h₁ with h₂
    subst h₂
    have hanneal : evalStmt s ⟨.intrinsic (.assume op), span⟩ body.localDecls body.layouts =
        match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
        | true => MirStepNode.step (advanceStmt s s.frame.locals)
        | false => MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only
      rw [ha]
      rfl
    rw [hanneal, hsc1]
    have hbeq1 : Nat.beq 1 1 = true := rfl
    rw [hbeq1, Bool.true_and]
    by_cases h0 : sc.bits = 0
    · -- `false`: both report undefined behavior.
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.intrinsic (.assume op), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "assume called with false")) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm]
        simp only [htoBool, h0, ↓reduceIte, liftScalarResult, Except.mapError,
          Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
          Bool.not_false, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      have hb : Nat.beq sc.bits 1 = false := by rw [h0]; rfl
      rw [hb]
      exact .ub _ _
    · by_cases h1 : sc.bits = 1
      · -- `true`: both advance.
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.intrinsic (.assume op), span⟩) m =
            ({ m with stack := ⟨#[tf']⟩ }, .ok ()) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm]
          simp only [htoBool, h1, ↓reduceIte, liftScalarResult, Except.mapError,
            Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure]
          rfl
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hfr₁.location_eq]
        have hb : Nat.beq sc.bits 1 = true := by rw [h1]; rfl
        rw [hb]
        exact .step _ _ (StateRelLM3_1.advance_same hstate' rfl)
      · -- Bit pattern `2..255`: `Scalar.toBool` reports `invalidBool`.
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.intrinsic (.assume op), span⟩) m =
            ({ m with stack := ⟨#[tf']⟩ },
              .error (Miri.Interpreter.ScalarOps.scalarError
                (.scalarInt (.invalidBool (UInt8.ofNat sc.bits))))) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm]
          simp only [htoBool, h0, h1, ↓reduceIte, liftScalarResult, Except.mapError,
            Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
            throw, throwThe, MonadExceptOf.throw, EStateM.throw]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        have hb : Nat.beq sc.bits 1 = false := by
          cases h : Nat.beq sc.bits 1
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) h1
        rw [hb]
        exact .ub _ _

/-! ## 2. Integer bit intrinsics -/

/-- **`call_intrinsic_bitcount_simulation` (`LM-4.2`)**: one real step of a call
of a one-operand integer bit intrinsic (`ctpop`, `ctlz`, `ctlz_nonzero`, `cttz`,
`cttz_nonzero`, `bswap`, `bitreverse`) in both machines, from
`StateRelLM3_1`-related states.

Anneal evaluates the call inline (`evalInlineIntrinsicCall?`,
`evalIntegerBitIntrinsic`); `lean-miri` runs the vendored call pipeline
(`Call.evalCallTerminator`) and the numeric arm of `Intrinsics.eval`
(`IntegerIntrinsic.run`). Both write equal results (the bit count as a `u32`,
or the permuted value of the operand's type) to the destination and return to
`targetBb`, or both report undefined behavior: a zero operand of
`ctlz_nonzero` / `cttz_nonzero`, an uninitialized or dead operand, or a dead
destination. -/
theorem call_intrinsic_bitcount_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (op : IntegerBitIntrinsic)
    {c : ConstOperand} {op₁ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁] ⟨dstIdx, []⟩ (some targetBb) unwind)
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hc : c.ty.kind = .fnDef (AnnealIntrinsic.ofBit op).defPath [ty.kind])
    (hcallee : findCallee? s.memory.callees (AnnealIntrinsic.ofBit op).defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty)
    {dstDecl : LocalDecl} {dstKind : Miri.MIR.IntegerKind}
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstInt : IsIntegralTy dstDecl.ty dstKind)
    (hcount : (op = .bswap ∨ op = .bitreverse) ∨ dstKind = .u32)
    (hperm : (op = .bswap ∨ op = .bitreverse) → dstKind = kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, _, _⟩ := id hstate
  have hopTy : operandTy body.localDecls body.layouts op₁ = some ty :=
    (hop₁ tf hframes).operandTy_eq
  refine step_intrinsic_call_one_simulation hstate hphase hbb hstmt_none hstmt_len
    (AnnealIntrinsic.ofBit_arity op) hterm hc hprog hop₁ hint.prim hdst hdstInt.prim hdstImm
    _ (evalTerminator_inline_intrinsic_call hterm hc hcallee (AnnealIntrinsic.ofBit_ne_exactDiv op))
    ?_ ?_
  · intro dest m'
    rw [intrinsics_eval_numeric _ _ _ (AnnealIntrinsic.ofBit_numeric op)]
    exact ⟨_, rfl⟩
  · intro sc₁ msc₁ hrel₁ id0 m'
    cases hrel₁ with
    | scalar _ _ hrel hsz _ _ =>
    have hvalid : ValidScalarBytes (integerKindByteWidth kind) := by
      unfold ValidScalarBytes; cases kind <;> simp [integerKindByteWidth]
    have hszEq : sc₁.sizeBytes = integerKindByteWidth kind :=
      translateSizeBytes_inj hrel.validBytes hvalid (hsz.symm.trans (hint.size_eq body.layouts))
    rw [intrinsics_eval_numeric _ _ _ (AnnealIntrinsic.ofBit_numeric op)]
    have hinline : ∀ L, evalInlineIntrinsicCall? s (AnnealIntrinsic.ofBit op).defPath [op₁]
        [.scalar sc₁] L ⟨dstIdx, []⟩ targetBb body.localDecls body.layouts =
        some (match evalIntegerBitIntrinsic op sc₁ with
          | .some r => intrinsicWriteReturn s L ⟨dstIdx, []⟩ targetBb (.scalar r)
          | .none => MirStepNode.fail .ub) := by
      intro L
      simp only [evalInlineIntrinsicCall?, integerBitIntrinsicOfPath?_ofBit, integerOperandBytes?,
        hopTy, hint.intCastTargetBytes_eq, hszEq, Nat.beq_refl] <;> rfl
    rcases annealNumericEval_simulation (ly := body.layouts) op hint hdstInt hcount hperm hrel hsz
        ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ rfl (some targetBb) m' with
      ⟨hnone, msg, hev⟩ | ⟨r, mr, hsome, hrelR, hszR, hev⟩
    · left
      refine ⟨?_, msg, hev⟩
      simp only [hinline, hnone]
    · right
      refine ⟨r, mr, .scalar r mr hrelR hszR (fun h => absurd h hdstInt.ne_bool)
        (fun h => absurd h hdstInt.ne_char), ?_, hev⟩
      simp only [hinline, hsome]

/-- **`call_intrinsic_rotate_simulation` (`LM-4.2`)**: one real step of a call of
`rotate_left` (`isLeft = true`) or `rotate_right` (`isLeft = false`) on an
integer `x : T` and a `u32` shift, from `StateRelLM3_1`-related states.

This is a characterized divergence. Anneal evaluates the intrinsic inline and
writes `evalRotate isLeft x shift` to the destination (or reports undefined
behavior for an uninitialized or dead argument). `lean-miri`'s pinned
`Intrinsics.eval` has no `rotate_left` / `rotate_right` arm and leaves the call
to the intrinsic's MIR fallback body, which is outside Anneal's correspondence
(`annealCallHooks.findMirOrEvalFn`), so the real `lean-miri` step fails closed
with `StepError.unsupported`, except that a dead argument is undefined behavior
in both machines. Neither machine's outcome is assumed. -/
theorem call_intrinsic_rotate_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} {isLeft : Bool}
    (hrot : (k = .rotateLeft ∧ isLeft = true) ∨ (k = .rotateRight ∧ isLeft = false))
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    {ty shiftTy : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hshift : IsIntegralTy shiftTy .u32)
    (hc : c.ty.kind = .fnDef k.defPath [ty.kind])
    (hcallee : findCallee? s.memory.callees k.defPath = none)
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ shiftTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl) :
    ((∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported msg))) ∧
      (stepMirFn body s = MirStepNode.fail .ub ∨
        ∃ x shift, evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
            body.layouts s.memory.callerLocals = .ok [.scalar x, .scalar shift] s.frame.locals ∧
          stepMirFn body s =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb
              (.scalar (evalRotate isLeft x shift)))) ∨
    (∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) ∧
      stepMirFn body s = MirStepNode.fail .ub) := by
  obtain ⟨tf, hframes, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
  have hk2 : k.arity = 2 := by rcases hrot with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hne : k ≠ .exactDiv := by rcases hrot with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> nofun
  have hunh : ∀ (args : Array (Miri.Interpreter.OpTy AnnealProv))
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := ty.kind, layoutIdx := 0 }] args dest (some targetBb) m' =
        .ok false m' := by
    intro args dest m'
    rcases hrot with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rw [intrinsics_eval_rotateLeft]; rfl
    · rw [intrinsics_eval_rotateRight]; rfl
  have hstepA : stepMirFn body s =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' =>
        match evalInlineIntrinsicCall? s k.defPath [op₁, op₂] vs locals' ⟨dstIdx, []⟩ targetBb
            body.localDecls body.layouts with
        | some node => node
        | none =>
          MirStepNode.extCall { defPath := k.defPath, args := vs, memory := s.memory }
            (resumeExternalCall s locals' ⟨dstIdx, []⟩ targetBb unwind)
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
    exact evalTerminator_inline_intrinsic_call hterm hc hcallee hne
  have hopTy : operandTy body.localDecls body.layouts op₁ = some ty :=
    (hop₁ tf hframes).operandTy_eq
  rcases step_intrinsic_call_two_unhandled hstate hbb hstmt_none hk2 hterm hc hop₁ hop₂ hint.prim
      hshift.prim hdst hunh with hunsup | ⟨m', msg, hm, hub⟩
  · left
    refine ⟨hunsup, ?_⟩
    rcases evalOperands_two_scalar_lm3_1 hstate hframes (hop₁ tf hframes) (hop₂ tf hframes)
        hint.prim hshift.prim with hub | ⟨x, shift, mx, mshift, hok, hrelx, hrelshift⟩
    · left
      rw [hstepA, hub]
    · right
      refine ⟨x, shift, hok, ?_⟩
      have hxsz := ImmediateRel.integral_sizeBytes hint hrelx
      have hshsz := ImmediateRel.integral_sizeBytes hshift hrelshift
      rw [hstepA, hok]
      rcases hrot with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [evalInlineIntrinsicCall?, integerOperandBytes?, hopTy,
          hint.intCastTargetBytes_eq, hxsz, hshsz, Nat.beq_refl] <;> rfl
  · right
    refine ⟨m', msg, hm, ?_⟩
    rw [hstepA, hub]

/-- Anneal's inline evaluation of `saturating_add` (`isAdd = true`) or
`saturating_sub` (`isAdd = false`) on two scalar arguments. -/
theorem evalInlineIntrinsicCall?_saturating {k : AnnealIntrinsic} {isAdd : Bool}
    (hsat : (k = .saturatingAdd ∧ isAdd = true) ∨ (k = .saturatingSub ∧ isAdd = false))
    (s : MachineState) (lhsOp rhsOp : MirAst.Operand) (a b : MirAst.ScalarInt)
    (L : List LocalSlot) (dest : Place) (targetBb : BasicBlockIdx)
    (ld : List LocalDecl) (ly : LayoutTable) :
    evalInlineIntrinsicCall? s k.defPath [lhsOp, rhsOp] [.scalar a, .scalar b] L dest targetBb
        ld ly =
      some (match integerOperandBytes? ld ly lhsOp with
        | some n =>
          match Nat.beq a.sizeBytes n with
          | false => MirStepNode.unsupported
          | true =>
            match evalSaturatingArith isAdd a b L s.memory (operandIsSigned ld lhsOp ly) with
            | .ok retVal localsAfter _ => intrinsicWriteReturn s localsAfter dest targetBb retVal
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
        | none => MirStepNode.unsupported) := by
  rcases hsat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **`call_intrinsic_saturating_simulation` (`LM-4.2`)**: one real step of a call
of `saturating_add` (`isAdd = true`) or `saturating_sub` (`isAdd = false`) on
two integers of type `T`, from `StateRelLM3_1`-related states.

Anneal evaluates the call inline (`evalSaturatingArith`); `lean-miri` runs the
vendored call pipeline and the saturating arm of `Intrinsics.eval` (overflowing
`ScalarOps.binary`, then `Size.signedIntMax` / `signedIntMin` by the sign of
the first operand, or `unsignedIntMax` / `0`). Both write equal results to the
destination and return to `targetBb`; uninitialized or dead arguments and a
dead destination are undefined behavior in both. -/
theorem call_intrinsic_saturating_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} {isAdd : Bool}
    (hsat : (k = .saturatingAdd ∧ isAdd = true) ∨ (k = .saturatingSub ∧ isAdd = false))
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hc : c.ty.kind = .fnDef k.defPath [ty.kind])
    (hcallee : findCallee? s.memory.callees k.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstInt : IsIntegralTy dstDecl.ty kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, _, _⟩ := id hstate
  have hopTy : operandTy body.localDecls body.layouts op₁ = some ty :=
    (hop₁ tf hframes).operandTy_eq
  have hsigned : operandIsSigned body.localDecls op₁ body.layouts = kind.signed := by
    rw [← hint.signed_eq]; simp [hopTy]
  have hk2 : k.arity = 2 := by rcases hsat with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hne : k ≠ .exactDiv := by rcases hsat with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> nofun
  have heval : ∀ (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv),
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := ty.kind, layoutIdx := 0 }] #[v₁, v₂] dest (some targetBb) =
      annealSaturatingEval body.localDecls body.layouts isAdd v₁ v₂ dest (some targetBb) := by
    intro v₁ v₂ dest
    rcases hsat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact intrinsics_eval_saturatingAdd _ _ _ _ _ _ _
    · exact intrinsics_eval_saturatingSub _ _ _ _ _ _ _
  refine step_intrinsic_call_two_simulation hstate hphase hbb hstmt_none hstmt_len hk2 hterm hc
    hprog hop₁ hop₂ hint.prim hint.prim hdst hdstInt.prim hdstImm _
    (evalTerminator_inline_intrinsic_call hterm hc hcallee hne) ?_ ?_ ?_
  · intro v₂ dest m'
    rw [heval]
    exact ⟨_, rfl⟩
  · intro msc₁ dest m'
    rw [heval]
    exact ⟨_, rfl⟩
  · intro sc₁ sc₂ msc₁ msc₂ hrel₁ hrel₂ id0 m'
    cases hrel₁ with
    | scalar _ _ hr₁ hsz₁ _ _ =>
    cases hrel₂ with
    | scalar _ _ hr₂ hsz₂ _ _ =>
    have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes :=
      translateSizeBytes_inj hr₁.validBytes hr₂.validBytes (hsz₁.symm.trans hsz₂)
    have hvalid : ValidScalarBytes (integerKindByteWidth kind) := by
      unfold ValidScalarBytes; cases kind <;> simp [integerKindByteWidth]
    have hszK : sc₁.sizeBytes = integerKindByteWidth kind :=
      translateSizeBytes_inj hr₁.validBytes hvalid (hsz₁.symm.trans (hint.size_eq body.layouts))
    obtain ⟨r, mr, hsatA, hrR, hev⟩ := annealSaturatingEval_simulation (ld := body.localDecls)
      (ly := body.layouts) isAdd hint hr₁ hr₂ hsz₁ hsz₂ s.frame.locals s.memory
      ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m'
    have hrsz : r.sizeBytes = sc₁.sizeBytes :=
      evalSaturatingArith_sizeBytes isAdd hr₁ hr₂ hsz_eq kind hsatA
    right
    refine ⟨r, mr, .scalar r mr hrR ?_ (fun h => absurd h hdstInt.ne_bool)
      (fun h => absurd h hdstInt.ne_char), ?_, ?_⟩
    · rw [hdstInt.translateTy_eq hint body.layouts body.layouts, hrsz]; exact hsz₁
    · simp only [evalInlineIntrinsicCall?_saturating hsat, integerOperandBytes?, hopTy,
        hint.intCastTargetBytes_eq, hszK, Nat.beq_refl, hsigned, hsatA]
    · rw [heval]; exact hev

/-! ## 3. `exact_div` -/

/-- The result of `evalExactDiv` has the width of its first operand. -/
theorem evalExactDiv_sizeBytes {lhs rhs q : MirAst.ScalarInt} {sg : Bool}
    (h : evalExactDiv lhs rhs sg = some q) : q.sizeBytes = lhs.sizeBytes := by
  unfold evalExactDiv at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (exact absurd h (by simp))

/-- Anneal's evaluation of a call of `exact_div` once the arguments have been
evaluated (the `exact_div` arm of `MirSemantics.evalTerminator`). -/
def annealExactDivCall (s : MachineState) (lhsOp : MirAst.Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (dstIdx : Local) (targetBb : BasicBlockIdx) (vs : List Value)
    (locals' : List LocalSlot) : MirStepNode :=
  match vs with
  | .scalar lhs :: .scalar rhs :: .nil =>
    match evalScalarExactDiv lhs rhs locals' s.memory (operandIsSigned ld lhsOp ly) with
    | .ok retVal localsAfter memAfter =>
      match writePlaceValue localsAfter memAfter.borrows ⟨dstIdx, []⟩ retVal with
      | .ok updatedLocals =>
        MirStepNode.step
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
            memory := memAfter }
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | _ => MirStepNode.unsupported

/-- Anneal's `evalTerminator` on a call of `exact_div` with no transparent
body: evaluate the arguments, then `annealExactDivCall`. -/
theorem evalTerminator_exactDiv_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.exactDiv.defPath [argKind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.exactDiv.defPath = none) :
    evalTerminator s term (some body) =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' =>
        annealExactDivCall s op₁ body.localDecls body.layouts dstIdx targetBb vs locals'
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalTerminator
  rw [hterm]
  simp only [extractCalleeDefPath?, hc]
  cases evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' =>
    simp only [hcallee]
    rfl
  | ub => rfl
  | unsupported => rfl

/-- **`call_intrinsic_exact_div_simulation` (`LM-4.2`, certifying `I-11`)**: one
real step of a call of `core::intrinsics::exact_div::<T>(a, b)` on integers of
any width and signedness (`u8`..`u128`, `usize`, `i8`..`i128`, `isize`), from
`StateRelLM3_1`-related states.

Anneal evaluates `evalScalarExactDiv`; `lean-miri` runs the vendored call
pipeline and the `exact_div` arm of `Intrinsics.eval` (`ScalarOps.binary .Rem`,
remainder check, `ScalarOps.binary .Div`). Both machines report undefined
behavior exactly when `b == 0`, when `T` is signed and `a == T::MIN && b == -1`,
or when `a % b != 0`; otherwise both write the exact quotient `a / b` to the
destination and return to `targetBb` with `StateRelLM3_1`-related states.
Uninitialized or dead arguments and a dead destination are undefined behavior
in both machines. -/
theorem call_intrinsic_exact_div_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.exactDiv.defPath [ty.kind])
    (hcallee : findCallee? s.memory.callees AnnealIntrinsic.exactDiv.defPath = none)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstInt : IsIntegralTy dstDecl.ty kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, _, _⟩ := id hstate
  have hopTy : operandTy body.localDecls body.layouts op₁ = some ty :=
    (hop₁ tf hframes).operandTy_eq
  have hsigned : operandIsSigned body.localDecls op₁ body.layouts = kind.signed := by
    rw [← hint.signed_eq]; simp [hopTy]
  have heval : ∀ (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv),
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        AnnealIntrinsic.exactDiv.name #[encodeTyId { kind := ty.kind, layoutIdx := 0 }] #[v₁, v₂]
        dest (some targetBb) =
      annealExactDivEval body.localDecls body.layouts v₁ v₂ dest (some targetBb) :=
    fun v₁ v₂ dest => intrinsics_eval_exactDiv _ _ _ _ _ _ _
  refine step_intrinsic_call_two_simulation hstate hphase hbb hstmt_none hstmt_len rfl hterm hc
    hprog hop₁ hop₂ hint.prim hint.prim hdst hdstInt.prim hdstImm _
    (evalTerminator_exactDiv_call hterm hc hcallee) ?_ ?_ ?_
  · intro v₂ dest m'
    rw [heval]
    exact ⟨_, rfl⟩
  · intro msc₁ dest m'
    rw [heval]
    exact ⟨_, rfl⟩
  · intro sc₁ sc₂ msc₁ msc₂ hrel₁ hrel₂ id0 m'
    cases hrel₁ with
    | scalar _ _ hr₁ hsz₁ _ _ =>
    cases hrel₂ with
    | scalar _ _ hr₂ hsz₂ _ _ =>
    rcases annealExactDivEval_simulation (ld := body.localDecls) (ly := body.layouts) hint hr₁ hr₂
        hsz₁ hsz₂ s.frame.locals s.memory
        ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' with
      ⟨hub, msg, hev⟩ | ⟨q, mq, hq, hrq, hev⟩
    · left
      refine ⟨?_, msg, by rw [heval]; exact hev⟩
      simp only [annealExactDivCall, hsigned, hub]
    · right
      have hqsz : q.sizeBytes = sc₁.sizeBytes := by
        unfold evalScalarExactDiv at hq
        split at hq
        · next q' hq' =>
          injection hq with h₁
          injection h₁ with h₂
          subst h₂
          exact evalExactDiv_sizeBytes hq'
        · cases hq
      refine ⟨q, mq, .scalar q mq hrq ?_ (fun h => absurd h hdstInt.ne_bool)
        (fun h => absurd h hdstInt.ne_char), ?_, by rw [heval]; exact hev⟩
      · rw [hdstInt.translateTy_eq hint body.layouts body.layouts, hqsz]; exact hsz₁
      · simp only [annealExactDivCall, hsigned, hq]
        rfl

/-! ## 4. All integer bit-manipulation and saturating intrinsics -/

/-- **`call_intrinsic_bitops_simulation` (`LM-4.2`)**: one real step of a call of
each integer bit-manipulation or saturating intrinsic, from
`StateRelLM3_1`-related states:

1. `ctpop`, `ctlz`, `ctlz_nonzero`, `cttz`, `cttz_nonzero`, `bswap`,
   `bitreverse`: lockstep `StepRelLM3_1` (`call_intrinsic_bitcount_simulation`);
2. `saturating_add`, `saturating_sub`: lockstep `StepRelLM3_1`
   (`call_intrinsic_saturating_simulation`);
3. `rotate_left`, `rotate_right`: Anneal computes the rotation while the real
   `lean-miri` step fails closed (`StepError.unsupported`), except for dead
   arguments, which are undefined behavior in both
   (`call_intrinsic_rotate_simulation`). -/
theorem call_intrinsic_bitops_simulation :
    (∀ {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
      {allocMap : List AllocMapEntry},
      StateRelLM3_1 body s m allocMap →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        ∀ (op : IntegerBitIntrinsic) {c : ConstOperand} {op₁ : MirAst.Operand}
          {dstIdx : Local} {targetBb : BasicBlockIdx} {unwind : UnwindAction},
          bb.terminator.kind = .call (.constant c) [op₁] ⟨dstIdx, []⟩ (some targetBb) unwind →
          ∀ {ty : Ty} {kind : Miri.MIR.IntegerKind},
            IsIntegralTy ty kind →
            c.ty.kind = .fnDef (AnnealIntrinsic.ofBit op).defPath [ty.kind] →
            findCallee? s.memory.callees (AnnealIntrinsic.ofBit op).defPath = none →
            (targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0) →
            (∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty) →
            ∀ {dstDecl : LocalDecl} {dstKind : Miri.MIR.IntegerKind},
              get? body.localDecls dstIdx = some dstDecl →
              IsIntegralTy dstDecl.ty dstKind →
              ((op = .bswap ∨ op = .bitreverse) ∨ dstKind = .u32) →
              ((op = .bswap ∨ op = .bitreverse) → dstKind = kind) →
              (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) →
              StepRelLM3_1 body m allocMap (stepMirFn body s)
                (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m)) ∧
    (∀ {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
      {allocMap : List AllocMapEntry},
      StateRelLM3_1 body s m allocMap →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        ∀ {k : AnnealIntrinsic} {isAdd : Bool},
          ((k = .saturatingAdd ∧ isAdd = true) ∨ (k = .saturatingSub ∧ isAdd = false)) →
          ∀ {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local}
            {targetBb : BasicBlockIdx} {unwind : UnwindAction},
            bb.terminator.kind =
              .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind →
            ∀ {ty : Ty} {kind : Miri.MIR.IntegerKind},
              IsIntegralTy ty kind →
              c.ty.kind = .fnDef k.defPath [ty.kind] →
              findCallee? s.memory.callees k.defPath = none →
              (targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0) →
              (∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty) →
              (∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty) →
              ∀ {dstDecl : LocalDecl},
                get? body.localDecls dstIdx = some dstDecl →
                IsIntegralTy dstDecl.ty kind →
                (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) →
                StepRelLM3_1 body m allocMap (stepMirFn body s)
                  (Miri.Interpreter.Step.step
                    (annealStepHooks body.localDecls body.layouts) () m)) ∧
    (∀ {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
      {allocMap : List AllocMapEntry},
      StateRelLM3_1 body s m allocMap →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        ∀ {k : AnnealIntrinsic} {isLeft : Bool},
          ((k = .rotateLeft ∧ isLeft = true) ∨ (k = .rotateRight ∧ isLeft = false)) →
          ∀ {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local}
            {targetBb : BasicBlockIdx} {unwind : UnwindAction},
            bb.terminator.kind =
              .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind →
            ∀ {ty shiftTy : Ty} {kind : Miri.MIR.IntegerKind},
              IsIntegralTy ty kind →
              IsIntegralTy shiftTy .u32 →
              c.ty.kind = .fnDef k.defPath [ty.kind] →
              findCallee? s.memory.callees k.defPath = none →
              (∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty) →
              (∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ shiftTy) →
              ∀ {dstDecl : LocalDecl},
                get? body.localDecls dstIdx = some dstDecl →
                (((∃ m' msg,
                    Miri.Interpreter.Step.step
                      (annealStepHooks body.localDecls body.layouts) () m =
                      (m', .error (.unsupported msg))) ∧
                  (stepMirFn body s = MirStepNode.fail .ub ∨
                    ∃ x shift,
                      evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
                        body.layouts s.memory.callerLocals =
                        .ok [.scalar x, .scalar shift] s.frame.locals ∧
                      stepMirFn body s =
                        intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb
                          (.scalar (evalRotate isLeft x shift)))) ∨
                (∃ m' msg,
                  Miri.Interpreter.Step.step
                    (annealStepHooks body.localDecls body.layouts) () m =
                    (m', .error (.undefinedBehavior msg)) ∧
                  stepMirFn body s = MirStepNode.fail .ub))) :=
  ⟨@call_intrinsic_bitcount_simulation, @call_intrinsic_saturating_simulation,
    @call_intrinsic_rotate_simulation⟩

end LeanMiriSpec.Correspondence
