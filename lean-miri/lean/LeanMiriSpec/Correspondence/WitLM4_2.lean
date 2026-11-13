/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM4_2
import LeanMiriSpec.Correspondence.WriteBytesLM4_2
import LeanMiriSpec.Correspondence.CopyLM4_2
import LeanMiriSpec.Correspondence.WitLM3_1

/-!
# Witnesses for `LM-4.2`

Concrete MIR bodies and `StateRelLM3_1`-related pre-states on which the
`LM-4.2` simulation theorems of `SimLM4_2.lean` apply, together with the real
outcome of one step of both machines (`stepMirFn` and
`Miri.Interpreter.Step.step` under `annealStepHooks`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- A `StepRelLM3_1` whose Anneal side steps forces a lockstep `lean-miri` step
to a related state. -/
theorem StepRelLM3_1.miri_step_of_anneal_step {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {s' : MachineState}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap (MirStepNode.step s') mRes) :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases h with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- A `StepRelLM3_1` whose Anneal side reports undefined behavior forces
`lean-miri` to report undefined behavior. -/
theorem StepRelLM3_1.miri_ub_of_anneal_ub {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap (MirStepNode.fail .ub) mRes) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  cases h with
  | ub m' msg => exact ⟨m', msg, rfl⟩

namespace WitnessLM4_2

/-! ## 1. Shared fixtures -/

def mkStmt42 (k : StatementKind) : MirAst.Statement := { kind := k, span := "lm-4.2-witness" }
def mkTerm42 (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "lm-4.2-witness" }
def local42 (i : Nat) : Place := { local_ := i, projection := [] }

/-- The type of rigid kind `k` (layout index `0`). -/
def tyOf (k : RigidTy) : Ty := { kind := k, layoutIdx := 0 }

/-- A mutable local of rigid kind `k`. -/
def declOf (k : RigidTy) : LocalDecl := { mutability := .mut, ty := tyOf k, debugName := none }

/-- The integer constant with bit pattern `bits` of width `size` and kind `k`. -/
def constInt (k : RigidTy) (bits size : Nat) : ConstOperand :=
  { ty := tyOf k, val := .scalar (.int ⟨bits, size⟩) }

/-- The function item constant of `path` instantiated at `argKind`. -/
def fnItem (path : DefPath) (argKind : RigidTy) : ConstOperand :=
  { ty := { kind := .fnDef path [argKind], layoutIdx := 0 }, val := .zeroSized }

def layout42 : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbi42 : FnAbi :=
  { args := [], ret := { layout := layout42, mode := .direct }, conv := .rust, canUnwind := false }

/-! ## 2. `NonDivergingIntrinsic.Assume` -/

/-- The only basic block of `assumeBody op`. -/
def assumeBB (op : MirAst.Operand) : BasicBlockData :=
  { statements := [mkStmt42 (.intrinsic (.assume op))],
    terminator := mkTerm42 .return_, isCleanup := false }

/-- `bb0: assume(op); return` with `_0 : u8` and `_1 : u8`. -/
def assumeBody (op : MirAst.Operand) : CapturedMir where
  defPath := "lm_4_2_witness::assume"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf (.uint .u8), declOf (.uint .u8)]
  basicBlocks := [assumeBB op]
  fnAbi := fnAbi42
  layouts := emptyLayoutTable
  allocations := []

/-- `lean-miri`'s `2_u8`. -/
def lm42Scalar2 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt8 2

theorem lm42_scalarRel2 : ScalarRel ⟨2, 1⟩ lm42Scalar2 :=
  ⟨Or.inl rfl, by decide, rfl, rfl⟩

/-- Anneal state at the `assume` statement, with `_1 = 2_u8` (an invalid `bool`
bit pattern). -/
def assumeAnnealPre (op : MirAst.Operand) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨2, 1⟩)] }
    memory := (initMachineState (assumeBody op) []).memory }

/-- `lean-miri`'s local `_1 = 2_u8`. -/
def assumeLocal1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  { value := .live (.immediate (.scalar (.fromScalarInt lm42Scalar2))), layout := none }

def assumeMiriFrame (op : MirAst.Operand) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (assumeBody op)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (tyOf (.uint .u8))) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none }, assumeLocal1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def assumeMiriPre (op : MirAst.Operand) : AnnealStepState :=
  { stack := ⟨#[assumeMiriFrame op]⟩, machine := AnnealMachine.empty }

theorem assume_stateRel (op : MirAst.Operand) :
    StateRelLM3_1 (assumeBody op) (assumeAnnealPre op) (assumeMiriPre op) [] := by
  refine StateRel.toLM3_1 (StateRel.mk (assumeMiriFrame op) rfl rfl
    ⟨translateTy (tyOf (.uint .u8)), rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | 1 => rintro ⟨⟩
      | _ + 2 => rintro ⟨⟩))
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = declOf (.uint .u8) := by simpa [assumeBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [assumeAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [assumeMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = declOf (.uint .u8) := by simpa [assumeBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨2, 1⟩) := by simpa [assumeAnnealPre, get?] using hslot.symm
    have hm : mls = assumeLocal1 := by
      simpa [assumeMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ none (fun _ h => nomatch h)
      (Or.inr ⟨_, rfl, .scalar _ _ lm42_scalarRel2 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | n + 2 =>
    simp [assumeBody, get?] at hdecl

/-- The `bool` constant `b`. -/
def constBool (b : Bool) : ConstOperand :=
  { ty := tyOf .bool, val := .scalar (.int ⟨if b then 1 else 0, 1⟩) }

theorem constBool_wellTyped (b : Bool) (tf : Miri.Interpreter.Frame AnnealProv
    Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand (assumeBody (.constant (constBool b))) tf
      (.constant (constBool b)) (tyOf .bool) := by
  refine .constScalar (constBool b) ⟨if b then 1 else 0, 1⟩ rfl (Or.inl rfl) (Or.inl rfl) ?_ rfl
    (fun _ => ⟨rfl, by cases b <;> simp⟩) (fun h => nomatch h)
  cases b <;> decide

/-- **`wit_lm4_2_assume_true`**: `assume(true)` steps in both machines to
`StateRelLM3_1`-related states (the next statement of the same block). -/
theorem wit_lm4_2_assume_true :
    ∃ m', stepMirFn (assumeBody (.constant (constBool true)))
        (assumeAnnealPre (.constant (constBool true))) =
        .step (advanceStmt (assumeAnnealPre (.constant (constBool true)))
          (assumeAnnealPre (.constant (constBool true))).frame.locals) ∧
      Miri.Interpreter.Step.step
        (annealStepHooks (assumeBody (.constant (constBool true))).localDecls
          (assumeBody (.constant (constBool true))).layouts) ()
        (assumeMiriPre (.constant (constBool true))) = (m', .ok true) ∧
      StateRelLM3_1 (assumeBody (.constant (constBool true)))
        (advanceStmt (assumeAnnealPre (.constant (constBool true)))
          (assumeAnnealPre (.constant (constBool true))).frame.locals) m' [] := by
  have hsim := step_intrinsic_assume_simulation (assume_stateRel (.constant (constBool true)))
    (by intro p h; cases h) (bb := assumeBB (.constant (constBool true)))
    rfl rfl (fun tf _ => constBool_wellTyped true tf) (Or.inl rfl) rfl
  have hA : stepMirFn (assumeBody (.constant (constBool true)))
      (assumeAnnealPre (.constant (constBool true))) =
      .step (advanceStmt (assumeAnnealPre (.constant (constBool true)))
        (assumeAnnealPre (.constant (constBool true))).frame.locals) := rfl
  rw [hA] at hsim
  obtain ⟨m', hM, hrel⟩ := hsim.miri_step_of_anneal_step
  exact ⟨m', rfl, hM, hrel⟩

/-- **`wit_lm4_2_assume_false`**: `assume(false)` is undefined behavior in both
machines. -/
theorem wit_lm4_2_assume_false :
    stepMirFn (assumeBody (.constant (constBool false)))
        (assumeAnnealPre (.constant (constBool false))) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
        (annealStepHooks (assumeBody (.constant (constBool false))).localDecls
          (assumeBody (.constant (constBool false))).layouts) ()
        (assumeMiriPre (.constant (constBool false))) = (m', .error (.undefinedBehavior msg)) := by
  have hsim := step_intrinsic_assume_simulation (assume_stateRel (.constant (constBool false)))
    (by intro p h; cases h) (bb := assumeBB (.constant (constBool false)))
    rfl rfl (fun tf _ => constBool_wellTyped false tf) (Or.inl rfl) rfl
  have hA : stepMirFn (assumeBody (.constant (constBool false)))
      (assumeAnnealPre (.constant (constBool false))) = .fail .ub := rfl
  rw [hA] at hsim
  exact ⟨rfl, hsim.miri_ub_of_anneal_ub⟩

/-- `_1` is an immediate local of `assumeMiriPre op`. -/
theorem assume_local1_immediate (op : MirAst.Operand) :
    ∀ tf, (assumeMiriPre op).stack.frames = #[tf] → IsImmediateFrameLocal tf 1 := by
  intro tf h
  injection h with h₁
  injection h₁ with h₂
  subst h₂
  intro mls hmls mp hmp
  simp [assumeMiriFrame] at hmls
  subst hmls
  cases hmp

/-- **`wit_lm4_2_assume_invalid_bool`**: `assume(copy _1)` with `_1 = 2_u8`, an
invalid `bool` bit pattern, is undefined behavior in both machines (Anneal
requires the scalar `1`; `lean-miri`'s `Scalar.toBool` reports `invalidBool`). -/
theorem wit_lm4_2_assume_invalid_bool :
    stepMirFn (assumeBody (.copy (local42 1))) (assumeAnnealPre (.copy (local42 1))) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
        (annealStepHooks (assumeBody (.copy (local42 1))).localDecls
          (assumeBody (.copy (local42 1))).layouts) ()
        (assumeMiriPre (.copy (local42 1))) = (m', .error (.undefinedBehavior msg)) := by
  have hsim := step_intrinsic_assume_simulation (assume_stateRel (.copy (local42 1)))
    (by intro p h; cases h) (bb := assumeBB (.copy (local42 1))) (ty := tyOf (.uint .u8))
    rfl rfl
    (fun tf h => .copyLocal 1 (declOf (.uint .u8)) rfl (by decide)
      (assume_local1_immediate _ tf h))
    (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) rfl
  have hA : stepMirFn (assumeBody (.copy (local42 1))) (assumeAnnealPre (.copy (local42 1))) =
      .fail .ub := rfl
  rw [hA] at hsim
  exact ⟨rfl, hsim.miri_ub_of_anneal_ub⟩

/-! ## 3. Intrinsic calls -/

/-- The entry block of `callBody`: `_0 = path::<argKind>(args) -> bb1`. -/
def callBB0 (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand) : BasicBlockData :=
  { statements := []
    terminator := mkTerm42
      (.call (.constant (fnItem path argKind)) args (local42 0) (some 1) .unreachable)
    isCleanup := false }

/-- `bb0: _0 = path::<argKind>(args) -> bb1; bb1: return` with `_0 : dstKind`. -/
def callBody (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) : CapturedMir where
  defPath := "lm_4_2_witness::call"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf dstKind]
  basicBlocks := [callBB0 path argKind args,
    { statements := [], terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := fnAbi42
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal state at the call (`_0` uninitialized). -/
def callAnnealPre (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
    memory := (initMachineState (callBody path argKind args dstKind) []).memory }

/-- Anneal state after a call that wrote `v` to `_0` and returned to `bb1`. -/
def callAnnealPost (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) (v : Value) : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [.init v] }
    memory := (initMachineState (callBody path argKind args dstKind) []).memory }

def callMiriFrame (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (callBody path argKind args dstKind)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (tyOf dstKind)) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def callMiriPre (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) : AnnealStepState :=
  { stack := ⟨#[callMiriFrame path argKind args dstKind]⟩, machine := AnnealMachine.empty }

theorem call_stateRel (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) :
    StateRelLM3_1 (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind)
      (callMiriPre path argKind args dstKind) [] := by
  refine StateRel.toLM3_1 (StateRel.mk (callMiriFrame path argKind args dstKind) rfl rfl
    ⟨translateTy (tyOf dstKind), rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | _ + 1 => rintro ⟨⟩))
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = declOf dstKind := by simpa [callBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [callAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [callMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | n + 1 =>
    simp [callBody, get?] at hdecl

theorem call_dst_immediate (path : DefPath) (argKind : RigidTy) (args : List MirAst.Operand)
    (dstKind : RigidTy) :
    ∀ tf, (callMiriPre path argKind args dstKind).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 := by
  intro tf h
  injection h with h₁
  injection h₁ with h₂
  subst h₂
  intro mls hmls mp hmp
  simp [callMiriFrame] at hmls
  subst hmls
  cases hmp

/-- A well-typed integer constant. -/
theorem constInt_wellTyped {k : RigidTy} {kind : Miri.MIR.IntegerKind}
    (hk : IsIntegralTy (tyOf k) kind) {bits size : Nat} (hsize : ValidScalarBytes size)
    (hbits : bits < scalarModulus size)
    (hsz : (translateTy (tyOf k) emptyLayoutTable).layout.size = translateSizeBytes size)
    (body : CapturedMir) (hly : body.layouts = emptyLayoutTable)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand body tf (.constant (constInt k bits size)) (tyOf k) := by
  refine .constScalar (constInt k bits size) ⟨bits, size⟩ rfl hk.prim hsize hbits ?_
    (fun h => absurd h hk.ne_bool) (fun h => absurd h hk.ne_char)
  rw [hly]; exact hsz

def u32K : RigidTy := .uint .u32
def u8K : RigidTy := .uint .u8
def i8K : RigidTy := .int .i8

theorem u32_integral : IsIntegralTy (tyOf u32K) .u32 := .uint .u32 rfl
theorem u8_integral : IsIntegralTy (tyOf u8K) .u8 := .uint .u8 rfl
theorem i8_integral : IsIntegralTy (tyOf i8K) .i8 := .int .i8 rfl

/-- One-operand bit-intrinsic call fixture: `_0 = op::<T>(const x)`. -/
abbrev bitArgs (k : RigidTy) (x size : Nat) : List MirAst.Operand := [.constant (constInt k x size)]

/-- **`wit_lm4_2_ctpop`**: `ctpop::<u32>(0b1011)` writes `3_u32` to `_0` and
returns to `bb1` in both machines, from and to `StateRelLM3_1`-related
states. -/
theorem wit_lm4_2_ctpop :
    ∃ m', stepMirFn (callBody "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K)
        (callAnnealPre "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K) =
        .step (callAnnealPost "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K
          (.scalar ⟨3, 4⟩)) ∧
      Miri.Interpreter.Step.step
        (annealStepHooks (callBody "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K).localDecls
          (callBody "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K).layouts) ()
        (callMiriPre "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K) = (m', .ok true) ∧
      StateRelLM3_1 (callBody "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K)
        (callAnnealPost "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K (.scalar ⟨3, 4⟩))
        m' [] := by
  have hsim := call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h)
    (bb := callBB0 "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4)) rfl rfl rfl .ctpop rfl
    u32_integral rfl rfl (Or.inl (by decide))
    (fun tf _ => constInt_wellTyped u32_integral (Or.inr (Or.inr (Or.inl rfl))) (by decide) rfl
      _ rfl tf)
    rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h)
    (call_dst_immediate _ _ _ _)
  have hA : stepMirFn (callBody "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K)
      (callAnnealPre "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K) =
      .step (callAnnealPost "core::intrinsics::ctpop" u32K (bitArgs u32K 11 4) u32K
        (.scalar ⟨3, 4⟩)) := rfl
  rw [hA] at hsim
  obtain ⟨m', hM, hrel⟩ := hsim.miri_step_of_anneal_step
  exact ⟨m', rfl, hM, hrel⟩

/-- Extract a lockstep step witness from a call simulation whose Anneal side
steps to `callAnnealPost … v`. -/
theorem call_witness_of_step {path : DefPath} {argKind : RigidTy} {args : List MirAst.Operand}
    {dstKind : RigidTy} {v : Value}
    (hsim : StepRelLM3_1 (callBody path argKind args dstKind) (callMiriPre path argKind args dstKind)
      [] (stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind))
      (Miri.Interpreter.Step.step
        (annealStepHooks (callBody path argKind args dstKind).localDecls
          (callBody path argKind args dstKind).layouts) ()
        (callMiriPre path argKind args dstKind)))
    (hA : stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind) =
      .step (callAnnealPost path argKind args dstKind v)) :
    stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind) =
        .step (callAnnealPost path argKind args dstKind v) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody path argKind args dstKind).localDecls
            (callBody path argKind args dstKind).layouts) ()
          (callMiriPre path argKind args dstKind) = (m', .ok true) ∧
        StateRelLM3_1 (callBody path argKind args dstKind)
          (callAnnealPost path argKind args dstKind v) m' [] := by
  rw [hA] at hsim
  exact ⟨hA, hsim.miri_step_of_anneal_step⟩

/-- Extract a lockstep undefined-behavior witness from a call simulation whose
Anneal side reports undefined behavior. -/
theorem call_witness_of_ub {path : DefPath} {argKind : RigidTy} {args : List MirAst.Operand}
    {dstKind : RigidTy}
    (hsim : StepRelLM3_1 (callBody path argKind args dstKind) (callMiriPre path argKind args dstKind)
      [] (stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind))
      (Miri.Interpreter.Step.step
        (annealStepHooks (callBody path argKind args dstKind).localDecls
          (callBody path argKind args dstKind).layouts) ()
        (callMiriPre path argKind args dstKind)))
    (hA : stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind) =
      .fail .ub) :
    stepMirFn (callBody path argKind args dstKind) (callAnnealPre path argKind args dstKind) =
        .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody path argKind args dstKind).localDecls
            (callBody path argKind args dstKind).layouts) ()
          (callMiriPre path argKind args dstKind) = (m', .error (.undefinedBehavior msg)) := by
  rw [hA] at hsim
  exact ⟨hA, hsim.miri_ub_of_anneal_ub⟩

/-- Two-operand integer call fixture: `_0 = op::<T>(const a, const b)`. -/
abbrev binArgs (k : RigidTy) (a b size : Nat) : List MirAst.Operand :=
  [.constant (constInt k a size), .constant (constInt k b size)]

theorem valid4 : ValidScalarBytes 4 := Or.inr (Or.inr (Or.inl rfl))
theorem valid1 : ValidScalarBytes 1 := Or.inl rfl

/-- **`wit_lm4_2_ctlz`**: `ctlz::<u32>(1)` writes `31_u32` in both machines. -/
theorem wit_lm4_2_ctlz :
    stepMirFn (callBody "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K) (callAnnealPre "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K) = .step (callAnnealPost "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K (.scalar ⟨31, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K).localDecls (callBody "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K).layouts) () (callMiriPre "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K) (callAnnealPost "core::intrinsics::ctlz" u32K (bitArgs u32K 1 4) u32K (.scalar ⟨31, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .ctlz rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_cttz`**: `cttz::<u32>(8)` writes `3_u32` in both machines. -/
theorem wit_lm4_2_cttz :
    stepMirFn (callBody "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K) (callAnnealPre "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K) = .step (callAnnealPost "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K (.scalar ⟨3, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K).localDecls (callBody "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K).layouts) () (callMiriPre "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K) (callAnnealPost "core::intrinsics::cttz" u32K (bitArgs u32K 8 4) u32K (.scalar ⟨3, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .cttz rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_bswap`**: `bswap::<u32>(0x12345678)` writes `0x78563412_u32` in both machines. -/
theorem wit_lm4_2_bswap :
    stepMirFn (callBody "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K) (callAnnealPre "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K) = .step (callAnnealPost "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K (.scalar ⟨2018915346, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K).localDecls (callBody "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K).layouts) () (callMiriPre "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K) (callAnnealPost "core::intrinsics::bswap" u32K (bitArgs u32K 305419896 4) u32K (.scalar ⟨2018915346, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .bswap rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inl (Or.inl rfl)) (fun _ => rfl) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_bitreverse`**: `bitreverse::<u8>(1)` writes `128_u8` in both machines. -/
theorem wit_lm4_2_bitreverse :
    stepMirFn (callBody "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K) (callAnnealPre "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K) = .step (callAnnealPost "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K (.scalar ⟨128, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K).localDecls (callBody "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K).layouts) () (callMiriPre "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K) (callAnnealPost "core::intrinsics::bitreverse" u8K (bitArgs u8K 1 1) u8K (.scalar ⟨128, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .bitreverse rfl u8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) rfl u8_integral (Or.inl (Or.inr rfl)) (fun _ => rfl) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_ctlz_nonzero_zero_ub`**: `ctlz_nonzero::<u32>(0)` is undefined behavior in both machines. -/
theorem wit_lm4_2_ctlz_nonzero_zero_ub :
    stepMirFn (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 0 4) u32K) (callAnnealPre "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 0 4) u32K) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 0 4) u32K).localDecls (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 0 4) u32K).layouts) () (callMiriPre "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 0 4) u32K) =
        (m', .error (.undefinedBehavior msg)) :=
  call_witness_of_ub (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .ctlzNonzero rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_cttz_nonzero_zero_ub`**: `cttz_nonzero::<u32>(0)` is undefined behavior in both machines. -/
theorem wit_lm4_2_cttz_nonzero_zero_ub :
    stepMirFn (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 0 4) u32K) (callAnnealPre "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 0 4) u32K) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 0 4) u32K).localDecls (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 0 4) u32K).layouts) () (callMiriPre "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 0 4) u32K) =
        (m', .error (.undefinedBehavior msg)) :=
  call_witness_of_ub (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .cttzNonzero rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_ctlz_nonzero_ok`**: `ctlz_nonzero::<u32>(1)` writes `31_u32` in lockstep in both machines. -/
theorem wit_lm4_2_ctlz_nonzero_ok :
    stepMirFn (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K) (callAnnealPre "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K) = .step (callAnnealPost "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K (.scalar ⟨31, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K).localDecls (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K).layouts) () (callMiriPre "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K) (callAnnealPost "core::intrinsics::ctlz_nonzero" u32K (bitArgs u32K 1 4) u32K (.scalar ⟨31, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .ctlzNonzero rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_cttz_nonzero_ok`**: `cttz_nonzero::<u32>(8)` writes `3_u32` in lockstep in both machines. -/
theorem wit_lm4_2_cttz_nonzero_ok :
    stepMirFn (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K) (callAnnealPre "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K) = .step (callAnnealPost "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K (.scalar ⟨3, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K).localDecls (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K).layouts) () (callMiriPre "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K) (callAnnealPost "core::intrinsics::cttz_nonzero" u32K (bitArgs u32K 8 4) u32K (.scalar ⟨3, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_bitcount_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl .cttzNonzero rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (Or.inr rfl) (by intro h; rcases h with h | h <;> cases h) (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_add`**: `saturating_add::<u8>(100, 27)` writes `127_u8` (no saturation) in both machines. -/
theorem wit_lm4_2_saturating_add :
    stepMirFn (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K) (callAnnealPre "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K) = .step (callAnnealPost "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K (.scalar ⟨127, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K).localDecls (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K).layouts) () (callMiriPre "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K) (callAnnealPost "core::intrinsics::saturating_add" u8K (binArgs u8K 100 27 1) u8K (.scalar ⟨127, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl u8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) rfl u8_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_add_max`**: `saturating_add::<u8>(250, 10)` saturates at `u8::MAX = 255` in both machines. -/
theorem wit_lm4_2_saturating_add_max :
    stepMirFn (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K) (callAnnealPre "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K) = .step (callAnnealPost "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K (.scalar ⟨255, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K).localDecls (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K).layouts) () (callMiriPre "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K) (callAnnealPost "core::intrinsics::saturating_add" u8K (binArgs u8K 250 10 1) u8K (.scalar ⟨255, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl u8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) rfl u8_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_add_signed_max`**: `saturating_add::<i8>(100, 100)` saturates at `i8::MAX = 127` in both machines. -/
theorem wit_lm4_2_saturating_add_signed_max :
    stepMirFn (callBody "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K) (callAnnealPre "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K) = .step (callAnnealPost "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K (.scalar ⟨127, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K).localDecls (callBody "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K).layouts) () (callMiriPre "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K) (callAnnealPost "core::intrinsics::saturating_add" i8K (binArgs i8K 100 100 1) i8K (.scalar ⟨127, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl i8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped i8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped i8_integral valid1 (by decide) rfl _ rfl tf) rfl i8_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_sub`**: `saturating_sub::<u8>(10, 3)` writes `7_u8` (no saturation) in both machines. -/
theorem wit_lm4_2_saturating_sub :
    stepMirFn (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K) (callAnnealPre "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K) = .step (callAnnealPost "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K (.scalar ⟨7, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K).localDecls (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K).layouts) () (callMiriPre "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K) (callAnnealPost "core::intrinsics::saturating_sub" u8K (binArgs u8K 10 3 1) u8K (.scalar ⟨7, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inr ⟨rfl, rfl⟩) rfl u8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) rfl u8_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_sub_zero`**: `saturating_sub::<u8>(5, 10)` saturates at `0` in both machines. -/
theorem wit_lm4_2_saturating_sub_zero :
    stepMirFn (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K) (callAnnealPre "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K) = .step (callAnnealPost "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K (.scalar ⟨0, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K).localDecls (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K).layouts) () (callMiriPre "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K) (callAnnealPost "core::intrinsics::saturating_sub" u8K (binArgs u8K 5 10 1) u8K (.scalar ⟨0, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inr ⟨rfl, rfl⟩) rfl u8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u8_integral valid1 (by decide) rfl _ rfl tf) rfl u8_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_saturating_sub_min`**: `saturating_sub::<i8>(-100, 100)` saturates at `i8::MIN = -128` (bit pattern `128`) in both machines. -/
theorem wit_lm4_2_saturating_sub_min :
    stepMirFn (callBody "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K) (callAnnealPre "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K) = .step (callAnnealPost "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K (.scalar ⟨128, 1⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K).localDecls (callBody "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K).layouts) () (callMiriPre "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K) (callAnnealPost "core::intrinsics::saturating_sub" i8K (binArgs i8K 156 100 1) i8K (.scalar ⟨128, 1⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_saturating_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl (Or.inr ⟨rfl, rfl⟩) rfl i8_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped i8_integral valid1 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped i8_integral valid1 (by decide) rfl _ rfl tf) rfl i8_integral (call_dst_immediate _ _ _ _)) rfl

def i32K : RigidTy := .int .i32
theorem i32_integral : IsIntegralTy (tyOf i32K) .i32 := .int .i32 rfl

/-- **`wit_lm4_2_exact_div_signed`**: `exact_div::<i32>(-42, 7)` writes `-6_i32` (bit pattern `2^32 - 6`) in both machines. -/
theorem wit_lm4_2_exact_div_signed :
    stepMirFn (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K) (callAnnealPre "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K) = .step (callAnnealPost "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K (.scalar ⟨4294967290, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K).localDecls (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K).layouts) () (callMiriPre "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K) (callAnnealPost "core::intrinsics::exact_div" i32K (binArgs i32K 4294967254 7 4) i32K (.scalar ⟨4294967290, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_exact_div_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl rfl i32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped i32_integral valid4 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped i32_integral valid4 (by decide) rfl _ rfl tf) rfl i32_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_exact_div_unsigned`**: `exact_div::<u32>(42, 7)` writes `6_u32` in both machines. -/
theorem wit_lm4_2_exact_div_unsigned :
    stepMirFn (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K) (callAnnealPre "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K) = .step (callAnnealPost "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K (.scalar ⟨6, 4⟩)) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K).localDecls (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K).layouts) () (callMiriPre "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K) = (m', .ok true) ∧
        StateRelLM3_1 (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K) (callAnnealPost "core::intrinsics::exact_div" u32K (binArgs u32K 42 7 4) u32K (.scalar ⟨6, 4⟩)) m' [] :=
  call_witness_of_step (call_intrinsic_exact_div_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_exact_div_by_zero_ub`**: `exact_div::<u32>(7, 0)` is undefined behavior in both machines. -/
theorem wit_lm4_2_exact_div_by_zero_ub :
    stepMirFn (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 0 4) u32K) (callAnnealPre "core::intrinsics::exact_div" u32K (binArgs u32K 7 0 4) u32K) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 0 4) u32K).localDecls (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 0 4) u32K).layouts) () (callMiriPre "core::intrinsics::exact_div" u32K (binArgs u32K 7 0 4) u32K) =
        (m', .error (.undefinedBehavior msg)) :=
  call_witness_of_ub (call_intrinsic_exact_div_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_exact_div_min_neg_one_ub`**: `exact_div::<i32>(i32::MIN, -1)` is undefined behavior in both machines. -/
theorem wit_lm4_2_exact_div_min_neg_one_ub :
    stepMirFn (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 2147483648 4294967295 4) i32K) (callAnnealPre "core::intrinsics::exact_div" i32K (binArgs i32K 2147483648 4294967295 4) i32K) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 2147483648 4294967295 4) i32K).localDecls (callBody "core::intrinsics::exact_div" i32K (binArgs i32K 2147483648 4294967295 4) i32K).layouts) () (callMiriPre "core::intrinsics::exact_div" i32K (binArgs i32K 2147483648 4294967295 4) i32K) =
        (m', .error (.undefinedBehavior msg)) :=
  call_witness_of_ub (call_intrinsic_exact_div_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl rfl i32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped i32_integral valid4 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped i32_integral valid4 (by decide) rfl _ rfl tf) rfl i32_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_exact_div_remainder_ub`**: `exact_div::<u32>(7, 2)` (remainder `1`) is undefined behavior in both machines. -/
theorem wit_lm4_2_exact_div_remainder_ub :
    stepMirFn (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 2 4) u32K) (callAnnealPre "core::intrinsics::exact_div" u32K (binArgs u32K 7 2 4) u32K) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 2 4) u32K).localDecls (callBody "core::intrinsics::exact_div" u32K (binArgs u32K 7 2 4) u32K).layouts) () (callMiriPre "core::intrinsics::exact_div" u32K (binArgs u32K 7 2 4) u32K) =
        (m', .error (.undefinedBehavior msg)) :=
  call_witness_of_ub (call_intrinsic_exact_div_simulation (call_stateRel _ _ _ _) (by intro p h; cases h) (bb := callBB0 _ _ _) rfl rfl rfl rfl u32_integral rfl rfl (Or.inl (by decide)) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl u32_integral (call_dst_immediate _ _ _ _)) rfl

/-- **`wit_lm4_2_rotate_left_divergence`**: `rotate_left::<u32>(0x80000001, 1)`: Anneal writes `3_u32` and returns to `bb1`, while the real `lean-miri` step fails closed (`StepError.unsupported`: the pinned dispatcher leaves `rotate_left` to its MIR fallback body). -/
theorem wit_lm4_2_rotate_left_divergence :
    stepMirFnLM4_2 (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) = .step (callAnnealPost "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K (.scalar ⟨3, 4⟩)) ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K).localDecls (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K).layouts) () (callMiriPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) =
        (m', .error (.unsupported msg)) := by
  have hrot := call_intrinsic_rotate_simulation
    (call_stateRel "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) (by intro p h; cases h)
    (bb := callBB0 "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4)) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl u32_integral u32_integral rfl rfl
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf)
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl
  have hA : stepMirFnLM4_2 (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K) = .step (callAnnealPost "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 1 4) u32K (.scalar ⟨3, 4⟩)) := rfl
  refine ⟨hA, ?_⟩
  rcases hrot with ⟨hunsup, _⟩ | ⟨_, _, _, hub⟩
  · exact hunsup
  · rw [hA] at hub
    simp [MirStepNode.step, MirStepNode.fail] at hub

/-- **`wit_lm4_2_rotate_right_divergence`**: `rotate_right::<u32>(3, 1)`: Anneal writes `0x80000001_u32`, while the real `lean-miri` step fails closed (`StepError.unsupported`). -/
theorem wit_lm4_2_rotate_right_divergence :
    stepMirFnLM4_2 (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) = .step (callAnnealPost "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K (.scalar ⟨2147483649, 4⟩)) ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K).localDecls (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K).layouts) () (callMiriPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) =
        (m', .error (.unsupported msg)) := by
  have hrot := call_intrinsic_rotate_simulation
    (call_stateRel "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) (by intro p h; cases h)
    (bb := callBB0 "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4)) rfl rfl rfl (Or.inr ⟨rfl, rfl⟩) rfl u32_integral u32_integral rfl rfl
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf)
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl
  have hA : stepMirFnLM4_2 (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K) = .step (callAnnealPost "core::intrinsics::rotate_right" u32K (binArgs u32K 3 1 4) u32K (.scalar ⟨2147483649, 4⟩)) := rfl
  refine ⟨hA, ?_⟩
  rcases hrot with ⟨hunsup, _⟩ | ⟨_, _, _, hub⟩
  · exact hunsup
  · rw [hA] at hub
    simp [MirStepNode.step, MirStepNode.fail] at hub

/-- **`wit_lm4_2_rotate_left_mod_mask`**: `rotate_left::<u32>(0x80000001, 33)` exercises
modular shift masking (`33 % 32 = 1`): Anneal writes `3_u32` (`BitVec.rotateLeft` of
`0x80000001` by `33`), certified via `ScalarRel` (`truncateFromUInt`), while `lean-miri`
fails closed with `StepError.unsupported`. -/
theorem wit_lm4_2_rotate_left_mod_mask :
    stepMirFnLM4_2 (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K)
        (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K) =
      .step (callAnnealPost "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K (.scalar ⟨3, 4⟩)) ∧
    (∃ m' msg, Miri.Interpreter.Step.step
        (annealStepHooks (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K).localDecls
          (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K).layouts) ()
        (callMiriPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K) =
      (m', .error (.unsupported msg))) ∧
    ∃ mr,
      (BitVec.ofNat 32 2147483649).rotateLeft 33 = BitVec.ofNat 32 3 ∧
      ScalarRel ⟨3, 4⟩ mr ∧
      ∃ b, Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 3) (translateSizeBytes 4) = .ok (mr, b) := by
  have hrot := call_intrinsic_rotate_simulation
    (call_stateRel "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K) (by intro p h; cases h)
    (bb := callBB0 "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4)) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩)
    rfl u32_integral u32_integral rfl rfl
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf)
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl
  have hA : stepMirFnLM4_2 (callBody "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K)
      (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K) =
    .step (callAnnealPost "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K (.scalar ⟨3, 4⟩)) := rfl
  rcases hrot with ⟨hunsup, ⟨_, hub⟩ | ⟨x, shift, mr, hevals, _, _, _, _, hrel, htrunc⟩⟩ | ⟨_, _, _, hub⟩
  · rw [hA] at hub; cases hub
  · have hev0 : evalOperands
        (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K).frame.locals
        (binArgs u32K 2147483649 33 4) [] [] emptyLayoutTable [] =
      .ok [.scalar ⟨2147483649, 4⟩, .scalar ⟨33, 4⟩]
        (callAnnealPre "core::intrinsics::rotate_left" u32K (binArgs u32K 2147483649 33 4) u32K).frame.locals := rfl
    have heq := hevals.symm.trans hev0
    injection heq with hls _
    injection hls with hx hls'
    injection hx with hx'
    injection hls' with hs _
    injection hs with hs'
    subst hx' hs'
    exact ⟨hA, hunsup, mr, by decide, hrel, htrunc⟩
  · rw [hA] at hub; cases hub

/-- **`wit_lm4_2_rotate_right_mod_mask`**: `rotate_right::<u32>(3, 33)` exercises
modular shift masking (`33 % 32 = 1`): Anneal writes `0x80000001_u32` (`2147483649`),
certified via `BitVec.rotateRight` and `ScalarRel` (`truncateFromUInt`), while `lean-miri`
fails closed with `StepError.unsupported`. -/
theorem wit_lm4_2_rotate_right_mod_mask :
    stepMirFnLM4_2 (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K)
        (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K) =
      .step (callAnnealPost "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K (.scalar ⟨2147483649, 4⟩)) ∧
    (∃ m' msg, Miri.Interpreter.Step.step
        (annealStepHooks (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K).localDecls
          (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K).layouts) ()
        (callMiriPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K) =
      (m', .error (.unsupported msg))) ∧
    ∃ mr,
      (BitVec.ofNat 32 3).rotateRight 33 = BitVec.ofNat 32 2147483649 ∧
      ScalarRel ⟨2147483649, 4⟩ mr ∧
      ∃ b, Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 2147483649) (translateSizeBytes 4) = .ok (mr, b) := by
  have hrot := call_intrinsic_rotate_simulation
    (call_stateRel "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K) (by intro p h; cases h)
    (bb := callBB0 "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4)) rfl rfl rfl (Or.inr ⟨rfl, rfl⟩)
    rfl u32_integral u32_integral rfl rfl
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf)
    (fun tf _ => constInt_wellTyped u32_integral valid4 (by decide) rfl _ rfl tf) rfl
  have hA : stepMirFnLM4_2 (callBody "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K)
      (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K) =
    .step (callAnnealPost "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K (.scalar ⟨2147483649, 4⟩)) := rfl
  rcases hrot with ⟨hunsup, ⟨_, hub⟩ | ⟨x, shift, mr, hevals, _, _, _, _, hrel, htrunc⟩⟩ | ⟨_, _, _, hub⟩
  · rw [hA] at hub; cases hub
  · have hev0 : evalOperands
        (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K).frame.locals
        (binArgs u32K 3 33 4) [] [] emptyLayoutTable [] =
      .ok [.scalar ⟨3, 4⟩, .scalar ⟨33, 4⟩]
        (callAnnealPre "core::intrinsics::rotate_right" u32K (binArgs u32K 3 33 4) u32K).frame.locals := rfl
    have heq := hevals.symm.trans hev0
    injection heq with hls _
    injection hls with hx hls'
    injection hx with hx'
    injection hls' with hs _
    injection hs with hs'
    subst hx' hs'
    exact ⟨hA, hunsup, mr, by decide, hrel, htrunc⟩
  · rw [hA] at hub; cases hub

/-! ## 4. `arith_offset` / `wrapping_offset` real-step witnesses -/

def isizeK : RigidTy := .int .isize
def usizeK : RigidTy := .uint .usize
def u64K : RigidTy := .uint .u64
def rawMutU64K : RigidTy := .rawPtr .mut u64K

theorem isize_integral : IsIntegralTy (tyOf isizeK) .isize := .int .isize rfl
theorem usize_integral : IsIntegralTy (tyOf usizeK) .usize := .uint .usize rfl
theorem valid8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- Reusable 4-local MIR body (`_0 : d₀`, `_1 : u64`, `_2 : d₂`, `_3 : d₃`)
whose `bb0` runs `stmts` followed by `term0`, and whose `bb1` returns. -/
def ptr4Body (d₀ d₂ d₃ : RigidTy) (stmts : List MirAst.Statement) (term0 : TerminatorKind) :
    CapturedMir where
  defPath := "lm_4_2_witness::ptr4"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf d₀, declOf u64K, declOf d₂, declOf d₃]
  basicBlocks := [
    { statements := stmts, terminator := mkTerm42 term0, isCleanup := false },
    { statements := [], terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Pre-state of `ptr4Body` (`_1 = 42_u64`, all other locals `.uninit`). -/
def ptr4AnnealPre (b : CapturedMir) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState b []).memory }

/-- Construct an Anneal `MachineState` for `b` at `(bbIdx, stmtIdx)`. -/
def mkPtrState (b : CapturedMir) (bbIdx stmtIdx : Nat) (locals : List LocalSlot)
    (borrows : List BorrowEntry) (nextTag : Nat) : MachineState :=
  { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState b []).memory with borrows := borrows, nextTag := nextTag } }

def ptr4MiriFramePre (b : CapturedMir) (d₀ : RigidTy) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody b
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (tyOf d₀)) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (tyOf u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def ptr4MiriPre (b : CapturedMir) (d₀ : RigidTy) : AnnealStepState :=
  { stack := ⟨#[ptr4MiriFramePre b d₀]⟩, machine := AnnealMachine.empty }

theorem ptr4_all_immediate (b : CapturedMir) (d₀ : RigidTy) :
    ∀ tf, (ptr4MiriPre b d₀).stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 => simp [ptr4MiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 4 => simp [ptr4MiriFramePre] at hmls

theorem ptr4_stateRel (d₀ d₂ d₃ : RigidTy) (stmts : List MirAst.Statement)
    (term0 : TerminatorKind) :
    StateRel (ptr4Body d₀ d₂ d₃ stmts term0)
      (ptr4AnnealPre (ptr4Body d₀ d₂ d₃ stmts term0))
      (ptr4MiriPre (ptr4Body d₀ d₂ d₃ stmts term0) d₀) := by
  let b := ptr4Body d₀ d₂ d₃ stmts term0
  refine StateRel.mk (ptr4MiriFramePre b d₀) rfl rfl ⟨translateTy (tyOf d₀), rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [ptr4AnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [ptr4MiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = declOf u64K := by simpa [b, ptr4Body, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [ptr4AnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
          layout := some (translateTy (tyOf u64K)) } := by
      simpa [ptr4MiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (tyOf u64K))) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 4 => simp [ptr4Body, get?] at hdecl

/-- `arith_offset::<u64>(copy ptrIdx, const count_isize) -> bb1` into `_0`. -/
def arithOffsetTerm (ptrIdx : Local) (countBits : Nat) : TerminatorKind :=
  .call (.constant (fnItem "core::intrinsics::arith_offset" u64K))
    [.copy (local42 ptrIdx), .constant (constInt isizeK countBits 8)]
    (local42 0) (some 1) .unreachable

/-- Body for positive `arith_offset`: `_2 = &raw mut _1; _0 = arith_offset(copy _2, 5_isize)`. -/
def arithOffsetPosBody : CapturedMir :=
  ptr4Body rawMutU64K rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))]
    (arithOffsetTerm 2 5)

/-- **`wit_lm4_2_arith_offset_pos`**: real 2-step execution of `_2 = &raw mut _1`
followed by `_0 = core::intrinsics::arith_offset::<u64>(copy _2, 5_isize) -> bb1`.
Even though `5 * 8 = 40` bytes lies past the end of the 8-byte stack allocation
of `_1` (where `BinOp.Offset` would report undefined behavior), both machines
step in lockstep to `StateRelLM3_1`-related states with `_0` holding
`{ allocId := 1, offsetBytes := 40 }` and preserving provenance (`lm31AllocId1`). -/
theorem wit_lm4_2_arith_offset_pos :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := arithOffsetPosBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b rawMutU64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 0 = some (.init (.ptr { allocId := 1, offsetBytes := 40 } 8)) := by
  let b := arithOffsetPosBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b rawMutU64K) :=
    ptr4_stateRel rawMutU64K rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))] (arithOffsetTerm 2 5)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 1 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := call_intrinsic_arithOffset_stage1_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
    isize_integral (fun tf₁ _ => constInt_wellTyped isize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 0 (by decide)) rfl rfl (by decide)
    (fun p countSc hp hc _ => by
      have hp' : p = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨5, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hp' hc'
      decide)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl⟩

def rawMutU8K : RigidTy := .rawPtr .mut u8K

private theorem stepMirFn_binOp_offset_const_eq
    {body : CapturedMir} {s s' : MachineState}
    {bb : BasicBlockData} {dstIdx : Local}
    {op_lhs : MirAst.Operand} {c : ConstOperand} {span : String}
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt} {stride : Nat}
    (e : AllocMapEntry) (tgtDecl : LocalDecl) {slot_t slot_d : LocalSlot}
    {locals_mid : List LocalSlot}
    (hphase : ∀ p, body.phase ≠ .other p)
    (htgt_prim : IsPrimScalarTy tgtDecl.ty)
    (hcal : s.memory.activeCallee = none := by rfl)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb := by rfl)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset op_lhs (.constant c)), span⟩ := by rfl)
    (hop_lhs : evalOperand s.frame.locals op_lhs s.memory.borrows
      s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
      .ok (.ptr ptrVal 8) locals_mid := by rfl)
    (hc : c.val = .scalar (.int sc) := by rfl)
    (hsz8 : sc.sizeBytes = 8 := by rfl)
    (hbor : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by rfl)
    (hstride : pointeeElemByteStride body.localDecls body.layouts op_lhs =
      some stride := by rfl)
    (htgt_decl : get? body.localDecls e.localIdx = some tgtDecl := by rfl)
    (hslot_t : get? locals_mid e.localIdx = some slot_t := by rfl)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl)
    (hslot_d : get? locals_mid dstIdx = some slot_d := by rfl)
    (hset_d : set? locals_mid dstIdx
      (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits * stride } 8)) =
      some s'.frame.locals := by rfl)
    (hprot : s.memory.activeProtectors = .nil := by rfl)
    (hs' : advanceStmt s s'.frame.locals
      { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstIdx none
        activeProtectors := .nil } = s' := by rfl)
    (hperm : e.perm ≠ .disabled := by rintro ⟨⟩)
    (hstride_le : stride ≤ 16 := by decide)
    (hbits_lt : sc.bits < 2 ^ 32 := by decide)
    (hoff_lt : ptrVal.offsetBytes < 2 ^ 32 := by decide)
    (hinb : (sc.bits = 0 ∧ ptrVal.offsetBytes = 0) ∨
      (slot_t ≠ .dead ∧
        ptrVal.offsetBytes + sc.bits * stride ≤
          (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat) := by
      exact Or.inr ⟨by decide, by decide⟩)
    (hd_ne : slot_d ≠ .dead := by decide) :
    stepMirFn body s = .step s' := by
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  unfold evalStmt evalRvalue
  dsimp only []
  rw [hop_lhs]
  dsimp only []
  have hop_rhs : evalOperand locals_mid (.constant c) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.scalar sc) locals_mid := by
    unfold evalOperand evalConstValue; dsimp only []; rw [hc]
  rw [hop_rhs]
  dsimp only []
  rw [evalPtrOffsetBinOp_allocMap_ok hbor hperm hstride hstride_le htgt_decl htgt_prim hslot_t
    hsz8 hbits_lt hoff_lt hptr8 hinb]
  dsimp only []
  rw [hslot_d]
  cases slot_d with
  | dead => exact absurd rfl hd_ne
  | uninit => simp only [hset_d, hprot, hs']
  | init _ => simp only [hset_d, hprot, hs']

/-- Body for negative `arith_offset`: `_2 = &raw mut _1`, `_3 = copy _2 as *mut u8`,
`_3 = Offset(copy _3, 8_usize)`, `_2 = copy _3 as *mut u64`, then
`_0 = arith_offset::<u64>(copy _2, -1_isize)` (`2^64 - 1`). -/
def arithOffsetNegBody : CapturedMir :=
  ptr4Body rawMutU64K rawMutU64K rawMutU8K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 3)
       (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 8 8)))),
     mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K)))]
    (arithOffsetTerm 2 18446744073709551615)

/-- **`wit_lm4_2_arith_offset_neg`**: real 5-step execution advancing `_2` to
one-past-end (`offsetBytes = 8`) and then calling
`core::intrinsics::arith_offset::<u64>(copy _2, -1_isize)` (`count = 2^64 - 1`,
stride `8`), wrapping two's-complement 64-bit arithmetic back to
`offsetBytes = 0` while preserving `StateRelLM3_1` and provenance
(`lm31AllocId1`). -/
theorem wit_lm4_2_arith_offset_neg :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := arithOffsetNegBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b rawMutU64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      get? s₅.frame.locals 0 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) := by
  let b := arithOffsetNegBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b rawMutU64K) :=
    ptr4_stateRel rawMutU64K rawMutU64K rawMutU8K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
       mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 3)
         (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 8 8)))),
       mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K)))]
      (arithOffsetTerm 2 18446744073709551615)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkPtrState b 0 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkPtrState b 0 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_3 = Offset(copy _3, 8_usize)`
  let s₃ := mkPtrState b 0 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr8]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 3 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
    (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨8, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constInt usizeK 8 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_2 = copy _3 as *mut u64`
  let s₄ := mkPtrState b 0 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr8, .init ptr8]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have hsim₄ := step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 2 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (fun _ h => by simp [s₃, mkPtrState, get?] at h)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  -- Step 5: `_0 = arith_offset::<u64>(copy _2, -1_isize) -> bb1`
  let s₅ := mkPtrState b 1 0 [.init ptr0, .init (.scalar ⟨42, 8⟩), .init ptr8, .init ptr8]
    [entry.toBorrowEntry] 2
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  have hsim₅ := call_intrinsic_arithOffset_stage1_simulation hrel₄ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 2 (by decide))
    (fun _ h => by simp [s₄, mkPtrState, ptr8, get?] at h)
    isize_integral (fun tf₄ _ => constInt_wellTyped isize_integral valid8 (by decide) rfl b rfl tf₄)
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 0 (by decide)) rfl rfl (by decide)
    (fun p countSc hp hc _ => by
      have hp' : p = { allocId := 1, offsetBytes := 8 } := by
        simpa [s₄, mkPtrState, ptr8, get?] using hp.symm
      have hc' : countSc = ⟨18446744073709551615, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hp' hc'
      decide)
  rw [hs₅] at hsim₅
  obtain ⟨m₅, hm₅, hrel₅⟩ := hsim₅.miri_step_of_anneal_step
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅, rfl⟩

/-- **`wit_lm4_2_arith_offset_uninit_ub`**: calling `arith_offset` on an
uninitialized pointer local `_2` reports undefined behavior in both machines. -/
theorem wit_lm4_2_arith_offset_uninit_ub :
    let b := ptr4Body rawMutU64K rawMutU64K rawMutU64K [] (arithOffsetTerm 2 1)
    stepMirFn b (ptr4AnnealPre b) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) ()
          (ptr4MiriPre b rawMutU64K) = (m', .error (.undefinedBehavior msg)) := by
  let b := ptr4Body rawMutU64K rawMutU64K rawMutU64K [] (arithOffsetTerm 2 1)
  have hrel₀ := (ptr4_stateRel rawMutU64K rawMutU64K rawMutU64K [] (arithOffsetTerm 2 1)).toLM3_1
  have hsim := call_intrinsic_arithOffset_stage1_simulation hrel₀ (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf htf => ptr4_all_immediate b _ tf htf 2)
    (fun _ h => by simp [ptr4AnnealPre, get?] at h)
    isize_integral (fun tf _ => constInt_wellTyped isize_integral valid8 (by decide) rfl b rfl tf)
    rfl rfl (fun tf htf => ptr4_all_immediate b _ tf htf 0) rfl rfl (by decide)
    (fun _ _ hp _ _ => by simp [ptr4AnnealPre, get?] at hp)
  have hA : stepMirFn b (ptr4AnnealPre b) = .fail .ub := rfl
  rw [hA] at hsim
  exact ⟨rfl, hsim.miri_ub_of_anneal_ub⟩

/-- `wrapping_offset::<u64>(copy ptrIdx, const count_isize) -> bb1` into `_0`. -/
def wrappingOffsetTerm (ptrIdx : Local) (countBits : Nat) : TerminatorKind :=
  .call (.constant (fnItem "core::intrinsics::wrapping_offset" u64K))
    [.copy (local42 ptrIdx), .constant (constInt isizeK countBits 8)]
    (local42 0) (some 1) .unreachable

/-- Body for positive `wrapping_offset`: `_2 = &raw mut _1; _0 = wrapping_offset(copy _2, 5_isize)`. -/
def wrappingOffsetPosBody : CapturedMir :=
  ptr4Body rawMutU64K rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))]
    (wrappingOffsetTerm 2 5)

/-- **`wit_lm4_2_wrapping_offset_ok`**: real 2-step execution of `_2 = &raw mut _1`
followed by `_0 = core::intrinsics::wrapping_offset::<u64>(copy _2, 5_isize) -> bb1`,
stepping in lockstep via `call_intrinsic_offset_simulation` (`k = .wrappingOffset`)
to `StateRelLM3_1`-related states with `_0 = .ptr { allocId := 1, offsetBytes := 40 } 8`. -/
theorem wit_lm4_2_wrapping_offset_ok :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := wrappingOffsetPosBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b rawMutU64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 0 = some (.init (.ptr { allocId := 1, offsetBytes := 40 } 8)) := by
  let b := wrappingOffsetPosBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b rawMutU64K) :=
    ptr4_stateRel rawMutU64K rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))] (wrappingOffsetTerm 2 5)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 1 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := rfl
  have hsim₂ := call_intrinsic_offset_simulation hrel₁ hphase rfl rfl rfl (Or.inr rfl) rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    isize_integral (fun tf₁ _ => constInt_wellTyped isize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 0 (by decide)) rfl rfl (by decide)
    (fun p countSc hp hc _ => by
      have hp' : p = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨5, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hp' hc'
      decide)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl⟩

/-- `std::intrinsics::wrapping_offset::<u64>(copy ptrIdx, const count_isize) -> bb1` into `_0`. -/
def stdWrappingOffsetTerm (ptrIdx : Local) (countBits : Nat) : TerminatorKind :=
  .call (.constant (fnItem "std::intrinsics::wrapping_offset" u64K))
    [.copy (local42 ptrIdx), .constant (constInt isizeK countBits 8)]
    (local42 0) (some 1) .unreachable

/-- Body for `"std::intrinsics::wrapping_offset"`:
`_2 = &raw mut _1; _0 = std::intrinsics::wrapping_offset::<u64>(copy _2, 5_isize)`. -/
def stdWrappingOffsetPosBody : CapturedMir :=
  ptr4Body rawMutU64K rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))]
    (stdWrappingOffsetTerm 2 5)

/-- **`wit_lm4_2_std_wrapping_offset_ok`**: real 2-step execution of
`_2 = &raw mut _1` followed by
`_0 = std::intrinsics::wrapping_offset::<u64>(copy _2, 5_isize) -> bb1`,
stepping in lockstep via `call_intrinsic_offset_simulation`
(`calleePath = "std::intrinsics::wrapping_offset"`, `k = .wrappingOffset`)
to `StateRelLM3_1`-related states with `_0 = .ptr { allocId := 1, offsetBytes := 40 } 8`. -/
theorem wit_lm4_2_std_wrapping_offset_ok :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := stdWrappingOffsetPosBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b rawMutU64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 0 = some (.init (.ptr { allocId := 1, offsetBytes := 40 } 8)) := by
  let b := stdWrappingOffsetPosBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b rawMutU64K) :=
    ptr4_stateRel rawMutU64K rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))] (stdWrappingOffsetTerm 2 5)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 1 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := rfl
  have hsim₂ := call_intrinsic_offset_simulation hrel₁ hphase rfl rfl rfl (Or.inr rfl) rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    isize_integral (fun tf₁ _ => constInt_wellTyped isize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 0 (by decide)) rfl rfl (by decide)
    (fun p countSc hp hc _ => by
      have hp' : p = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨5, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hp' hc'
      decide)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl⟩

/-! ## 5. `write_bytes` real-step witnesses -/

def unitK : RigidTy := .tuple []
def rawConstU64K : RigidTy := .rawPtr .not u64K

theorem u64_integral : IsIntegralTy (tyOf u64K) .u64 := .uint .u64 rfl

theorem u64_writeBytesPointee :
    WriteBytesPointee emptyLayoutTable (tyOf u64K).kind (encodeTyId (tyOf u64K)) 8 :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- `write_bytes::<u64>(copy ptrIdx, const val_u8, const count_usize) -> bb1` into `_0`. -/
def writeBytesTerm (ptrIdx : Local) (valBits countBits : Nat) : TerminatorKind :=
  .call (.constant (fnItem "core::intrinsics::write_bytes" u64K))
    [.copy (local42 ptrIdx),
     .constant (constInt u8K valBits 1),
     .constant (constInt usizeK countBits 8)]
    (local42 0) (some 1) .unreachable

/-- Body for `write_bytes` on `&raw mut _1` with constant `val` and `count`. -/
def writeBytesMutBody (valBits countBits : Nat) : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))]
    (writeBytesTerm 2 valBits countBits)

/-- **`wit_lm4_2_write_bytes_ok`**: real 2-step execution of `_2 = &raw mut _1`
followed by `core::intrinsics::write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb1`,
filling all 8 bytes of `_1` with `0xAB` (`0xABAB_ABAB_ABAB_ABAB = 12370169555311111083`)
and preserving `StateRelLM3_1` in both machines. -/
theorem wit_lm4_2_write_bytes_ok :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := writeBytesMutBody 0xAB 1
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) := by
  let b := writeBytesMutBody 0xAB 1
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))] (writeBytesTerm 2 0xAB 1)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 1 0
    [.uninit, .init (.scalar ⟨0xABABABABABABABAB, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := rfl
  have hsim₂ := call_intrinsic_write_bytes_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    u8_integral (fun tf₁ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₁)
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl u64_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, u64_integral⟩)
    (fun ptrVal countSc e tgtDecl tgtKind hp hc hpos _ he _ htgt ht _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hc' hd
        cases ht with
        | int _ hk => cases hk
        | uint ut hk =>
          cases ut <;> try cases hk
          refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
          intro x hx _
          cases hx with
          | tail _ h => cases h
          | head _ => exact Or.inl ⟨rfl, rfl⟩)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl⟩

/-- **`wit_lm4_2_write_bytes_oob_ub`**: real 2-step execution where
`write_bytes::<u64>(copy _2, 0xAB_u8, 2_usize)` attempts to write `16 > 8` bytes
into the 8-byte stack allocation of `_1`, triggering undefined behavior in both
machines. -/
theorem wit_lm4_2_write_bytes_oob_ub :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := writeBytesMutBody 0xAB 2
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  let b := writeBytesMutBody 0xAB 2
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))] (writeBytesTerm 2 0xAB 2)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  have hsim₂ := call_intrinsic_write_bytes_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    u8_integral (fun tf₁ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₁)
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl u64_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, u64_integral⟩)
    (fun ptrVal countSc e tgtDecl tgtKind hp hc _ _ he _ htgt ht _ hinb => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨2, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hc' hd
        cases ht with
        | int _ hk => cases hk
        | uint ut hk =>
          cases ut <;> try cases hk
          exact absurd hinb (by decide))
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-- **`wit_lm4_2_write_bytes_overflow_ub`**: real 2-step execution where
`write_bytes::<u64>(copy _2, 0xAB_u8, (2^60)_usize)` overflows `isize::MAX`
(`2^60 * 8 = 2^63 > 2^63 - 1`), triggering undefined behavior in both machines. -/
theorem wit_lm4_2_write_bytes_overflow_ub :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := writeBytesMutBody 0xAB 1152921504606846976
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  let b := writeBytesMutBody 0xAB 1152921504606846976
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1)))]
      (writeBytesTerm 2 0xAB 1152921504606846976)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  have hsim₂ := call_intrinsic_write_bytes_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    u8_integral (fun tf₁ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₁)
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl u64_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, u64_integral⟩)
    (fun _ countSc _ _ _ _ hc _ hle _ _ _ _ _ _ => by
      have hc' : countSc = ⟨1152921504606846976, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hc'
      exact absurd hle (by decide))
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-- Body for `write_bytes` on `&raw const _1` (`.frozen` borrow permission). -/
def writeBytesFrozenBody : CapturedMir :=
  ptr4Body unitK rawConstU64K rawConstU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .not (local42 1)))]
    (writeBytesTerm 2 0xAB 1)

/-- **`wit_lm4_2_write_bytes_frozen_divergence`**: real 2-step execution of
`_2 = &raw const _1` (creating a `.frozen` borrow entry) followed by
`write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize)`: Anneal rejects the write with
`MirStepNode.fail .ub`, while `lean-miri`'s `annealWriteRepeatedBytes` (which
checks allocation mutability without Tree Borrows transitions) steps with
`.ok true`. -/
theorem wit_lm4_2_write_bytes_frozen_divergence :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := writeBytesFrozenBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) := by
  let b := writeBytesFrozenBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawConstU64K rawConstU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .not (local42 1)))] (writeBytesTerm 2 0xAB 1)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  have hdiv := call_intrinsic_write_bytes_perm_divergence (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    u8_integral (fun tf₁ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₁)
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    rfl u64_writeBytesPointee (ptrVal := { allocId := 1, offsetBytes := 0 })
    (valSc := ⟨0xAB, 1⟩) (countSc := ⟨1, 8⟩) (e := entry) (tgtDecl := declOf u64K) (tgtKind := .u64)
    rfl (Or.inl ⟨_, rfl, rfl⟩) (Or.inl ⟨_, rfl, rfl⟩) (.head _) rfl rfl u64_integral
    (by simp [s₁, mkPtrState, entry, rawPtrAllocMapEntry, get?])
    (by decide) (by decide) rfl rfl (Or.inl rfl)
  obtain ⟨ha₂, m₂, hm₂⟩ := hdiv
  exact ⟨s₁, m₁, m₂, hs₁, hm₁, hrel₁, ha₂, hm₂⟩

/-- Body for `write_bytes` at misaligned `offsetBytes = 1` on `*mut u64` with `count = 0`. -/
def writeBytesMisalignedZeroBody : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU8K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 3)
       (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 1 8)))),
     mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K)))]
    (writeBytesTerm 2 0xAB 0)

/-- **`wit_lm4_2_write_bytes_zero_misaligned_ok`**: real 5-step execution
advancing `_2 : *mut u64` to misaligned `offsetBytes = 1` and calling
`write_bytes::<u64>(copy _2, 0xAB_u8, 0_usize) -> bb1`. Because neither Anneal's
`evalWriteBytesCall` nor `lean-miri`'s `Intrinsics.writeBytes` checks pointer
alignment, both step in lockstep to `StateRelLM3_1`-related states with `_1 = 42_u64`
unchanged. -/
theorem wit_lm4_2_write_bytes_zero_misaligned_ok :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := writeBytesMisalignedZeroBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFnLM4_2 b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨42, 8⟩)) := by
  let b := writeBytesMisalignedZeroBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU8K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
       mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 3)
         (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 1 8)))),
       mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K)))]
      (writeBytesTerm 2 0xAB 0)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkPtrState b 0 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkPtrState b 0 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_3 = Offset(copy _3, 1_usize)`
  let s₃ := mkPtrState b 0 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr1]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 3 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
    (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨1, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constInt usizeK 1 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_2 = copy _3 as *mut u64`
  let s₄ := mkPtrState b 0 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr1]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have hsim₄ := step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 2 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (fun _ h => by simp [s₃, mkPtrState, get?] at h)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  -- Step 5: `write_bytes::<u64>(copy _2, 0xAB_u8, 0_usize) -> bb1`
  let s₅ := mkPtrState b 1 0 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr1]
    [entry.toBorrowEntry] 2
  have hs₅ : stepMirFnLM4_2 b s₄ = .step s₅ := rfl
  have hsim₅ := call_intrinsic_write_bytes_simulation (pointeeTy := tyOf u64K)
    hrel₄ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 2 (by decide))
    u8_integral (fun tf₄ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₄)
    usize_integral (fun tf₄ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₄)
    rfl u64_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, u64_integral⟩)
    (fun _ countSc _ _ _ _ hc hpos _ _ _ _ _ _ _ => by
      have hc' : countSc = ⟨0, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      subst hc'
      exact absurd hpos (by decide))
  rw [hs₅] at hsim₅
  obtain ⟨m₅, hm₅, hrel₅⟩ := hsim₅.miri_step_of_anneal_step
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅, rfl⟩

theorem u8_writeBytesPointee :
    WriteBytesPointee emptyLayoutTable (tyOf u8K).kind (encodeTyId (tyOf u8K)) 1 :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- `write_bytes::<u8>(copy ptrIdx, const val_u8, const count_usize) -> bb1` into `_0`. -/
def writeBytesU8Term (ptrIdx : Local) (valBits countBits : Nat) : TerminatorKind :=
  .call (.constant (fnItem "core::intrinsics::write_bytes" u8K))
    [.copy (local42 ptrIdx),
     .constant (constInt u8K valBits 1),
     .constant (constInt usizeK countBits 8)]
    (local42 0) (some 1) .unreachable

/-- Body for partial sub-range `write_bytes` at non-zero byte offset `2`:
`_2 = &raw mut _1; _3 = copy _2 as *mut u8; _3 = Offset(copy _3, 2_usize);
write_bytes::<u8>(copy _3, 0xAB_u8, 2_usize) -> bb1`. -/
def writeBytesPartialBody : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU8K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 3)
       (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 2 8))))]
    (writeBytesU8Term 3 0xAB 2)

/-- **`wit_lm4_2_write_bytes_partial_ok`**: real 4-step execution advancing `_3 : *mut u8`
to byte offset `2` inside `_1 : u64` (`42_u64 = 0x0000_0000_0000_002A`) and calling
`core::intrinsics::write_bytes::<u8>(copy _3, 0xAB_u8, 2_usize) -> bb1`. Both machines
splice bytes `[2, 4)` in lockstep to `0x0000_0000_ABAB_002A` (`2880110634_u64`),
preserving `StateRelLM3_1` and updating `lm31AllocId1` in `lean-miri`'s live memory. -/
theorem wit_lm4_2_write_bytes_partial_ok :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let b := writeBytesPartialBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFnLM4_2 b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨0x00000000ABAB002A, 8⟩)) ∧
      (∃ la msc,
        m₄.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) =
          some (Witness.lm31AllocId1, la) ∧
        ScalarRel ⟨0x00000000ABAB002A, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc)) := by
  let b := writeBytesPartialBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU8K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
       mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 3)
         (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 2 8))))]
      (writeBytesU8Term 3 0xAB 2)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkPtrState b 0 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkPtrState b 0 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_3 = Offset(copy _3, 2_usize)`
  let s₃ := mkPtrState b 0 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr2]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 3 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
    (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨2, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constInt usizeK 2 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `write_bytes::<u8>(copy _3, 0xAB_u8, 2_usize) -> bb1`
  let s₄ := mkPtrState b 1 0
    [.uninit, .init (.scalar ⟨0x00000000ABAB002A, 8⟩), .init ptr0, .init ptr2]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFnLM4_2 b s₃ = .step s₄ := rfl
  have hsim₄ := call_intrinsic_write_bytes_simulation (pointeeTy := tyOf u8K)
    hrel₃ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 3 (by decide))
    u8_integral (fun tf₃ _ => constInt_wellTyped u8_integral valid1 (by decide) rfl b rfl tf₃)
    usize_integral (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    rfl u8_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, u64_integral⟩)
    (fun ptrVal countSc e tgtDecl tgtKind hp hc _ _ he _ htgt ht _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 2 } := by
        simpa [s₃, mkPtrState, ptr2, get?] using hp.symm
      have hc' : countSc = ⟨2, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [constInt] using hval.symm
        · cases hidx
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hc' hd
        cases ht with
        | int _ hk => cases hk
        | uint ut hk =>
          cases ut <;> try cases hk
          refine ⟨?_, Or.inr ⟨⟨42, 8⟩, rfl⟩⟩
          intro x hx _
          cases hx with
          | tail _ h => cases h
          | head _ => exact Or.inl ⟨rfl, rfl⟩)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  have hmem₁ : ∃ la msc,
      m₄.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) =
        some (Witness.lm31AllocId1, la) ∧
      ScalarRel ⟨0x00000000ABAB002A, 8⟩ msc ∧
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
        .ok (.fromScalarInt msc) := by
    obtain ⟨tf₄, htf₄, _, _, hfr₄, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    obtain ⟨slot₁, mls₁, _, _, hslot₁, hmls₁, _, hloc₁⟩ :=
      hfr₄.lookup_local (idx := 1) (decl := declOf u64K) rfl
    have hsl₁ : slot₁ = .init (.scalar ⟨0x00000000ABAB002A, 8⟩) := by
      simpa [s₄, mkPtrState, get?] using hslot₁.symm
    subst hsl₁
    obtain ⟨⟨lay₁, hlay₁⟩, _, hshape_fn₁⟩ :=
      (halloc₄.local_alloc_sync tf₄ htf₄ entry (.head _)).1 _ hslot₁ (by nofun)
    obtain ⟨la₁, hfind₁, _, _, _⟩ := hshape_fn₁ (declOf u64K) rfl
    have hmls₁_eq : mls₁ = ⟨.live (.indirect (stackAllocPlace entry.allocId)), lay₁⟩ := by
      change tf₄.locals[1]? = _ at hlay₁; rw [hlay₁] at hmls₁; exact Option.some.inj hmls₁.symm
    obtain ⟨_, hsc_spec⟩ := hloc₁.indirect_stackAllocPlace_spec hmls₁_eq
      (halloc₄.base_addr_valid entry (.head _)).2.2 hfind₁
      (halloc₄.live_key_unique entry (.head _)) (by decide)
    obtain ⟨_, _, _, msc, hrel_sc, hread⟩ := hsc_spec ⟨0x00000000ABAB002A, 8⟩ rfl
    exact ⟨la₁, msc, hfind₁, hrel_sc, hread⟩
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, rfl, hmem₁⟩

/-! ## 6. `NonDivergingIntrinsic.CopyNonOverlapping` real-step witnesses -/

theorem u64_copyPointee :
    CopyPointee emptyLayoutTable (tyOf u64K).kind (encodeTyId (tyOf u64K)) 8 8 :=
  ⟨u64_writeBytesPointee, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

/-- `copy_nonoverlapping(copy srcIdx, copy dstIdx, const count_usize)` statement. -/
def copyStmt (srcIdx dstIdx : Local) (countBits : Nat) : MirAst.Statement :=
  mkStmt42 (.intrinsic
    (.copyNonOverlapping (.copy (local42 srcIdx)) (.copy (local42 dstIdx))
      (.constant (constInt usizeK countBits 8))))

/-- Single-local `CopyNonOverlapping` body (`_2 = &raw mut _1; copy_nonoverlapping(copy _2, copy _2, count)`). -/
def copySingleMutBody (countBits : Nat) : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     copyStmt 2 2 countBits]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_zero_ok`**: real 2-step execution of
`_2 = &raw mut _1` followed by `copy_nonoverlapping(copy _2, copy _2, 0_usize)`,
showing an aligned zero-count copy succeeds as a no-op even on aliasing pointers
(`src = dst`), preserving `StateRelLM3_1` and `_1 = 42_u64`. -/
theorem wit_lm4_2_copy_nonoverlapping_zero_ok :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := copySingleMutBody 0
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨42, 8⟩)) := by
  let b := copySingleMutBody 0
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))), copyStmt 2 2 0] .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := rfl
  have hsim₂ := step_intrinsic_copyNonOverlapping_simulation_explicit (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro _ _ countSc _ _ _ _ _ _ _ _ hc hpos _ _ _ _ _ _ _ _ _ _ _ _ _
      have hc' : countSc = ⟨0, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [constInt] using hval.symm
        · cases hidx
      subst hc'; exact absurd hpos (by decide))
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl⟩

/-- **`wit_lm4_2_copy_nonoverlapping_overlap_ub`**: real 2-step execution where
`copy_nonoverlapping(copy _2, copy _2, 1_usize)` copies a live `u64` onto itself,
triggering overlap undefined behavior in both machines. -/
theorem wit_lm4_2_copy_nonoverlapping_overlap_ub :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := copySingleMutBody 1
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  let b := copySingleMutBody 1
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))), copyStmt 2 2 1] .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  obtain ⟨_, hsim₂⟩ := step_intrinsic_copyNonOverlapping_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro _ _ _ e_s e_d _ _ _ _ _ _ _ _ _ he_s _ he_d _ _ _ _ _ _ _ _ _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ =>
          exact ⟨by nofun, Or.inl rfl,
            by simp [s₁, mkPtrState, entry, rawPtrAllocMapEntry, get?],
            Or.inr (by simp [s₁, mkPtrState, entry, rawPtrAllocMapEntry, get?])⟩)
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-- **`wit_lm4_2_copy_nonoverlapping_oob_ub`**: real 2-step execution where
`copy_nonoverlapping(copy _2, copy _2, 2_usize)` attempts to copy `16 > 8` bytes
out of the 8-byte stack allocation of `_1`, triggering undefined behavior in both
machines. -/
theorem wit_lm4_2_copy_nonoverlapping_oob_ub :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := copySingleMutBody 2
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  let b := copySingleMutBody 2
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))), copyStmt 2 2 2] .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  obtain ⟨_, hsim₂⟩ := step_intrinsic_copyNonOverlapping_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro _ _ countSc e_s _ decl_s _ srcBytes _ _ _ hc _ _ he_s _ _ _ hdecl_s _ hrig_s _ hinS _ _ _
      have hc' : countSc = ⟨2, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [constInt] using hval.symm
        · cases hidx
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases hdecl_s; cases hrig_s
        subst hc'; dsimp only at hinS; omega)
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-- **`wit_lm4_2_copy_nonoverlapping_overflow_ub`**: real 2-step execution where
`copy_nonoverlapping(copy _2, copy _2, (2^60)_usize)` overflows `isize::MAX`
(`2^60 * 8 = 2^63 > 2^63 - 1`), triggering undefined behavior in both machines. -/
theorem wit_lm4_2_copy_nonoverlapping_overflow_ub :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := copySingleMutBody (2 ^ 60)
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  let b := copySingleMutBody (2 ^ 60)
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU64K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))), copyStmt 2 2 (2 ^ 60)] .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  obtain ⟨_, hsim₂⟩ := step_intrinsic_copyNonOverlapping_simulation (pointeeTy := tyOf u64K)
    hrel₁ hphase rfl rfl rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    usize_integral (fun tf₁ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₁)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro _ _ countSc _ _ _ _ _ _ _ _ hc _ hle _ _ _ _ _ _ _ _ _ _ _ _
      have hc' : countSc = ⟨2 ^ 60, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [constInt] using hval.symm
        · cases hidx
      subst hc'; exact absurd hle (by decide))
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-- Body for `copy_nonoverlapping` at misaligned `offsetBytes = 1` on `*mut u64` with `count = 0`. -/
def copyMisalignedZeroBody : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU8K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 3)
       (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 1 8)))),
     mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K))),
     copyStmt 2 2 0]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_zero_misaligned_ub`**: real 5-step execution
advancing `_2 : *mut u64` to misaligned `offsetBytes = 1` and executing
`copy_nonoverlapping(copy _2, copy _2, 0_usize)`. Contrasting directly with
`wit_lm4_2_write_bytes_zero_misaligned_ok`, both Anneal's `evalCopyNonOverlapping`
and `lean-miri`'s `Intrinsics.copyWith` check pointer alignment unconditionally
before checking `count = 0`, so both machines diagnose undefined behavior. -/
theorem wit_lm4_2_copy_nonoverlapping_zero_misaligned_ub :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState) (msg : String),
      let b := copyMisalignedZeroBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFnLM4_2 b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg)) := by
  let b := copyMisalignedZeroBody
  have hrel₀ : StateRel b (ptr4AnnealPre b) (ptr4MiriPre b unitK) :=
    ptr4_stateRel unitK rawMutU64K rawMutU8K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
       mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 3)
         (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 1 8)))),
       mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K))),
       copyStmt 2 2 0]
      .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr4_all_immediate b _ tf htf 2, ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
  let s₁ := mkPtrState b 0 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr4_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 0 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  let s₃ := mkPtrState b 0 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr1]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 3 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
    (fun ptrVal sc _ tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨1, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constInt usizeK 1 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkPtrState b 0 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr1]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have hsim₄ := step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 2 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (fun _ h => by simp [s₃, mkPtrState, get?] at h)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  obtain ⟨_, hsim₅⟩ := step_intrinsic_copyNonOverlapping_simulation (pointeeTy := tyOf u64K)
    hrel₄ hphase rfl rfl rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 2 (by decide))
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 2 (by decide))
    usize_integral (fun tf₄ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₄)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro _ _ countSc _ _ _ _ _ _ _ _ hc hpos _ _ _ _ _ _ _ _ _ _ _ _ _
      have hc' : countSc = ⟨0, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [constInt] using hval.symm
        · cases hidx
      subst hc'; exact absurd hpos (by decide))
  have hs₅ : stepMirFnLM4_2 b s₄ = .fail .ub := rfl
  rw [hs₅] at hsim₅
  obtain ⟨m₅, msg, hm₅⟩ := hsim₅.miri_ub_of_anneal_ub
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅, msg,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, hs₅, hm₅⟩

/-- Reusable 6-local MIR body (`_0 : (), _1 : u64, _2 : u64, _3 : *const u64, _4 : d₄, _5 : *mut u64`)
for distinct-allocation `CopyNonOverlapping` witnesses. -/
def copy6Body (d₄ : RigidTy) (stmts : List MirAst.Statement) : CapturedMir where
  defPath := "lm_4_2_witness::copy6"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf unitK, declOf u64K, declOf u64K, declOf rawConstU64K, declOf d₄,
    declOf rawMutU64K]
  basicBlocks := [{ statements := stmts, terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Pre-state of `copy6Body` with `_1 = 42_u64` (if `initSrc = true`, else `.uninit`)
and `_2 = 99_u64`. -/
def copy6AnnealPre (b : CapturedMir) (initSrc : Bool) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit,
          if initSrc then .init (.scalar ⟨42, 8⟩) else .uninit,
          .init (.scalar ⟨99, 8⟩), .uninit, .uninit, .uninit] }
    memory := (initMachineState b []).memory }

def copy6MiriFramePre (b : CapturedMir) (initSrc : Bool) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody b
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (tyOf unitK)) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      if initSrc then
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
          layout := some (translateTy (tyOf u64K)) }
      else
        { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))),
        layout := some (translateTy (tyOf u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def copy6MiriPre (b : CapturedMir) (initSrc : Bool) : AnnealStepState :=
  { stack := ⟨#[copy6MiriFramePre b initSrc]⟩, machine := AnnealMachine.empty }

theorem copy6_all_immediate (b : CapturedMir) (initSrc : Bool) :
    ∀ tf, (copy6MiriPre b initSrc).stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 2 | 3 | 4 | 5 => simp [copy6MiriFramePre] at hmls; subst hmls; cases hmp
  | 1 => cases initSrc <;> (simp [copy6MiriFramePre] at hmls; subst hmls; cases hmp)
  | _ + 6 => simp [copy6MiriFramePre] at hmls

theorem copy6_stateRel (d₄ : RigidTy) (stmts : List MirAst.Statement) (initSrc : Bool) :
    StateRel (copy6Body d₄ stmts)
      (copy6AnnealPre (copy6Body d₄ stmts) initSrc)
      (copy6MiriPre (copy6Body d₄ stmts) initSrc) := by
  let b := copy6Body d₄ stmts
  refine StateRel.mk (copy6MiriFramePre b initSrc) rfl rfl ⟨translateTy (tyOf unitK), rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 2 | 3 | 4 | 5 | _ + 6 => rintro ⟨⟩
      | 1 => cases initSrc <;> rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 3 | 4 | 5 =>
    have hs : slot = .uninit := by simpa [copy6AnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [copy6MiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = declOf u64K := by simpa [b, copy6Body, get?] using hdecl.symm
    subst hd
    cases initSrc with
    | true =>
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [copy6AnnealPre, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy (tyOf u64K)) } := by
        simpa [copy6MiriFramePre] using hmls.symm
      subst hs hm
      exact .immediate _ _ (some (translateTy (tyOf u64K))) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | false =>
      have hs : slot = .uninit := by simpa [copy6AnnealPre, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [copy6MiriFramePre] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 2 =>
    have hd : decl = declOf u64K := by simpa [b, copy6Body, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨99, 8⟩) := by simpa [copy6AnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))),
          layout := some (translateTy (tyOf u64K)) } := by
      simpa [copy6MiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (tyOf u64K))) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel99 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 6 => simp [copy6Body, get?] at hdecl

/-- Body for distinct-local `copy_nonoverlapping`:
`_3 = &raw const _1; _4 = &raw mut _2; copy_nonoverlapping(copy _3, copy _4, 1_usize)`. -/
def copyDistinctBody : CapturedMir :=
  copy6Body rawMutU64K
    [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
     mkStmt42 (.assign (local42 4) (.rawPtr .mut (local42 2))),
     copyStmt 3 4 1]

/-- **`wit_lm4_2_copy_nonoverlapping_ok`**: real 3-step execution from pointer-free
`StateRel` (`_1 = 42_u64`, `_2 = 99_u64`):
1. `_3 = &raw const _1` promotes `_1` into `lm31AllocId1`;
2. `_4 = &raw mut _2` promotes `_2` into `lm31AllocId2`;
3. `copy_nonoverlapping(copy _3, copy _4, 1_usize)` copies `42_u64` from `_1` into
   `_2`, preserving `StateRelLM3_1` under `copyNextAllocMap`, updating Anneal's `_2`
   to `42_u64`, and writing `42_u64` into `lm31AllocId2` in `lean-miri`'s live memory. -/
theorem wit_lm4_2_copy_nonoverlapping_ok :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := copyDistinctBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
      stepMirFn b (copy6AnnealPre b true) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (copy6MiriPre b true) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      stepMirFnLM4_2 b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₂, e₁] ∧
      get? s₃.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩)) ∧
      (∃ la msc,
        m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
          some (Witness.lm31AllocId2, la) ∧
        ScalarRel ⟨42, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc)) := by
  let b := copyDistinctBody
  have hrel₀ : StateRel b (copy6AnnealPre b true) (copy6MiriPre b true) :=
    copy6_stateRel rawMutU64K
      [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
       mkStmt42 (.assign (local42 4) (.rawPtr .mut (local42 2))),
       copyStmt 3 4 1] true
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  have himm₀ : ∀ tf, (copy6MiriPre b true).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨copy6_all_immediate b true tf htf 3, copy6_all_immediate b true tf htf 1⟩
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .uninit, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b (copy6AnnealPre b true) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (copy6AnnealPre b true).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(copy6MiriPre b true).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (copy6_all_immediate b true _ rfl k)
  -- Step 2: `_4 = &raw mut _2`
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .uninit]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  have hsim₂ := step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; decide) (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  -- Step 3: `copy_nonoverlapping(copy _3, copy _4, 1_usize)`
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr2, .uninit]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFnLM4_2 b s₂ = .step s₃ := rfl
  have hsim₃ := step_intrinsic_copyNonOverlapping_simulation_explicit (pointeeTy := tyOf u64K)
    hrel₂ hphase rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide) (by decide))
    rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 4 (by decide) (by decide))
    usize_integral (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      have hs_ty : decl_s = declOf u64K := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · exact Option.some.inj hd_s.symm
        · rcases List.mem_cons.mp he' with rfl | h
          · exact Option.some.inj hd_s.symm
          · cases h
      have hd_ty : decl_d = declOf u64K := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · exact Option.some.inj hd_d.symm
        · rcases List.mem_cons.mp he' with rfl | h
          · exact Option.some.inj hd_d.symm
          · cases h
      subst hs_ty hd_ty; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro srcPtr dstPtr _ e_s e_d _ _ _ _ hsrc hdst _ _ _ he_s het_s he_d het_d _ _ _ _ _ _ _ _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr1, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr2, get?] using hdst.symm
      subst hpS hpD
      have hes : e_s = e₁ := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · cases het_s
        · rcases List.mem_cons.mp he' with rfl | h
          · rfl
          · cases h
      have hed : e_d = e₂ := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het_d
          · cases h
      subst hes hed
      exact ⟨by nofun, Or.inl rfl, by simp [s₂, mkPtrState, e₁, rawPtrAllocMapEntry, get?],
        Or.inr (by simp [s₂, mkPtrState, e₂, rawPtrAllocMapEntry, get?])⟩)
  rw [hs₃] at hsim₃
  have hmap_eq : copyNextAllocMap s₂.frame.locals [e₂, e₁] 4
      (.constant (constInt usizeK 1 8)) 8 = [e₂, e₁] := rfl
  rw [hmap_eq] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  -- Extract `readScalar = 42_u64` from `lm31AllocId2` in `m₃.machine.memory.live`.
  have hmem₂ : ∃ la msc,
      m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
        some (Witness.lm31AllocId2, la) ∧
      ScalarRel ⟨42, 8⟩ msc ∧
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
        .ok (.fromScalarInt msc) := by
    obtain ⟨tf₃, htf₃, _, _, hfr₃, _, _, _, _, _, halloc₃, _⟩ := id hrel₃
    obtain ⟨slot₂, mls₂, _, _, hslot₂, hmls₂, _, hloc₂⟩ :=
      hfr₃.lookup_local (idx := 2) (decl := declOf u64K) rfl
    have hsl₂ : slot₂ = .init (.scalar ⟨42, 8⟩) := by
      simpa [s₃, mkPtrState, get?] using hslot₂.symm
    subst hsl₂
    obtain ⟨⟨lay₂, hlay₂⟩, _, hshape_fn₂⟩ :=
      (halloc₃.local_alloc_sync tf₃ htf₃ e₂ (.head _)).1 _ hslot₂ (by nofun)
    obtain ⟨la₂, hfind₂, _, _, _⟩ := hshape_fn₂ (declOf u64K) rfl
    have hmls₂_eq : mls₂ = ⟨.live (.indirect (stackAllocPlace e₂.allocId)), lay₂⟩ := by
      change tf₃.locals[2]? = _ at hlay₂; rw [hlay₂] at hmls₂; exact Option.some.inj hmls₂.symm
    obtain ⟨_, hsc_spec⟩ := hloc₂.indirect_stackAllocPlace_spec hmls₂_eq
      (halloc₃.base_addr_valid e₂ (.head _)).2.2 hfind₂
      (halloc₃.live_key_unique e₂ (.head _)) (by decide)
    obtain ⟨_, _, _, msc, hrel_sc, hread⟩ := hsc_spec ⟨42, 8⟩ rfl
    exact ⟨la₂, msc, hfind₂, hrel_sc, hread⟩
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, rfl, hmem₂⟩

/-- **`wit_lm4_2_copy_nonoverlapping_uninit_src_divergence`**: real 3-step execution
from `_1 = .uninit`, `_2 = 99_u64` (`_3 = &raw const _1; _4 = &raw mut _2;
copy_nonoverlapping(copy _3, copy _4, 1_usize)`), witnessing the characterized
uninitialized-source divergence: Anneal's typed `evalCopySingleDirect` rejects
reading `.uninit` (`MirStepNode.fail .ub`), whereas `lean-miri`'s untyped
`Allocation.copyRepeatedly` copies the uninitialized byte mask (`.ok true`). -/
theorem wit_lm4_2_copy_nonoverlapping_uninit_src_divergence :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := copyDistinctBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
      stepMirFn b (copy6AnnealPre b false) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (copy6MiriPre b false) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      stepMirFnLM4_2 b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) := by
  let b := copyDistinctBody
  have hrel₀ : StateRel b (copy6AnnealPre b false) (copy6MiriPre b false) :=
    copy6_stateRel rawMutU64K
      [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
       mkStmt42 (.assign (local42 4) (.rawPtr .mut (local42 2))),
       copyStmt 3 4 1] false
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  have himm₀ : ∀ tf, (copy6MiriPre b false).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨copy6_all_immediate b false tf htf 3, copy6_all_immediate b false tf htf 1⟩
  let s₁ := mkPtrState b 0 1
    [.uninit, .uninit, .init (.scalar ⟨99, 8⟩), .init ptr1, .uninit, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b (copy6AnnealPre b false) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (copy6AnnealPre b false).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(copy6MiriPre b false).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (copy6_all_immediate b false _ rfl k)
  let s₂ := mkPtrState b 0 2
    [.uninit, .uninit, .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .uninit]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  have hsim₂ := step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; decide) (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  obtain ⟨ha₃, m₃, hm₃⟩ := step_intrinsic_copyNonOverlapping_uninit_src_divergence
    (pointeeTy := tyOf u64K) hrel₂ hphase rfl rfl rfl rfl
    (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide) (by decide))
    rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 4 (by decide) (by decide))
    usize_integral (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    u64_copyPointee (srcPtr := { allocId := 1, offsetBytes := 0 })
    (dstPtr := { allocId := 2, offsetBytes := 0 }) (countSc := ⟨1, 8⟩)
    (e_s := e₁) (e_d := e₂) rfl rfl rfl rfl (Or.inl ⟨_, rfl, rfl⟩) rfl
    (.tail _ (.head _)) rfl (.head _) rfl
    (fun _ h => by cases h; rfl) (fun _ h => by cases h; rfl)
    rfl (by simp [s₂, mkPtrState, e₂, rawPtrAllocMapEntry, get?])
  exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, ha₃, hm₃⟩

/-- Body for Tree Borrows frozen-destination `copy_nonoverlapping` divergence:
`_3 = &raw const _1; _4 = &raw const _2; _5 = copy _4 as *mut u64;
copy_nonoverlapping(copy _3, copy _5, 1_usize)`. -/
def copyPermDivBody : CapturedMir :=
  copy6Body rawConstU64K
    [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
     mkStmt42 (.assign (local42 4) (.rawPtr .not (local42 2))),
     mkStmt42 (.assign (local42 5) (.cast .ptrToPtr (.copy (local42 4)) (tyOf rawMutU64K))),
     copyStmt 3 5 1]

/-- **`wit_lm4_2_copy_nonoverlapping_perm_divergence`**: real 4-step execution
casting `_4 = &raw const _2` (`perm = .frozen`) to `_5 : *mut u64` and running
`copy_nonoverlapping(copy _3, copy _5, 1_usize)`: Anneal rejects writing through
the `.frozen` destination borrow (`MirStepNode.fail .ub`), whereas `lean-miri`
under `annealMemoryCopyHooks` (pre-`LM-3.3` Tree Borrows) steps with `.ok true`. -/
theorem wit_lm4_2_copy_nonoverlapping_perm_divergence :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let b := copyPermDivBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .not 2 2 Witness.lm31AllocId2
      stepMirFn b (copy6AnnealPre b true) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (copy6MiriPre b true) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₂, e₁] ∧
      stepMirFnLM4_2 b s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) := by
  let b := copyPermDivBody
  have hrel₀ : StateRel b (copy6AnnealPre b true) (copy6MiriPre b true) :=
    copy6_stateRel rawConstU64K
      [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
       mkStmt42 (.assign (local42 4) (.rawPtr .not (local42 2))),
       mkStmt42 (.assign (local42 5) (.cast .ptrToPtr (.copy (local42 4)) (tyOf rawMutU64K))),
       copyStmt 3 5 1] true
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .not 2 2 Witness.lm31AllocId2
  have himm₀ : ∀ tf, (copy6MiriPre b true).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨copy6_all_immediate b true tf htf 3, copy6_all_immediate b true tf htf 1⟩
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .uninit, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b (copy6AnnealPre b true) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (copy6AnnealPre b true).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(copy6MiriPre b true).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (copy6_all_immediate b true _ rfl k)
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .uninit]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  have hsim₂ := step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; decide) (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hsim₃ := step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₂ htf₂ =>
      ⟨himm₂ tf₂ htf₂ 5 (by decide) (by decide), himm₂ tf₂ htf₂ 4 (by decide) (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hk₁ hk₂
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hk₁ hk₂)
  obtain ⟨ha₄, m₄, hm₄⟩ := step_intrinsic_copyNonOverlapping_perm_divergence
    (pointeeTy := tyOf u64K) hrel₃ hphase rfl rfl rfl rfl
    (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 3 (by decide) (by decide))
    rfl rfl (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 5 (by decide) (by decide))
    usize_integral (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    u64_copyPointee (srcPtr := { allocId := 1, offsetBytes := 0 })
    (dstPtr := { allocId := 2, offsetBytes := 0 }) (countSc := ⟨1, 8⟩)
    (e_s := e₁) (e_d := e₂) rfl rfl rfl rfl (Or.inl ⟨_, rfl, rfl⟩) rfl
    (.tail _ (.head _)) rfl (.head _) rfl (by decide)
    (fun _ h => by cases h; rfl) (fun _ h => by cases h; rfl)
    (by simp [s₃, mkPtrState, e₁, rawPtrAllocMapEntry, get?])
    (by simp [s₃, mkPtrState, e₂, rawPtrAllocMapEntry, get?])
    (Or.inr (Or.inl rfl))
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, ha₄, hm₄⟩


def rawMutU32K : RigidTy := .rawPtr .mut u32K
def rawConstU32K : RigidTy := .rawPtr .not u32K
def rawConstU8K : RigidTy := .rawPtr .not u8K

theorem u8_copyPointee :
    CopyPointee emptyLayoutTable (tyOf u8K).kind (encodeTyId (tyOf u8K)) 1 1 :=
  ⟨u8_writeBytesPointee, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem u32_writeBytesPointee :
    WriteBytesPointee emptyLayoutTable (tyOf u32K).kind (encodeTyId (tyOf u32K)) 4 :=
  ⟨rfl, rfl, rfl, by decide⟩

theorem u32_copyPointee :
    CopyPointee emptyLayoutTable (tyOf u32K).kind (encodeTyId (tyOf u32K)) 4 4 :=
  ⟨u32_writeBytesPointee, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩

def ptr6Body (d₀ d₂ d₃ d₄ d₅ : RigidTy) (stmts : List MirAst.Statement) (term0 : TerminatorKind) :
    CapturedMir where
  defPath := "lm_4_2_witness::ptr6"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf d₀, declOf u64K, declOf d₂, declOf d₃, declOf d₄, declOf d₅]
  basicBlocks := [
    { statements := stmts, terminator := mkTerm42 term0, isCleanup := false },
    { statements := [], terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def ptr6AnnealPre (b : CapturedMir) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState b []).memory }

def ptr6MiriFramePre (b : CapturedMir) (d₀ : RigidTy) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody b
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (tyOf d₀)) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (tyOf u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def ptr6MiriPre (b : CapturedMir) (d₀ : RigidTy) : AnnealStepState :=
  { stack := ⟨#[ptr6MiriFramePre b d₀]⟩, machine := AnnealMachine.empty }

theorem ptr6_all_immediate (b : CapturedMir) (d₀ : RigidTy) :
    ∀ tf, (ptr6MiriPre b d₀).stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [ptr6MiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 6 => simp [ptr6MiriFramePre] at hmls

theorem ptr6_stateRel (d₀ d₂ d₃ d₄ d₅ : RigidTy) (stmts : List MirAst.Statement)
    (term0 : TerminatorKind) :
    StateRel (ptr6Body d₀ d₂ d₃ d₄ d₅ stmts term0)
      (ptr6AnnealPre (ptr6Body d₀ d₂ d₃ d₄ d₅ stmts term0))
      (ptr6MiriPre (ptr6Body d₀ d₂ d₃ d₄ d₅ stmts term0) d₀) := by
  let b := ptr6Body d₀ d₂ d₃ d₄ d₅ stmts term0
  refine StateRel.mk (ptr6MiriFramePre b d₀) rfl rfl ⟨translateTy (tyOf d₀), rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 | 4 | 5 =>
    have hs : slot = .uninit := by simpa [ptr6AnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [ptr6MiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = declOf u64K := by simpa [b, ptr6Body, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [ptr6AnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
          layout := some (translateTy (tyOf u64K)) } := by
      simpa [ptr6MiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (tyOf u64K))) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 6 => simp [ptr6Body, get?] at hdecl

/-- Body for same-allocation disjoint sub-range cross-type `copy_nonoverlapping`:
`_2 = &raw mut _1; _3 = copy _2 as *mut u8; _4 = copy _2 as *mut u8;
_4 = Offset(copy _4, 2_usize); copy_nonoverlapping::<u8>(copy _3, copy _4, 2_usize)`. -/
def copyDisjointSubrangeBody : CapturedMir :=
  ptr6Body unitK rawMutU64K rawMutU8K rawMutU8K u32K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 4)
       (.binaryOp .offset (.copy (local42 4)) (.constant (constInt usizeK 2 8)))),
     copyStmt 3 4 2]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_disjoint_subrange_ok`**: real 5-step execution
copying `2` bytes (`count = 2 > 1`) via `*mut u8` from byte sub-range `[0, 2)` of
`_1 : u64` (`42_u64 = 0x0000_0000_0000_002A`) into disjoint byte sub-range `[2, 4)`
of the same local `_1 : u64` via `step_intrinsic_copyNonOverlapping_simulation_same_allocMap`.
Both machines splice `_1` in lockstep to `0x0000_0000_002A_002A` (`2752554_u64`),
preserving `StateRelLM3_1` with `[entry]` and updating `lm31AllocId1` in
`lean-miri`'s live memory. -/
theorem wit_lm4_2_copy_nonoverlapping_disjoint_subrange_ok :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := copyDisjointSubrangeBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr6AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr6MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFnLM4_2 b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨0x00000000002A002A, 8⟩)) ∧
      (∃ la msc,
        m₅.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) =
          some (Witness.lm31AllocId1, la) ∧
        ScalarRel ⟨0x00000000002A002A, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc)) := by
  let b := copyDisjointSubrangeBody
  have hrel₀ : StateRel b (ptr6AnnealPre b) (ptr6MiriPre b unitK) :=
    ptr6_stateRel unitK rawMutU64K rawMutU8K rawMutU8K u32K
      [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
       mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 4)
         (.binaryOp .offset (.copy (local42 4)) (.constant (constInt usizeK 2 8)))),
       copyStmt 3 4 2]
      .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr6MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr6_all_immediate b _ tf htf 2, ptr6_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr6AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr6AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr6MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr6_all_immediate b _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_4 = copy _2 as *mut u8`
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hsim₃ := step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_4 = Offset(copy _4, 2_usize)`
  let s₄ := mkPtrState b 0 4
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFn b s₃ = .step s₄ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₄ := step_binOp_offset_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 4 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
    (fun _ h => by simp [s₃, mkPtrState, get?] at h)
    (fun ptrVal sc _ tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨2, 8⟩ := by
        change evalOperand s₃.frame.locals (.constant (constInt usizeK 2 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₃ (by rintro _ ⟨⟩)
    rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  -- Step 5: `copy_nonoverlapping::<u8>(copy _3, copy _4, 2_usize)`
  let s₅ := mkPtrState b 0 5
    [.uninit, .init (.scalar ⟨0x00000000002A002A, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit]
    [entry.toBorrowEntry] 2
  have hs₅ : stepMirFnLM4_2 b s₄ = .step s₅ := rfl
  have hsim₅ := step_intrinsic_copyNonOverlapping_simulation_same_allocMap (pointeeTy := tyOf u8K)
    hrel₄ hphase rfl rfl rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 3 (by decide))
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 4 (by decide))
    usize_integral (fun tf₄ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₄)
    u8_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ =>
          have hs_ty : decl_s = declOf u64K := Option.some.inj hd_s.symm
          have hd_ty : decl_d = declOf u64K := Option.some.inj hd_d.symm
          subst hs_ty hd_ty
          exact Or.inl ⟨⟨.u64, u64_integral⟩, ⟨.u64, u64_integral⟩⟩)
    (by
      intro _ _ _ e_s e_d _ _ _ _ _ _ _ _ _ he_s _ he_d _ _ _ _ _ _ _ _ _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ =>
          exact ⟨by nofun, Or.inl rfl,
            by simp [s₄, mkPtrState, entry, rawPtrAllocMapEntry, get?],
            Or.inr (by simp [s₄, mkPtrState, entry, rawPtrAllocMapEntry, get?])⟩)
    (by
      intro dstPtr _ e_d hdst _ _ he_d _ x hx _
      have hpD : dstPtr = { allocId := 1, offsetBytes := 2 } := by
        simpa [s₄, mkPtrState, ptr2, get?] using hdst.symm
      subst hpD
      cases he_d with
      | tail _ h => cases h
      | head _ =>
        cases hx with
        | tail _ h => cases h
        | head _ => exact Or.inl ⟨rfl, rfl⟩)
  rw [hs₅] at hsim₅
  obtain ⟨m₅, hm₅, hrel₅⟩ := hsim₅.miri_step_of_anneal_step
  have hmem₁ : ∃ la msc,
      m₅.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) =
        some (Witness.lm31AllocId1, la) ∧
      ScalarRel ⟨0x00000000002A002A, 8⟩ msc ∧
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
        .ok (.fromScalarInt msc) := by
    obtain ⟨tf₅, htf₅, _, _, hfr₅, _, _, _, _, _, halloc₅, _⟩ := id hrel₅
    obtain ⟨slot₁, mls₁, _, _, hslot₁, hmls₁, _, hloc₁⟩ :=
      hfr₅.lookup_local (idx := 1) (decl := declOf u64K) rfl
    have hsl₁ : slot₁ = .init (.scalar ⟨0x00000000002A002A, 8⟩) := by
      simpa [s₅, mkPtrState, get?] using hslot₁.symm
    subst hsl₁
    obtain ⟨⟨lay₁, hlay₁⟩, _, hshape_fn₁⟩ :=
      (halloc₅.local_alloc_sync tf₅ htf₅ entry (.head _)).1 _ hslot₁ (by nofun)
    obtain ⟨la₁, hfind₁, _, _, _⟩ := hshape_fn₁ (declOf u64K) rfl
    have hmls₁_eq : mls₁ = ⟨.live (.indirect (stackAllocPlace entry.allocId)), lay₁⟩ := by
      change tf₅.locals[1]? = _ at hlay₁; rw [hlay₁] at hmls₁; exact Option.some.inj hmls₁.symm
    obtain ⟨_, hsc_spec⟩ := hloc₁.indirect_stackAllocPlace_spec hmls₁_eq
      (halloc₅.base_addr_valid entry (.head _)).2.2 hfind₁
      (halloc₅.live_key_unique entry (.head _)) (by decide)
    obtain ⟨_, _, _, msc, hrel_sc, hread⟩ := hsc_spec ⟨0x00000000002A002A, 8⟩ rfl
    exact ⟨la₁, msc, hfind₁, hrel_sc, hread⟩
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅,
    rfl, hmem₁⟩

/-- Body for cross-type `u64 -> u32` `copy_nonoverlapping` into an `.uninit` destination:
`_3 = &raw const _1; _5 = &raw mut _2; _4 = copy _3 as *const u32;
copy_nonoverlapping::<u32>(copy _4, copy _5, 1_usize)`. -/
def copyCrossTypeBody : CapturedMir :=
  ptr6Body unitK u32K rawConstU64K rawConstU32K rawMutU32K
    [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
     mkStmt42 (.assign (local42 5) (.rawPtr .mut (local42 2))),
     mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawConstU32K))),
     copyStmt 4 5 1]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_cross_type_ok`**: real 4-step execution
slicing the low `4` bytes of `_1 : u64` (`42_u64`) via `*const u32` into
uninitialized `_2 : u32` (`.uninit`) via `*mut u32` and
`step_intrinsic_copyNonOverlapping_simulation_same_allocMap`. Both machines
initialize `_2` to `42_u32` in lockstep, preserving `StateRelLM3_1` with
`[e₂, e₁]` and writing `42_u32` into `lm31AllocId2` in `lean-miri`'s live memory. -/
theorem wit_lm4_2_copy_nonoverlapping_cross_type_ok :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let b := copyCrossTypeBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
      stepMirFn b (ptr6AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr6MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₂, e₁] ∧
      stepMirFnLM4_2 b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [e₂, e₁] ∧
      get? s₄.frame.locals 2 = some (.init (.scalar ⟨42, 4⟩)) ∧
      (∃ la msc,
        m₄.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
          some (Witness.lm31AllocId2, la) ∧
        ScalarRel ⟨42, 4⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) false =
          .ok (.fromScalarInt msc)) := by
  let b := copyCrossTypeBody
  have hrel₀ : StateRel b (ptr6AnnealPre b) (ptr6MiriPre b unitK) :=
    ptr6_stateRel unitK u32K rawConstU64K rawConstU32K rawMutU32K
      [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
       mkStmt42 (.assign (local42 5) (.rawPtr .mut (local42 2))),
       mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawConstU32K))),
       copyStmt 4 5 1]
      .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  have himm₀ : ∀ tf, (ptr6MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr6_all_immediate b _ tf htf 3, ptr6_all_immediate b _ tf htf 1⟩
  -- Step 1: `_3 = &raw const _1`
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr1, .uninit, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr6AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr6AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr6MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr6_all_immediate b _ _ rfl k)
  -- Step 2: `_5 = &raw mut _2`
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr1, .uninit, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 5 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 5 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  have hsim₂ := step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide) himm₁_pair hsupply₁
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; decide) (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  -- Step 3: `_4 = copy _3 as *const u32`
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr1, .init ptr1, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hsim₃ := step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₂ htf₂ =>
      ⟨himm₂ tf₂ htf₂ 4 (by decide) (by decide), himm₂ tf₂ htf₂ 3 (by decide) (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hk₁ hk₂
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hk₁ hk₂)
  -- Step 4: `copy_nonoverlapping::<u32>(copy _4, copy _5, 1_usize)`
  let s₄ := mkPtrState b 0 4
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 4⟩), .init ptr1, .init ptr1, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₄ : stepMirFnLM4_2 b s₃ = .step s₄ := rfl
  have hsim₄ := step_intrinsic_copyNonOverlapping_simulation_same_allocMap (pointeeTy := tyOf u32K)
    hrel₃ hphase rfl rfl rfl rfl (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 4 (by decide) (by decide))
    rfl rfl (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 5 (by decide) (by decide))
    usize_integral (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    u32_copyPointee
    (by
      intro srcPtr dstPtr e_s e_d decl_s decl_d hsrc hdst he_s het_s he_d het_d hd_s hd_d _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr1, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr2, get?] using hdst.symm
      subst hpS hpD
      have hes : e_s = e₁ := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · cases het_s
        · rcases List.mem_cons.mp he' with rfl | h
          · rfl
          · cases h
      have hed : e_d = e₂ := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het_d
          · cases h
      subst hes hed
      have hs_ty : decl_s = declOf u64K := Option.some.inj hd_s.symm
      have hd_ty : decl_d = declOf u32K := Option.some.inj hd_d.symm
      subst hs_ty hd_ty
      exact Or.inl ⟨⟨.u64, u64_integral⟩, ⟨.u32, u32_integral⟩⟩)
    (by
      intro srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes
        hsrc hdst hc _ _ he_s het_s he_d het_d hd_s hd_d _ hrig_d _ _ _ _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr1, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr2, get?] using hdst.symm
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [constInt] using hval.symm
        · cases hidx
      subst hpS hpD hc'
      have hes : e_s = e₁ := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · cases het_s
        · rcases List.mem_cons.mp he' with rfl | h
          · rfl
          · cases h
      have hed : e_d = e₂ := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het_d
          · cases h
      subst hes hed
      have hd_ty : decl_d = declOf u32K := Option.some.inj hd_d.symm
      subst hd_ty
      have hdst_sz : dstBytes = 4 := Option.some.inj hrig_d.symm
      subst hdst_sz
      exact ⟨by nofun, Or.inl rfl, by simp [s₃, mkPtrState, e₁, rawPtrAllocMapEntry, get?],
        Or.inl ⟨rfl, rfl⟩⟩)
    (by
      intro dstPtr _ e_d hdst _ _ he_d het_d x hx hloc
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr2, get?] using hdst.symm
      subst hpD
      have hed : e_d = e₂ := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het_d
          · cases h
      subst hed
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inl ⟨rfl, rfl⟩
      · rcases List.mem_cons.mp hx' with rfl | h
        · cases hloc
        · cases h)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  have hmem₂ : ∃ la msc,
      m₄.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
        some (Witness.lm31AllocId2, la) ∧
      ScalarRel ⟨42, 4⟩ msc ∧
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) false =
        .ok (.fromScalarInt msc) := by
    obtain ⟨tf₄, htf₄, _, _, hfr₄, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    obtain ⟨slot₂, mls₂, _, _, hslot₂, hmls₂, _, hloc₂⟩ :=
      hfr₄.lookup_local (idx := 2) (decl := declOf u32K) rfl
    have hsl₂ : slot₂ = .init (.scalar ⟨42, 4⟩) := by
      simpa [s₄, mkPtrState, get?] using hslot₂.symm
    subst hsl₂
    obtain ⟨⟨lay₂, hlay₂⟩, _, hshape_fn₂⟩ :=
      (halloc₄.local_alloc_sync tf₄ htf₄ e₂ (.head _)).1 _ hslot₂ (by nofun)
    obtain ⟨la₂, hfind₂, _, _, _⟩ := hshape_fn₂ (declOf u32K) rfl
    have hmls₂_eq : mls₂ = ⟨.live (.indirect (stackAllocPlace e₂.allocId)), lay₂⟩ := by
      change tf₄.locals[2]? = _ at hlay₂; rw [hlay₂] at hmls₂; exact Option.some.inj hmls₂.symm
    obtain ⟨_, hsc_spec⟩ := hloc₂.indirect_stackAllocPlace_spec hmls₂_eq
      (halloc₄.base_addr_valid e₂ (.head _)).2.2 hfind₂
      (halloc₄.live_key_unique e₂ (.head _)) (by decide)
    obtain ⟨_, _, _, msc, hrel_sc, hread⟩ := hsc_spec ⟨42, 4⟩ rfl
    exact ⟨la₂, msc, hfind₂, hrel_sc, hread⟩
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, rfl, hmem₂⟩

/-- Body for multi-element (`count = 2 > 1`) non-zero-offset (`offsetBytes = 2`)
uninitialized-source divergence on `_2 : u64 = .uninit`:
`_3 = &raw mut _2; _4 = copy _3 as *mut u8; _5 = Offset(copy _4, 2_usize);
copy_nonoverlapping::<u8>(copy _4, copy _5, 2_usize)`. -/
def copyUninitRangeDivBody : CapturedMir :=
  ptr6Body unitK u64K rawMutU64K rawMutU8K rawMutU8K
    [mkStmt42 (.assign (local42 3) (.rawPtr .mut (local42 2))),
     mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 5)
       (.binaryOp .offset (.copy (local42 4)) (.constant (constInt usizeK 2 8)))),
     copyStmt 4 5 2]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_uninit_src_range_divergence`**: real 4-step
execution with `count = 2 > 1` and destination `offsetBytes = 2` on `.uninit`
`_2 : u64`, exercising `step_intrinsic_copyNonOverlapping_uninit_src_range_divergence`:
Anneal reports `.fail .ub` while `lean-miri` steps with `.ok true`. -/
theorem wit_lm4_2_copy_nonoverlapping_uninit_src_range_divergence :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let b := copyUninitRangeDivBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 1 Witness.lm31AllocId1
      stepMirFn b (ptr6AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr6MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFnLM4_2 b s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) := by
  let b := copyUninitRangeDivBody
  have hrel₀ : StateRel b (ptr6AnnealPre b) (ptr6MiriPre b unitK) :=
    ptr6_stateRel unitK u64K rawMutU64K rawMutU8K rawMutU8K
      [mkStmt42 (.assign (local42 3) (.rawPtr .mut (local42 2))),
       mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 5)
         (.binaryOp .offset (.copy (local42 4)) (.constant (constInt usizeK 2 8)))),
       copyStmt 4 5 2]
      .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr6MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 2 :=
    fun tf htf => ⟨ptr6_all_immediate b _ tf htf 3, ptr6_all_immediate b _ tf htf 2⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr6AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr6AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr6MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 2 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr6_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 3 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .init ptr2]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₂ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₂)
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 5 (by decide), himm₂ tf₂ htf₂ 4 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
    (fun ptrVal sc _ tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨2, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constInt usizeK 2 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  obtain ⟨ha₄, m₄, hm₄⟩ := step_intrinsic_copyNonOverlapping_uninit_src_range_divergence
    (pointeeTy := tyOf u8K) hrel₃ hphase rfl rfl rfl rfl
    (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 4 (by decide))
    rfl rfl (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 5 (by decide))
    usize_integral (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    u8_copyPointee (srcPtr := { allocId := 1, offsetBytes := 0 })
    (dstPtr := { allocId := 1, offsetBytes := 2 }) (countSc := ⟨2, 8⟩)
    (e_s := entry) (e_d := entry) rfl rfl rfl rfl (Or.inl ⟨_, rfl, rfl⟩) (by decide)
    (.head _) rfl (.head _) rfl rfl rfl u64_integral u64_integral (by decide) (by decide)
    rfl (by simp [s₃, mkPtrState, entry, rawPtrAllocMapEntry, get?])
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, ha₄, hm₄⟩

/-- Body for multi-element (`count = 2 > 1`) non-zero-offset (`offsetBytes = 2`)
Tree Borrows `.frozen` permission divergence on `_1 : u64 = 42_u64`:
`_3 = &raw const _1; _4 = copy _3 as *const u8; _5 = copy _4 as *mut u8;
_5 = Offset(copy _5, 2_usize); copy_nonoverlapping::<u8>(copy _4, copy _5, 2_usize)`. -/
def copyPermRangeDivBody : CapturedMir :=
  ptr6Body unitK u32K rawConstU64K rawConstU8K rawMutU8K
    [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
     mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawConstU8K))),
     mkStmt42 (.assign (local42 5) (.cast .ptrToPtr (.copy (local42 4)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 5)
       (.binaryOp .offset (.copy (local42 5)) (.constant (constInt usizeK 2 8)))),
     copyStmt 4 5 2]
    .return_

/-- **`wit_lm4_2_copy_nonoverlapping_perm_range_divergence`**: real 5-step
execution with `count = 2 > 1` and destination `offsetBytes = 2` on a `.frozen`
borrow of `_1 : u64`, exercising `step_intrinsic_copyNonOverlapping_perm_range_divergence`:
Anneal reports `.fail .ub` while `lean-miri` steps with `.ok true`. -/
theorem wit_lm4_2_copy_nonoverlapping_perm_range_divergence :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := copyPermRangeDivBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr6AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr6MiriPre b unitK) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFnLM4_2 b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) := by
  let b := copyPermRangeDivBody
  have hrel₀ : StateRel b (ptr6AnnealPre b) (ptr6MiriPre b unitK) :=
    ptr6_stateRel unitK u32K rawConstU64K rawConstU8K rawMutU8K
      [mkStmt42 (.assign (local42 3) (.rawPtr .not (local42 1))),
       mkStmt42 (.assign (local42 4) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawConstU8K))),
       mkStmt42 (.assign (local42 5) (.cast .ptrToPtr (.copy (local42 4)) (tyOf rawMutU8K))),
       mkStmt42 (.assign (local42 5)
         (.binaryOp .offset (.copy (local42 5)) (.constant (constInt usizeK 2 8)))),
       copyStmt 4 5 2]
      .return_
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr6MiriPre b unitK).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨ptr6_all_immediate b _ tf htf 3, ptr6_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  let s₁ := mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr6AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr6AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr6MiriPre b unitK).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (ptr6_all_immediate b _ _ rfl k)
  let s₂ := mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 3 (by decide)⟩)
    (fun _ h => by simp [s₁, mkPtrState, get?] at h)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  let s₃ := mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .init ptr0]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hsim₃ := step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 5 (by decide), himm₂ tf₂ htf₂ 4 (by decide)⟩)
    (fun _ h => by simp [s₂, mkPtrState, get?] at h)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkPtrState b 0 4
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .init ptr2]
    [entry.toBorrowEntry] 2
  have hs₄ : stepMirFn b s₃ = .step s₄ :=
    stepMirFn_binOp_offset_const_eq entry (declOf u64K) hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
  have hsim₄ := step_binOp_offset_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := tyOf usizeK) (Or.inl rfl)
    (fun tf₃ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₃)
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 5 (by decide)⟩)
    (fun _ h => by simp [s₃, mkPtrState, get?] at h)
    (fun ptrVal sc _ tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₃, mkPtrState, ptr0, get?] using hp.symm
      have hsc' : sc = ⟨2, 8⟩ := by
        change evalOperand s₃.frame.locals (.constant (constInt usizeK 2 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = declOf u64K := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₃ (by rintro _ ⟨⟩)
    rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  obtain ⟨ha₅, m₅, hm₅⟩ := step_intrinsic_copyNonOverlapping_perm_range_divergence
    (pointeeTy := tyOf u8K) hrel₄ hphase rfl rfl rfl rfl
    (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 4 (by decide))
    rfl rfl (fun tf₄ htf₃ => himm₄ tf₄ htf₃ 5 (by decide))
    usize_integral (fun tf₄ _ => constInt_wellTyped usize_integral valid8 (by decide) rfl b rfl tf₄)
    u8_copyPointee (srcPtr := { allocId := 1, offsetBytes := 0 })
    (dstPtr := { allocId := 1, offsetBytes := 2 }) (countSc := ⟨2, 8⟩)
    (e_s := entry) (e_d := entry) rfl rfl rfl rfl (Or.inl ⟨_, rfl, rfl⟩) (by decide)
    (.head _) rfl (.head _) rfl rfl rfl u64_integral u64_integral (by decide) (by decide)
    (fun _ => Or.inl (by decide))
    (by simp [s₄, mkPtrState, entry, rawPtrAllocMapEntry, get?])
    (by simp [s₄, mkPtrState, entry, rawPtrAllocMapEntry, get?])
    (Or.inr (by simp [s₄, mkPtrState, entry, rawPtrAllocMapEntry, get?]))
    (Or.inr (Or.inl rfl))
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, ha₅, hm₅⟩

/-! ## 14. Pointee `layoutIdx := 0` and `isSingleDirect` Regression Witnesses -/

/-- Realistic `rustc-capture` layout table for a unit-returning function with an
ADT `struct S(u32)` (`size = 4, align = 4`): `TypeLayout[0]` is `()` (`size = 0,
align = 1`), `TypeLayout[1]` is `S`, and `TypeLayout[2]` is `*const S / *mut S`. -/
def adtUnitFirstLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [{ size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
         fields := .arbitrary .nil .nil, variants := .single 0, isUninhabited := false },
       { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
         fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0, isUninhabited := false },
       { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
         fields := .primitive, variants := .single 0, isUninhabited := false }] }

def sAdtK : RigidTy := .adt "S" []

def adtDeclAt (k : RigidTy) (idx : Nat) : LocalDecl :=
  { mutability := .mut, ty := { kind := k, layoutIdx := idx }, debugName := none }

def adtPointeeDecls : List LocalDecl :=
  [adtDeclAt unitK 0,
   adtDeclAt sAdtK 1,
   adtDeclAt sAdtK 1,
   adtDeclAt (.rawPtr .not sAdtK) 2,
   adtDeclAt (.rawPtr .mut sAdtK) 2,
   adtDeclAt (.rawPtr .not sAdtK) 2]

def adtPointeeState : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.aggregate 0 [.scalar ⟨7, 4⟩]),
         .init (.aggregate 0 [.scalar ⟨0, 4⟩]),
         .init (.ptr ⟨1, 0⟩ 8),
         .init (.ptr ⟨2, 0⟩ 8),
         .uninit] }
    memory := {
      emptyMemory with
      borrows :=
        [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen },
         { tag := 2, targetLocal := 2, targetProjection := [], perm := .active }]
      nextTag := 3 } }

/-- **`wit_lm4_2_adt_pointee_copy_write_offset_unsupported`**: when the pointee
type of `*const S` / `*mut S` is an ADT `S` (`struct S(u32)`) whose layout is
not determined by `rigidTyKindByteSize` / `rigidTyKindAlignBytes`, none of
`evalCopyNonOverlappingWithCount`, `evalWriteBytesCall`, or `evalArithOffsetCall`
ever consults `LayoutTable[0]` (`()` of size `0`) on `pointeeTyOf`'s synthetic
placeholder `layoutIdx := 0`; all three fail closed with `MirStepNode.unsupported`
(including on `count = 1`, `count = 1000`, and dangling/null pointers). -/
theorem wit_lm4_2_adt_pointee_copy_write_offset_unsupported :
    evalCopyNonOverlappingWithCountLM4_2 adtPointeeState (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      adtPointeeDecls adtUnitFirstLayouts (.ptr ⟨1, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 1
      adtPointeeState.frame.locals = MirStepNode.unsupported ∧
    evalCopyNonOverlappingWithCountLM4_2 adtPointeeState (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      adtPointeeDecls adtUnitFirstLayouts (.ptr ⟨1, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 1000
      adtPointeeState.frame.locals = MirStepNode.unsupported ∧
    evalCopyNonOverlappingWithCountLM4_2 adtPointeeState (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      adtPointeeDecls adtUnitFirstLayouts (.ptr ⟨99, 0⟩ 8) (.scalar ⟨0, 8⟩) 1
      adtPointeeState.frame.locals = MirStepNode.unsupported ∧
    evalWriteBytesCall adtPointeeState (.copy ⟨4, []⟩) (.scalar ⟨0, 8⟩) ⟨0xFF, 1⟩ ⟨1, 8⟩
      adtPointeeState.frame.locals 1 adtPointeeDecls adtUnitFirstLayouts =
      MirStepNode.unsupported ∧
    evalWriteBytesCall adtPointeeState (.copy ⟨4, []⟩) (.ptr ⟨2, 0⟩ 8) ⟨0xFF, 1⟩ ⟨1, 8⟩
      adtPointeeState.frame.locals 1 adtPointeeDecls adtUnitFirstLayouts =
      MirStepNode.unsupported ∧
    evalArithOffsetCall adtPointeeState (.copy ⟨3, []⟩) (.ptr ⟨1, 0⟩ 8) (.scalar ⟨1, 8⟩)
      adtPointeeState.frame.locals ⟨5, []⟩ 1 adtPointeeDecls adtUnitFirstLayouts =
      MirStepNode.unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def u8Array4ToU32Decls : List LocalDecl :=
  [declOf unitK,
   declOf (.array u8K 4),
   declOf u32K,
   declOf rawConstU8K,
   declOf rawMutU8K]

def u8Array4ToU32PreState : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨4, 1⟩]),
         .init (.scalar ⟨0, 4⟩),
         .init (.ptr ⟨1, 0⟩ 8),
         .init (.ptr ⟨2, 0⟩ 8)] }
    memory := {
      emptyMemory with
      borrows :=
        [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen },
         { tag := 2, targetLocal := 2, targetProjection := [], perm := .active }]
      nextTag := 3 } }

/-- **`wit_lm4_2_copy_nonoverlapping_u8_array_to_u32_ok`**: copying `count = 4`
`u8` bytes from `_1 : [u8; 4] = [1, 2, 3, 4]` into `_2 : u32 = 0` via
`copy_nonoverlapping::<u8>(&raw const _1 as *const u8, &raw mut _2 as *mut u8, 4)`
does not take `evalCopySingleDirect` (`Nat.beq 4 1 = false`), and instead
decodes the 4 little-endian bytes into `_2 = .init (.scalar ⟨0x04030201, 4⟩)`
(never placing an untyped `[u8; 4]` `.aggregate` into the `u32` local). -/
theorem wit_lm4_2_copy_nonoverlapping_u8_array_to_u32_ok :
    ∃ s' : MachineState,
      evalCopyNonOverlapping u8Array4ToU32PreState (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
        (.constant (constInt usizeK 4 8)) u8Array4ToU32Decls emptyLayoutTable = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.scalar ⟨0x04030201, 4⟩)) :=
  ⟨_, rfl, rfl⟩

/-- **`wit_lm4_2_copy_nonoverlapping_count2_not_single_direct`**: a `count = 2`
copy at offset `0` on single-element `bool` locals is rejected out-of-bounds
with `MirStepNode.fail .ub` (`Nat.beq 2 1 = false`). -/
theorem wit_lm4_2_copy_nonoverlapping_count2_not_single_direct :
    let decls := [declOf unitK, declOf .bool, declOf .bool,
      declOf (.rawPtr .not .bool), declOf (.rawPtr .mut .bool)]
    let st : MachineState := {
      frame := {
        blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0, 1⟩),
          .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] }
      memory := {
        emptyMemory with
        borrows :=
          [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen },
           { tag := 2, targetLocal := 2, targetProjection := [], perm := .active }]
        nextTag := 3 } }
    evalCopyNonOverlappingLM4_2 st (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      (.constant (constInt usizeK 2 8)) decls emptyLayoutTable = MirStepNode.fail .ub := by
  rfl

/-- Body for Stage-1 provenance-preserving raw-pointer `copy_nonoverlapping`:
`_1 : *mut u64`, `_2 : *mut u64`, `_3 : *const *mut u64`, `_4 : *mut *mut u64`. -/
def copyStage1RawPtrBody : CapturedMir where
  defPath := "lm_4_2_witness::copy_stage1_rawptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf unitK, declOf rawMutU64K, declOf rawMutU64K,
    declOf (.rawPtr .not rawMutU64K), declOf (.rawPtr .mut rawMutU64K)]
  basicBlocks := [
    { statements := [copyStmt 3 4 1], terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm4_2_copy_nonoverlapping_stage1_rawPtr_ok`**: positive Stage-1
provenance-preserving `CopyNonOverlapping` witness exercising
`step_intrinsic_copyNonOverlapping_stage1_rawPtr_simulation` on **Stage-1
`stepMirFn`** (`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`): copying
`count = 1` element of pointee type `*mut u64` from `_1 = .init (.ptr ⟨9, 16⟩ 8)`
into `_2` copies `.init (.ptr ⟨9, 16⟩ 8)` into `_2` with its `ProvenancePtr`
`⟨9, 16⟩` preserved intact (`PtrRel`). -/
theorem wit_lm4_2_copy_nonoverlapping_stage1_rawPtr_ok :
    let b := copyStage1RawPtrBody
    let e_p := rawPtrAllocMapEntry b.localDecls b.layouts .mut 0 9 Witness.lm31AllocId1
    let e_s := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
    let e_d := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
    let p : ProvenancePtr := { allocId := 9, offsetBytes := 16 }
    let mptr : Miri.Memory.Pointer AnnealProv :=
      { offset := Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 16)
        provenance := .concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one }
    let s : MachineState := {
      frame := {
        blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.ptr p 8), .uninit,
          .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
          .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] }
      memory := {
        emptyMemory with
        borrows := [e_s.toBorrowEntry, e_d.toBorrowEntry, e_p.toBorrowEntry]
        nextTag := 10 } }
    ∃ s',
      stepMirFn b s = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr p 8)) ∧
      PtrRel [e_s, e_d, e_p] p mptr := by
  intro b e_p e_s e_d p mptr s
  have hptrRel : PtrRel [e_s, e_d, e_p] p mptr :=
    .mk Witness.lm31AllocId1 Miri.Memory.BorTag.one rfl (by decide) (by decide) rfl
      ⟨e_p, .tail _ (.tail _ (.head _)), rfl, rfl⟩
  obtain ⟨hstep, hrel⟩ :=
    step_intrinsic_copyNonOverlapping_stage1_rawPtr_simulation
      (body := b) (s := s) (allocMap := [e_s, e_d, e_p])
      (srcIdx := 3) (dstIdx := 4) (e_s := e_s) (e_d := e_d)
      (p := p) (mptr := mptr)
      rfl (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Or.inl ⟨_, rfl, rfl⟩) rfl rfl rfl (by nofun) (Or.inl rfl)
      (by decide) (by decide) rfl hptrRel rfl (by nofun) rfl rfl rfl rfl
  exact ⟨_, hstep, rfl, hrel⟩

end WitnessLM4_2

end LeanMiriSpec.Correspondence
