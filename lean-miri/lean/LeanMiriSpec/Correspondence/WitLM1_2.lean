/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.Witness

/-!
# Non-Vacuity Witnesses for the `LM-1.2` Correspondence

Three single-local `Runtime(PostCleanup)` bodies whose first action is an
`LM-1.2` construct. For each, the Anneal state built by `initMachineState` and
the matching root-frame `lean-miri` state satisfy every premise of the
corresponding step theorem, and both machines run the body to the same result:

* `lm12SwitchBody d`: `SwitchInt` on `const d_u8` with cases `0` and `7`
  (`step_terminator_switchInt_simulation`); `d = 7` takes the case, `d = 9`
  falls back to `otherwise`;
* `lm12BoolCmpBody`: `_0 = Lt(const false, const true)` on `bool`
  (`step_assign_lm1_2_simulation`, `WellTypedLM12Stmt.boolCmp`);
* `lm12CastBody`: `_0 = const -1_i8 as i16 (IntToInt)`, a sign extension to
  `0xFFFF` (`step_assign_lm1_2_simulation`, `WellTypedLM12Stmt.intToInt`);
  `lm12Cast_shapes_agree` also runs truncation, zero extension, and
  `bool -> int` casts on both machines.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

def lm12BoolLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def lm12I16Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def lm12FnAbi (ret : TypeLayout) : FnAbi :=
  { args := [], ret := { layout := ret, mode := .direct }, conv := .rust, canUnwind := false }

def lm12I16Ty : Ty := { kind := .int .i16, layoutIdx := 0 }
def lm12I16Decl : LocalDecl := { mutability := .mut, ty := lm12I16Ty, debugName := none }
def lm12ConstBool (b : Bool) : ConstOperand :=
  { ty := boolTy, val := .scalar (.int (boolToScalar b)) }

/-- `lean-miri`'s root frame on entry to a body whose only local is the return
place `_0` of type `retTy`, live and uninitialized. -/
def lm12Frame (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm12MiriInit (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[lm12Frame body retTy]⟩, machine := AnnealMachine.empty }

/-- The single-local entry states of Anneal and `lean-miri` are `StateRel`-related. -/
theorem lm12_stateRel_init (body : CapturedMir) (decl0 : LocalDecl)
    (hdecls : body.localDecls = [decl0])
    (hcal : (initMachineState body []).memory.activeCallee = none)
    (hstack : (initMachineState body []).memory.callStack = .nil)
    (hbor : (initMachineState body []).memory.borrows = .nil)
    (hprot : (initMachineState body []).memory.activeProtectors = .nil)
    (hcaller : (initMachineState body []).memory.callerLocals = .nil)
    (hframe0 : (initMachineState body []).frame =
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }) :
    StateRel body (initMachineState body []) (lm12MiriInit body decl0.ty) := by
  refine StateRel.mk (lm12Frame body decl0.ty) rfl rfl ⟨translateTy decl0.ty, rfl⟩ ?_
    hcal hstack hbor hprot hcaller (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | _ + 1 => rintro ⟨⟩)
  refine
    { body_eq := rfl
      location_eq := by rw [hframe0]; rfl
      af_locals_len := by rw [hframe0, hdecls]; rfl
      mf_locals_size := by rw [hdecls]; rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  rw [hframe0] at hslot
  rw [hdecls] at hdecl
  match i with
  | 0 =>
    have hd : decl = decl0 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm12Frame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | n + 1 =>
    simp [get?] at hdecl

theorem lm12Frame_immediate (body : CapturedMir) (retTy : Ty) (j : Nat) :
    IsImmediateFrameLocal (lm12Frame body retTy) j := by
  intro mls hmls mp hmp
  match j with
  | 0 =>
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm12Frame] using hmls.symm
    subst hm
    cases hmp
  | n + 1 =>
    simp [lm12Frame] at hmls

theorem lm12_frames_eq {body : CapturedMir} {retTy : Ty}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm12MiriInit body retTy).stack.frames = #[tf]) : tf = lm12Frame body retTy := by
  injection h with h_arr
  injection h_arr with h_eq _
  exact h_eq.symm

/-! ## `SwitchInt` -/

/-- MIR of `fn switch() -> u8 { match d { 0 => 10, 7 => 20, _ => 30 } }`:
```text
bb0: switchInt(const d_u8) -> [0: bb1, 7: bb2, otherwise: bb3]
bb1: _0 = const 10_u8; return
bb2: _0 = const 20_u8; return
bb3: _0 = const 30_u8; return
``` -/
def lm12SwitchBody (d : Nat) : CapturedMir where
  defPath := "lm_1_2_witness::switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.constant (constU8 d))
        { branches := [(0, 1), (7, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.constant (constU8 10))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.constant (constU8 20))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.constant (constU8 30))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi0
  layouts := emptyLayoutTable
  allocations := []

theorem lm12Switch_stateRel (d : Nat) :
    StateRel (lm12SwitchBody d) (initMachineState (lm12SwitchBody d) [])
      (lm12MiriInit (lm12SwitchBody d) u8Ty) :=
  lm12_stateRel_init _ u8Decl rfl rfl rfl rfl rfl rfl rfl

/-- Every premise of `step_terminator_switchInt_simulation` holds on entry to
`lm12SwitchBody d` for every `d < 256`. -/
theorem lm12Switch_step_applies (d : Nat) (hd : d < 256) :
    StepObsRel (lm12SwitchBody d) (lm12MiriInit (lm12SwitchBody d) u8Ty)
      (stepMirFn (lm12SwitchBody d) (initMachineState (lm12SwitchBody d) []))
      (Miri.Interpreter.Step.step
        (annealStepHooks (lm12SwitchBody d).localDecls (lm12SwitchBody d).layouts) ()
        (lm12MiriInit (lm12SwitchBody d) u8Ty)) := by
  have hu8 : IsPrimScalarTy u8Ty := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  refine step_terminator_switchInt_simulation (lm12Switch_stateRel d) (fun p h => nomatch h)
    (bb := (lm12SwitchBody d).basicBlocks.head (by simp [lm12SwitchBody])) rfl rfl rfl rfl
    (ty := u8Ty) (Or.inr (Or.inr ⟨.u8, rfl⟩)) ?_ ?_
  · intro tf _
    exact .constScalar (constU8 d) ⟨d, 1⟩ rfl hu8 (Or.inl rfl) hd rfl
      (fun h => nomatch h) (fun h => nomatch h)
  · intro v b hmem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by decide, fun h => nomatch h⟩
    · exact ⟨by decide, fun h => nomatch h⟩

/-- Both machines take case `7` of `lm12SwitchBody 7` and return `20`. -/
theorem lm12Switch_case_agrees :
    annealOutcomeScalarBits 1
        (runAnnealBounded (lm12SwitchBody 7) 4 (initMachineState (lm12SwitchBody 7) [])) =
      some 20 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded (lm12SwitchBody 7) 4 (lm12MiriInit (lm12SwitchBody 7) u8Ty)) =
      some 20 := by
  decide

/-- Neither case matches `9`: both machines fall back to `otherwise` and return `30`. -/
theorem lm12Switch_otherwise_agrees :
    annealOutcomeScalarBits 1
        (runAnnealBounded (lm12SwitchBody 9) 4 (initMachineState (lm12SwitchBody 9) [])) =
      some 30 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded (lm12SwitchBody 9) 4 (lm12MiriInit (lm12SwitchBody 9) u8Ty)) =
      some 30 := by
  decide

/-! ## `bool` comparison -/

/-- MIR of `fn lt() -> bool { false < true }`:
```text
bb0: _0 = Lt(const false, const true); return
``` -/
def lm12BoolCmpBody : CapturedMir where
  defPath := "lm_1_2_witness::bool_lt"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0)
        (.binaryOp .lt (.constant (lm12ConstBool false)) (.constant (lm12ConstBool true))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi lm12BoolLayout
  layouts := emptyLayoutTable
  allocations := []

theorem lm12BoolCmp_stateRel :
    StateRel lm12BoolCmpBody (initMachineState lm12BoolCmpBody [])
      (lm12MiriInit lm12BoolCmpBody boolTy) :=
  lm12_stateRel_init _ boolDecl rfl rfl rfl rfl rfl rfl rfl

theorem lm12ConstBool_wellTyped (b : Bool)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand lm12BoolCmpBody tf (.constant (lm12ConstBool b)) boolTy :=
  .constScalar (lm12ConstBool b) (boolToScalar b) rfl (Or.inl rfl) (Or.inl (by cases b <;> rfl))
    (by cases b <;> decide) (by cases b <;> rfl) (fun _ => by cases b <;> decide)
    (fun h => nomatch h)

/-- Every premise of `step_assign_lm1_2_simulation` holds on entry to
`lm12BoolCmpBody`. -/
theorem lm12BoolCmp_step_applies :
    StepRel lm12BoolCmpBody (lm12MiriInit lm12BoolCmpBody boolTy)
      (stepMirFn lm12BoolCmpBody (initMachineState lm12BoolCmpBody []))
      (Miri.Interpreter.Step.step
        (annealStepHooks lm12BoolCmpBody.localDecls lm12BoolCmpBody.layouts) ()
        (lm12MiriInit lm12BoolCmpBody boolTy)) := by
  refine step_assign_lm1_2_simulation lm12BoolCmp_stateRel (fun p h => nomatch h) rfl rfl ?_
  intro tf htf
  rw [lm12_frames_eq htf]
  exact .boolCmp _ 0 boolDecl .lt _ _ boolTy boolTy rfl rfl (lm12Frame_immediate _ _ 0)
    (Or.inr (Or.inr (Or.inl rfl))) (lm12ConstBool_wellTyped false _)
    (lm12ConstBool_wellTyped true _) rfl rfl rfl

/-- Both machines evaluate `false < true` and return `true` (`0x01`). -/
theorem lm12BoolCmp_returns_agree :
    annealOutcomeScalarBits 1
        (runAnnealBounded lm12BoolCmpBody 3 (initMachineState lm12BoolCmpBody [])) = some 1 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded lm12BoolCmpBody 3 (lm12MiriInit lm12BoolCmpBody boolTy)) = some 1 := by
  decide

/-! ## `IntToInt` cast -/

/-- MIR of `fn cast() -> T { c as T }` for a constant `c`:
```text
bb0: _0 = const c as T (IntToInt); return
``` -/
def lm12CastBodyOf (c : ConstOperand) (dstDecl : LocalDecl) (ret : TypeLayout) : CapturedMir where
  defPath := "lm_1_2_witness::cast"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [dstDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.cast .intToInt (.constant c) dstDecl.ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi ret
  layouts := emptyLayoutTable
  allocations := []

/-- `fn widen() -> i16 { -1_i8 as i16 }`, a sign extension. -/
def lm12CastBody : CapturedMir := lm12CastBodyOf (constI8W 0xFF) lm12I16Decl lm12I16Layout

theorem lm12Cast_stateRel :
    StateRel lm12CastBody (initMachineState lm12CastBody [])
      (lm12MiriInit lm12CastBody lm12I16Ty) :=
  lm12_stateRel_init _ lm12I16Decl rfl rfl rfl rfl rfl rfl rfl

/-- Every premise of `step_assign_lm1_2_simulation` holds on entry to
`lm12CastBody`. -/
theorem lm12Cast_step_applies :
    StepRel lm12CastBody (lm12MiriInit lm12CastBody lm12I16Ty)
      (stepMirFn lm12CastBody (initMachineState lm12CastBody []))
      (Miri.Interpreter.Step.step
        (annealStepHooks lm12CastBody.localDecls lm12CastBody.layouts) ()
        (lm12MiriInit lm12CastBody lm12I16Ty)) := by
  have hi8 : IsPrimScalarTy i8TyW := Or.inr (Or.inr (Or.inl ⟨.i8, rfl⟩))
  refine step_assign_lm1_2_simulation lm12Cast_stateRel (fun p h => nomatch h) rfl rfl ?_
  intro tf htf
  rw [lm12_frames_eq htf]
  exact .intToInt _ 0 lm12I16Decl _ i8TyW rfl rfl (lm12Frame_immediate _ _ 0)
    (.constScalar (constI8W 0xFF) ⟨0xFF, 1⟩ rfl hi8 (Or.inl rfl) (by decide) rfl
      (fun h => nomatch h) (fun h => nomatch h))
    (Or.inr (Or.inl ⟨.i8, rfl⟩)) (Or.inl ⟨.i16, rfl⟩)

/-- Both machines sign-extend `-1_i8` and return `0xFFFF_i16`. -/
theorem lm12Cast_returns_agree :
    annealOutcomeScalarBits 2
        (runAnnealBounded lm12CastBody 3 (initMachineState lm12CastBody [])) = some 0xFFFF ∧
    miriOutcomeScalarBits 2
        (runMiriBounded lm12CastBody 3 (lm12MiriInit lm12CastBody lm12I16Ty)) = some 0xFFFF := by
  decide

def lm12I32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
def lm12I32Decl : LocalDecl := { mutability := .mut, ty := lm12I32Ty, debugName := none }
def lm12I32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

/-- The other `IntToInt` shapes agree on both machines: truncation
(`0x1234_u16 as u8 = 0x34`), zero extension (`0xFF_u8 as u16 = 0x00FF`, where a
sign extension would give `0xFFFF`), and `bool -> int` (`true as i32 = 1`). -/
theorem lm12Cast_shapes_agree :
    (annealOutcomeScalarBits 1
        (runAnnealBounded (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) 3
          (initMachineState (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) [])) = some 0x34 ∧
      miriOutcomeScalarBits 1
        (runMiriBounded (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) 3
          (lm12MiriInit (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) u8Ty)) = some 0x34) ∧
    (annealOutcomeScalarBits 2
        (runAnnealBounded (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) 3
          (initMachineState (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) [])) =
        some 0x00FF ∧
      miriOutcomeScalarBits 2
        (runMiriBounded (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) 3
          (lm12MiriInit (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) u16Ty)) =
        some 0x00FF) ∧
    (annealOutcomeScalarBits 4
        (runAnnealBounded (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) 3
          (initMachineState (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) [])) =
        some 1 ∧
      miriOutcomeScalarBits 4
        (runMiriBounded (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) 3
          (lm12MiriInit (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout)
            lm12I32Ty)) =
        some 1) := by
  decide

end LeanMiriSpec.Correspondence.Witness
