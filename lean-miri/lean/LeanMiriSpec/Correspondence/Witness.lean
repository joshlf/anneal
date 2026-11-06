/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation

/-!
# Non-Vacuity Witness for the `LM-1.1` Correspondence

`step_wellTypedBody_simulation` and `step_wellTypedBody_bisim` would hold
vacuously if `StateRel`, `WellTypedBody`, `ValidFrameLocation`, or
`NonAddrTakenImmediate` could never be satisfied together. This module
exhibits a concrete `Runtime(PostCleanup)` body, the Anneal state that
`initMachineState` builds for it, and the matching root-frame `lean-miri`
state, and proves every premise. The correspondence theorems therefore apply
to it, for every divisor below `256`, including the divisor `0` whose third
statement is undefined behavior.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def u8Decl : LocalDecl := { mutability := .mut, ty := u8Ty, debugName := none }
def mkStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "lm-1.1-witness" }
def mkTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "lm-1.1-witness" }
def local_ (i : Nat) : Place := { local_ := i, projection := [] }
def constU8 (n : Nat) : ConstOperand := { ty := u8Ty, val := .scalar (.int ⟨n, 1⟩) }

def u8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbi0 : FnAbi :=
  { args := [], ret := { layout := u8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of `fn div() -> u8 { let x: u8 = 7; x / divisor }`,
with the divisor-zero check elided so that `divisor = 0` reaches `Div`:
```text
bb0: StorageLive(_1); _1 = const 7_u8; _0 = Div(copy _1, const divisor_u8);
     StorageDead(_1); return
``` -/
def divBody (divisor : Nat) : CapturedMir where
  defPath := "lm_1_1_witness::div"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.constant (constU8 7)))),
        mkStmt (.assign (local_ 0) (.binaryOp .div (.copy (local_ 1)) (.constant (constU8 divisor)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi0
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's initial state for `divBody`. -/
def annealInit (divisor : Nat) : MachineState := initMachineState (divBody divisor) []

/-- `lean-miri`'s root frame for `divBody` on entry: the return place `_0` is
always live (`.immediate .uninit`) and `_1`, which has storage statements,
starts dead. -/
def miriFrame (divisor : Nat) : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (divBody divisor)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u8Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri`'s initial single-threaded state for `divBody`. -/
def miriInit (divisor : Nat) : AnnealStepState :=
  { stack := ⟨#[miriFrame divisor]⟩, machine := Miri.Memory.MemoryState.empty }

theorem stateRel_init (divisor : Nat) :
    StateRel (divBody divisor) (annealInit divisor) (miriInit divisor) := by
  refine StateRel.mk (miriFrame divisor) rfl rfl ⟨translateTy u8Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u8Decl := by simpa [divBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [annealInit, initMachineState, divBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [miriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u8Decl := by simpa [divBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [annealInit, initMachineState, divBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [miriFrame] using hmls.symm
    subst hd hs hm
    exact .dead none (fun _ h => nomatch h)
  | n + 2 =>
    simp [divBody, get?] at hdecl

theorem wellTypedBody (divisor : Nat) (hd : divisor < 256) :
    WellTypedBody (divBody divisor) := by
  have hu8 : IsPrimScalarTy u8Ty := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hbits : ∀ n, n < 256 → n < scalarModulus 1 := fun n h => by
    rw [scalarModulus_eq_two_pow]; simpa using h
  have hconst : ∀ n, n < 256 →
      WellTypedScalarOperandSyn (divBody divisor) (fun _ => True) (.constant (constU8 n)) u8Ty :=
    fun n hn => .constScalar (constU8 n) ⟨n, 1⟩ rfl hu8 (Or.inl rfl) (hbits n hn) rfl
      (fun h => nomatch h)
  have hu8int : IsIntegralTy u8Ty (translateUintTy .u8) := .uint .u8 rfl
  refine ⟨(fun p h => by simp [divBody] at h), ?_⟩
  intro bb hbb
  simp only [divBody, List.mem_singleton] at hbb
  subst hbb
  refine ⟨rfl, ?_, Or.inr ⟨rfl, trivial, u8Decl, rfl, IsPrimScalarTy.size_ne_zero hu8⟩⟩
  intro stmt hstmt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
  rcases hstmt with rfl | rfl | rfl | rfl
  · exact .storageLive _ 1 u8Decl rfl rfl trivial
  · exact .assign _ 1 u8Decl _ rfl rfl trivial (.use _ _ (hconst 7 (by decide)))
  · exact .assign _ 0 u8Decl _ rfl rfl trivial
      (.binaryOp .div _ _ u8Ty u8Ty u8Ty
        (.copyLocal 1 u8Decl rfl (IsPrimScalarTy.size_ne_zero hu8) trivial)
        (hconst divisor hd)
        (.intArithOrBitwise .div u8Ty u8Ty u8Ty _
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
          hu8int hu8int hu8int))
  · exact .storageDead _ 1 u8Decl rfl rfl (by decide) trivial

/-- Every premise of the `LM-1.1` correspondence holds for `divBody` on entry,
so `step_wellTypedBody_bisim` applies to it. -/
theorem bisim_applies (divisor : Nat) (hd : divisor < 256) :
    ((∃ s', stepMirFn (divBody divisor) (annealInit divisor) = .step s' ∧
        StateRel (divBody divisor) s'
          (Miri.Interpreter.Step.step
            (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
            (miriInit divisor)).1) ↔
      ((Miri.Interpreter.Step.step
          (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
          (miriInit divisor)).2 = .ok true ∧
        (Miri.Interpreter.Step.step
          (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
          (miriInit divisor)).1.stack.frames ≠ #[])) ∧
    ((∃ retVal mem', stepMirFn (divBody divisor) (annealInit divisor) = .retNormal retVal mem') ↔
      ((Miri.Interpreter.Step.step
          (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
          (miriInit divisor)).2 = .ok true ∧
        (Miri.Interpreter.Step.step
          (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
          (miriInit divisor)).1.stack.frames = #[])) ∧
    (stepMirFn (divBody divisor) (annealInit divisor) = .fail .ub ↔
      ∃ msg, (Miri.Interpreter.Step.step
          (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) ()
          (miriInit divisor)).2 = .error (.undefinedBehavior msg)) ∧
    ((∃ s', stepMirFn (divBody divisor) (annealInit divisor) = .step s') ∨
      (∃ retVal mem', stepMirFn (divBody divisor) (annealInit divisor) = .retNormal retVal mem') ∨
      stepMirFn (divBody divisor) (annealInit divisor) = .fail .ub) :=
  step_wellTypedBody_bisim (wellTypedBody divisor hd) (stateRel_init divisor)
    ⟨_, rfl, Nat.zero_le _⟩
    (NonAddrTakenImmediate.of_live_nil _ (stateRel_init divisor) rfl)

/-! ## Concrete runs

Kernel evaluation (`decide`, no `native_decide`) of both machines on
`divBody`, independent of the simulation proofs: both reach undefined
behavior at `Div` when the divisor is `0`, and both return `7 / 2 = 3` when it
is `2`. -/

/-- Anneal's successor state after a silent step, if any. -/
def annealNext (divisor : Nat) (s : MachineState) : Option MachineState :=
  match stepMirFn (divBody divisor) s with
  | .tau (.running s') => some s'
  | _ => none

/-- `lean-miri`'s successor state after a step that continues (`.ok true`), if any. -/
def miriNext (divisor : Nat) (m : AnnealStepState) : Option AnnealStepState :=
  match Miri.Interpreter.Step.step
      (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) () m with
  | (m', .ok true) => some m'
  | _ => none

def annealRun (divisor : Nat) : Nat → MachineState → Option MachineState
  | 0, s => some s
  | n + 1, s => (annealNext divisor s).bind (annealRun divisor n)

def miriRun (divisor : Nat) : Nat → AnnealStepState → Option AnnealStepState
  | 0, m => some m
  | n + 1, m => (miriNext divisor m).bind (miriRun divisor n)

/-- Whether Anneal's next step reports undefined behavior. -/
def annealStepIsUB (divisor : Nat) (s : MachineState) : Bool :=
  match stepMirFn (divBody divisor) s with
  | .vis (.inl (.fail .ub)) _ => true
  | _ => false

/-- Whether `lean-miri`'s next step reports `StepError.undefinedBehavior`. -/
def miriStepIsUB (divisor : Nat) (m : AnnealStepState) : Bool :=
  match Miri.Interpreter.Step.step
      (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) () m with
  | (_, .error (.undefinedBehavior _)) => true
  | _ => false

/-- The `u8` value Anneal's next step returns from the root frame, if any. -/
def annealStepReturnsU8 (divisor : Nat) (s : MachineState) : Option Nat :=
  match stepMirFn (divBody divisor) s with
  | .ret (.normal (.scalar ⟨bits, 1⟩, _)) => some bits
  | _ => none

/-- The `u8` value in `lean-miri`'s return place `_0` if its next step pops
the root frame (`.ok true` with an empty stack). -/
def miriStepReturnsU8 (divisor : Nat) (m : AnnealStepState) : Option Nat :=
  match annealControlHooks.returnOperand () m,
      Miri.Interpreter.Step.step
        (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts) () m with
  | (_, .ok (.immediate (.scalar s))), (m', .ok true) =>
      if m'.stack.frames.isEmpty then
        match s.toScalarInt with
        | .ok sc => if sc.size == Miri.ABI.Size.ofBytes 1 then some sc.data.toNat else none
        | .error _ => none
      else none
  | _, _ => none

/-- Division by zero: after `StorageLive(_1)` and `_1 = const 7_u8`, both
machines report undefined behavior at `_0 = Div(copy _1, const 0_u8)`. -/
theorem divByZero_ub_agrees :
    (annealRun 0 2 (annealInit 0)).map (annealStepIsUB 0) = some true ∧
    (miriRun 0 2 (miriInit 0)).map (miriStepIsUB 0) = some true := by
  decide

/-- With divisor `2`, both machines run the four statements and return `3`. -/
theorem div_returns_agree :
    (annealRun 2 4 (annealInit 2)).bind (annealStepReturnsU8 2) = some 3 ∧
    (miriRun 2 4 (miriInit 2)).bind (miriStepReturnsU8 2) = some 3 := by
  decide

/-- Multi-step fuel-bounded bisimulation (`run_wellTypedBody_bisim`) instantiated
on `divBody` across arbitrary `fuel` steps, reaching `Div` UB at `fuel = 3`
(`divisor = 0`) and normal `return` at `fuel = 5` (`divisor = 2`). -/
theorem run_bisim_divBody (fuel : Nat) (divisor : Nat) (hd : divisor < 256) :
    ((∃ s', runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .running s') ↔
      (∃ m', runMiriBounded (divBody divisor) fuel (miriInit divisor) = .running m')) ∧
    (∀ s' m',
      runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .running s' →
      runMiriBounded (divBody divisor) fuel (miriInit divisor) = .running m' →
      StateRel (divBody divisor) s' m') ∧
    ((∃ retVal mem',
        runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .returned retVal mem') ↔
      (∃ m' retImm,
        runMiriBounded (divBody divisor) fuel (miriInit divisor) =
          .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .returned retVal mem' →
      runMiriBounded (divBody divisor) fuel (miriInit divisor) =
        .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? (divBody divisor).localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty (divBody divisor).layouts retVal retImm) ∧
    (runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .faulted .ub ↔
      ∃ m' msg,
        runMiriBounded (divBody divisor) fuel (miriInit divisor) =
          .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .running s') ∨
      (∃ retVal mem',
        runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .returned retVal mem') ∨
      runAnnealBounded (divBody divisor) fuel (annealInit divisor) = .faulted .ub) :=
  run_wellTypedBody_bisim fuel (wellTypedBody divisor hd) (stateRel_init divisor)
    ⟨_, rfl, Nat.zero_le _⟩
    (NonAddrTakenImmediate.of_live_nil _ (stateRel_init divisor) rfl)

/-! ## Multi-block signed `i8` witness (`Goto` + `INT_MIN / -1` UB & normal return) -/

def i8Ty : Ty := { kind := .int .i8, layoutIdx := 0 }
def i8Decl : LocalDecl := { mutability := .mut, ty := i8Ty, debugName := none }
def constI8 (bits : Nat) : ConstOperand := { ty := i8Ty, val := .scalar (.int ⟨bits, 1⟩) }

def i8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiI8 : FnAbi :=
  { args := [], ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- Multi-block `Runtime(PostCleanup)` MIR body computing `(-128_i8) / divisor`:
```text
bb0: StorageLive(_1); _1 = const (-128_i8); goto -> bb1
bb1: _0 = Div(copy _1, const divisor_i8); StorageDead(_1); return
```
When `divisorBits = 255` (`-1_i8`), `Div` triggers signed `INT_MIN / -1` overflow UB
at step 4; when `divisorBits = 2` (`2_i8`), execution returns `192` (`-64_i8`) at step 6. -/
def signedDivBody (divisorBits : Nat) : CapturedMir where
  defPath := "lm_1_1_witness::signed_div"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.constant (constI8 128))))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .div (.copy (local_ 1)) (.constant (constI8 divisorBits)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8
  layouts := emptyLayoutTable
  allocations := []

def annealSignedDivInit (divisorBits : Nat) : MachineState :=
  initMachineState (signedDivBody divisorBits) []

def miriSignedDivFrame (divisorBits : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (signedDivBody divisorBits)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy i8Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def miriSignedDivInit (divisorBits : Nat) : AnnealStepState :=
  { stack := ⟨#[miriSignedDivFrame divisorBits]⟩, machine := Miri.Memory.MemoryState.empty }

theorem stateRel_signedDiv (divisorBits : Nat) :
    StateRel (signedDivBody divisorBits)
      (annealSignedDivInit divisorBits)
      (miriSignedDivInit divisorBits) := by
  refine StateRel.mk (miriSignedDivFrame divisorBits) rfl rfl ⟨translateTy i8Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = i8Decl := by simpa [signedDivBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [annealSignedDivInit, initMachineState, signedDivBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [miriSignedDivFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = i8Decl := by simpa [signedDivBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [annealSignedDivInit, initMachineState, signedDivBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [miriSignedDivFrame] using hmls.symm
    subst hd hs hm
    exact .dead none (fun _ h => nomatch h)
  | n + 2 =>
    simp [signedDivBody, get?] at hdecl

theorem wellTyped_signedDiv (divisorBits : Nat) (hd : divisorBits < 256) :
    WellTypedBody (signedDivBody divisorBits) := by
  have hi8 : IsPrimScalarTy i8Ty := Or.inr (Or.inr (Or.inl ⟨.i8, rfl⟩))
  have hbits : ∀ n, n < 256 → n < scalarModulus 1 := fun n h => by
    rw [scalarModulus_eq_two_pow]; simpa using h
  have hconst : ∀ n, n < 256 →
      WellTypedScalarOperandSyn (signedDivBody divisorBits) (fun _ => True)
        (.constant (constI8 n)) i8Ty :=
    fun n hn => .constScalar (constI8 n) ⟨n, 1⟩ rfl hi8 (Or.inl rfl) (hbits n hn) rfl
      (fun h => nomatch h)
  have hi8int : IsIntegralTy i8Ty (translateIntTy .i8) := .int .i8 rfl
  refine ⟨(fun p h => by simp [signedDivBody] at h), ?_⟩
  intro bb hbb
  simp only [signedDivBody, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · refine ⟨rfl, ?_, Or.inl ⟨1, _, rfl, rfl⟩⟩
    intro stmt hstmt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
    rcases hstmt with rfl | rfl
    · exact .storageLive _ 1 i8Decl rfl rfl trivial
    · exact .assign _ 1 i8Decl _ rfl rfl trivial (.use _ _ (hconst 128 (by decide)))
  · refine ⟨rfl, ?_, Or.inr ⟨rfl, trivial, i8Decl, rfl, IsPrimScalarTy.size_ne_zero hi8⟩⟩
    intro stmt hstmt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
    rcases hstmt with rfl | rfl
    · exact .assign _ 0 i8Decl _ rfl rfl trivial
        (.binaryOp .div _ _ i8Ty i8Ty i8Ty
          (.copyLocal 1 i8Decl rfl (IsPrimScalarTy.size_ne_zero hi8) trivial)
          (hconst divisorBits hd)
          (.intArithOrBitwise .div i8Ty i8Ty i8Ty _
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
            hi8int hi8int hi8int))
    · exact .storageDead _ 1 i8Decl rfl rfl (by decide) trivial

theorem run_bisim_signedDiv (fuel : Nat) (divisorBits : Nat) (hd : divisorBits < 256) :
    ((∃ s', runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .running s') ↔
      (∃ m', runMiriBounded (signedDivBody divisorBits) fuel (miriSignedDivInit divisorBits) =
        .running m')) ∧
    (∀ s' m',
      runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .running s' →
      runMiriBounded (signedDivBody divisorBits) fuel (miriSignedDivInit divisorBits) =
        .running m' →
      StateRel (signedDivBody divisorBits) s' m') ∧
    ((∃ retVal mem',
        runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
          .returned retVal mem') ↔
      (∃ m' retImm,
        runMiriBounded (signedDivBody divisorBits) fuel (miriSignedDivInit divisorBits) =
          .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .returned retVal mem' →
      runMiriBounded (signedDivBody divisorBits) fuel (miriSignedDivInit divisorBits) =
        .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? (signedDivBody divisorBits).localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty (signedDivBody divisorBits).layouts retVal retImm) ∧
    (runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .faulted .ub ↔
      ∃ m' msg,
        runMiriBounded (signedDivBody divisorBits) fuel (miriSignedDivInit divisorBits) =
          .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .running s') ∨
      (∃ retVal mem',
        runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
          .returned retVal mem') ∨
      runAnnealBounded (signedDivBody divisorBits) fuel (annealSignedDivInit divisorBits) =
        .faulted .ub) :=
  run_wellTypedBody_bisim fuel (wellTyped_signedDiv divisorBits hd)
    (stateRel_signedDiv divisorBits)
    ⟨_, rfl, Nat.zero_le _⟩
    (NonAddrTakenImmediate.of_live_nil _ (stateRel_signedDiv divisorBits) rfl)

/-! ## Checked `(u16, bool)` `AddWithOverflow` witness (ABI-aligned scalar pair) -/

def u16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
def u16BoolTupleTy : Ty := { kind := .tuple [u16Ty.kind, .bool], layoutIdx := 0 }
def u16Decl : LocalDecl := { mutability := .mut, ty := u16Ty, debugName := none }
def u16BoolDecl : LocalDecl := { mutability := .mut, ty := u16BoolTupleTy, debugName := none }
def constU16 (n : Nat) : ConstOperand := { ty := u16Ty, val := .scalar (.int ⟨n, 2⟩) }

def u16BoolPairLayout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 2 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 16 false) { start := 0, end_ := 65535 })
        (.initialized (.int 8 false) { start := 0, end_ := 1 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }] [0, 1]
    variants := .single 0
    isUninhabited := false }

def u16BoolLayoutTable : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u16BoolPairLayout] }

def fnAbiU16Bool : FnAbi :=
  { args := []
    ret := { layout := u16BoolPairLayout, mode := .direct }
    conv := .rust
    canUnwind := false }

/-- `Runtime(PostCleanup)` MIR body computing `AddWithOverflow(65500_u16, rhs_u16)`
into a `(u16, bool)` return local `_0` whose ABI size is `4` (aligned from `3` up
to alignment `2`):
```text
bb0: StorageLive(_1); _1 = const 65500_u16;
     _0 = AddWithOverflow(copy _1, const rhs_u16);
     StorageDead(_1); return
``` -/
def addWithOverflowBody (rhs : Nat) : CapturedMir where
  defPath := "lm_1_1_witness::add_with_overflow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u16BoolDecl, u16Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.constant (constU16 65500)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .addWithOverflow (.copy (local_ 1)) (.constant (constU16 rhs)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU16Bool
  layouts := u16BoolLayoutTable
  allocations := []

def annealAddOvfInit (rhs : Nat) : MachineState :=
  initMachineState (addWithOverflowBody rhs) []

def miriAddOvfFrame (rhs : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (addWithOverflowBody rhs)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u16BoolTupleTy u16BoolLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def miriAddOvfInit (rhs : Nat) : AnnealStepState :=
  { stack := ⟨#[miriAddOvfFrame rhs]⟩, machine := Miri.Memory.MemoryState.empty }

theorem stateRel_addWithOverflow (rhs : Nat) :
    StateRel (addWithOverflowBody rhs) (annealAddOvfInit rhs) (miriAddOvfInit rhs) := by
  refine StateRel.mk (miriAddOvfFrame rhs) rfl rfl
    ⟨translateTy u16BoolTupleTy u16BoolLayoutTable, rfl⟩ ?_ rfl rfl rfl rfl rfl
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u16BoolDecl := by simpa [addWithOverflowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [annealAddOvfInit, initMachineState, addWithOverflowBody, initLocalsAux, get?]
        using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [miriAddOvfFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u16Decl := by simpa [addWithOverflowBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [annealAddOvfInit, initMachineState, addWithOverflowBody, initLocalsAux, get?]
        using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [miriAddOvfFrame] using hmls.symm
    subst hd hs hm
    exact .dead none (fun _ h => nomatch h)
  | n + 2 =>
    simp [addWithOverflowBody, get?] at hdecl

theorem wellTyped_addWithOverflow (rhs : Nat) (hrhs : rhs < 65536) :
    WellTypedBody (addWithOverflowBody rhs) := by
  have hu16 : IsPrimScalarTy u16Ty := Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))
  have hbits : ∀ n, n < 65536 → n < scalarModulus 2 := fun n h => by
    rw [scalarModulus_eq_two_pow]; simpa using h
  have hconst : ∀ n, n < 65536 →
      WellTypedScalarOperandSyn (addWithOverflowBody rhs) (fun _ => True)
        (.constant (constU16 n)) u16Ty :=
    fun n hn => .constScalar (constU16 n) ⟨n, 2⟩ rfl hu16 (Or.inr (Or.inl rfl))
      (hbits n hn) rfl (fun h => nomatch h)
  have hu16int : IsIntegralTy u16Ty (translateUintTy .u16) := .uint .u16 rfl
  refine ⟨(fun p h => by simp [addWithOverflowBody] at h), ?_⟩
  intro bb hbb
  simp only [addWithOverflowBody, List.mem_singleton] at hbb
  subst hbb
  have hsz0 : (translateTy u16BoolDecl.ty u16BoolLayoutTable).layout.size ≠ Miri.ABI.Size.ZERO := by
    decide
  refine ⟨rfl, ?_, Or.inr ⟨rfl, trivial, u16BoolDecl, rfl, hsz0⟩⟩
  intro stmt hstmt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
  rcases hstmt with rfl | rfl | rfl | rfl
  · exact .storageLive _ 1 u16Decl rfl rfl trivial
  · exact .assign _ 1 u16Decl _ rfl rfl trivial (.use _ _ (hconst 65500 (by decide)))
  · exact .assign _ 0 u16BoolDecl _ rfl rfl trivial
      (.binaryOp .addWithOverflow _ _ u16Ty u16Ty u16BoolTupleTy
        (.copyLocal 1 u16Decl rfl (IsPrimScalarTy.size_ne_zero hu16) trivial)
        (hconst rhs hrhs)
        (.intWithOverflow .addWithOverflow u16Ty u16Ty u16BoolTupleTy _
          (Or.inl rfl) hu16int hu16int (Or.inl ⟨[u16Ty.kind, .bool], rfl⟩) rfl))
  · exact .storageDead _ 1 u16Decl rfl rfl (by decide) trivial

theorem run_bisim_addWithOverflow (fuel : Nat) (rhs : Nat) (hrhs : rhs < 65536) :
    ((∃ s', runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .running s') ↔
      (∃ m', runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
        .running m')) ∧
    (∀ s' m',
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .running s' →
      runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) = .running m' →
      StateRel (addWithOverflowBody rhs) s' m') ∧
    ((∃ retVal mem',
        runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
          .returned retVal mem') ↔
      (∃ m' retImm,
        runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
          .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .returned retVal mem' →
      runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
        .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? (addWithOverflowBody rhs).localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty (addWithOverflowBody rhs).layouts retVal retImm) ∧
    (runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .faulted .ub ↔
      ∃ m' msg,
        runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
          .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .running s') ∨
      (∃ retVal mem',
        runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
          .returned retVal mem') ∨
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .faulted .ub) :=
  run_wellTypedBody_bisim fuel (wellTyped_addWithOverflow rhs hrhs)
    (stateRel_addWithOverflow rhs)
    ⟨_, rfl, Nat.zero_le _⟩
    (NonAddrTakenImmediate.of_live_nil _ (stateRel_addWithOverflow rhs) rfl)

/-! ## Concrete multi-step outcome checks (`decide`, zero `native_decide`) -/

def annealOutcomeIsUB : AnnealRunOutcome → Bool
  | .faulted .ub => true
  | _ => false

def miriOutcomeIsUB : MiriRunOutcome → Bool
  | .error _ (.undefinedBehavior _) => true
  | _ => false

def annealOutcomeScalarBits (sizeBytes : Nat) : AnnealRunOutcome → Option Nat
  | .returned (.scalar ⟨bits, sb⟩) _ => if sb == sizeBytes then some bits else none
  | _ => none

def miriOutcomeScalarBits (sizeBytes : Nat) : MiriRunOutcome → Option Nat
  | .returned m' (.ok (.immediate (.scalar s))) =>
      if m'.stack.frames.isEmpty then
        match s.toScalarInt with
        | .ok sc =>
            if sc.size == Miri.ABI.Size.ofBytes (UInt64.ofNat sizeBytes) then
              some sc.data.toNat
            else none
        | .error _ => none
      else none
  | _ => none

def annealOutcomeU16Bool : AnnealRunOutcome → Option (Nat × Bool)
  | .returned (.aggregate 0 [.scalar ⟨bits, 2⟩, .scalar ⟨b, 1⟩]) _ =>
      if b == 0 then some (bits, false)
      else if b == 1 then some (bits, true)
      else none
  | _ => none

def miriOutcomeU16Bool : MiriRunOutcome → Option (Nat × Bool)
  | .returned m' (.ok (.immediate (.scalarPair s₁ s₂))) =>
      if m'.stack.frames.isEmpty then
        match s₁.toScalarInt, s₂.toScalarInt with
        | .ok sc₁, .ok sc₂ =>
            if sc₁.size == Miri.ABI.Size.ofBytes 2 && sc₂.size == Miri.ABI.Size.ofBytes 1 then
              if sc₂.data.toNat == 0 then some (sc₁.data.toNat, false)
              else if sc₂.data.toNat == 1 then some (sc₁.data.toNat, true)
              else none
            else none
        | _, _ => none
      else none
  | _ => none

/-- Signed `INT_MIN / -1` (`(-128_i8) / (-1_i8)`): across `bb0 -> goto bb1`,
both `runAnnealBounded` and `runMiriBounded` report undefined behavior at step 4. -/
theorem signedDiv_intMinNegOne_ub_agrees :
    annealOutcomeIsUB (runAnnealBounded (signedDivBody 255) 4 (annealSignedDivInit 255)) = true ∧
    miriOutcomeIsUB (runMiriBounded (signedDivBody 255) 4 (miriSignedDivInit 255)) = true := by
  decide

/-- Signed `(-128_i8) / 2_i8`: across `bb0 -> goto bb1 -> return`, both machines
return `192` (`-64_i8` in two's complement) at step 6. -/
theorem signedDiv_returns_agree :
    annealOutcomeScalarBits 1
        (runAnnealBounded (signedDivBody 2) 6 (annealSignedDivInit 2)) = some 192 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded (signedDivBody 2) 6 (miriSignedDivInit 2)) = some 192 := by
  decide

/-- Checked `65500_u16 + 100_u16`: both machines wrap to `64` and set `overflow = true`. -/
theorem addWithOverflow_overflows_agrees :
    annealOutcomeU16Bool
        (runAnnealBounded (addWithOverflowBody 100) 5 (annealAddOvfInit 100)) =
      some (64, true) ∧
    miriOutcomeU16Bool
        (runMiriBounded (addWithOverflowBody 100) 5 (miriAddOvfInit 100)) =
      some (64, true) := by
  decide

/-- Checked `65500_u16 + 10_u16`: both machines return `(65510, false)`. -/
theorem addWithOverflow_noOverflow_agrees :
    annealOutcomeU16Bool
        (runAnnealBounded (addWithOverflowBody 10) 5 (annealAddOvfInit 10)) =
      some (65510, false) ∧
    miriOutcomeU16Bool
        (runMiriBounded (addWithOverflowBody 10) 5 (miriAddOvfInit 10)) =
      some (65510, false) := by
  decide

end LeanMiriSpec.Correspondence.Witness
