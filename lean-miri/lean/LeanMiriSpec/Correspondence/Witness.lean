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

end LeanMiriSpec.Correspondence.Witness
