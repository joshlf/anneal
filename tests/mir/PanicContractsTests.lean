-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.
import Anneal.PanicContracts

namespace Anneal.PanicContractsTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.ITree
open Anneal.Pass
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.PanicContracts

/-! ## Fixture Constructors -/

def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
def unitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def u8CheckedTy : Ty := { kind := .tuple [.uint .u8, .bool], layoutIdx := 0 }
def u32CheckedTy : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }

def u8Const (n : Nat) : Operand :=
  .constant { ty := u8Ty, val := .scalar (.int { bits := n, sizeBytes := 1 }) }

def testLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def testFnAbi : FnAbi := {
  args := []
  ret := { layout := testLayout, mode := .direct }
  conv := .rust
  canUnwind := true
}

def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "PanicContractsTests.lean" }

def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "PanicContractsTests.lean" }

def mkBody (defPath : DefPath) (argCount : Nat) (localDecls : List LocalDecl)
    (basicBlocks : List BasicBlockData) : CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  role := .subject
  phase := .runtimePostCleanup
  fnAbi := testFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

def local_ (idx : Nat) : Place := { local_ := idx, projection := [] }

/-! ## 1. Checked Addition -/

/--
`fn checked_add(a: T, b: T) -> T { a + b }` under `-Coverflow-checks=yes`:
`bb0: _3 = AddWithOverflow(copy _1, copy _2); assert(!move (_3.1)) -> bb1`,
`bb1: _0 = move (_3.0); return`, with `unwind` on the assertion.
-/
def checkedAddBlocks (ty : Ty) (unwind : UnwindAction) : List BasicBlockData :=
  [ { statements :=
        [ mkStmt (.storageLive 3)
        , mkStmt (.assign (local_ 3)
            (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))) ]
      terminator :=
        mkTerm (.assert
          (.move { local_ := 3, projection := [.field 1 boolTy] }) false 1 unwind)
      isCleanup := false }
  , { statements :=
        [ mkStmt (.assign (local_ 0)
            (.use (.move { local_ := 3, projection := [.field 0 ty] }))) ]
      terminator := mkTerm .return_
      isCleanup := false } ]

/-- `checkedAddBlocks` as a body, followed by `cleanupBlocks`. -/
def checkedAddMir (defPath : DefPath) (ty checkedTy : Ty) (unwind : UnwindAction)
    (cleanupBlocks : List BasicBlockData := []) : CapturedMir :=
  mkBody defPath 2
    [ mkDecl .mut ty, mkDecl .not ty, mkDecl .not ty, mkDecl .mut checkedTy ]
    (checkedAddBlocks ty unwind ++ cleanupBlocks)

def checkedAddU8Mir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_u8" u8Ty u8CheckedTy .continue_

/-- Two scalar arguments of byte width `w`. -/
def scalarArgs2 (w a b : Nat) : List Value :=
  [.scalar { bits := a, sizeBytes := w }, .scalar { bits := b, sizeBytes := w }]

def checkedAddU32Mir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_u32" u32Ty u32CheckedTy .continue_

theorem checkedAddU8_wp (a b : Nat) :
    wpMirSym 8 checkedAddU8Mir
      (initMachineStateWithCallees checkedAddU8Mir (scalarArgs2 1 a b) [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 })
        (256 ≤ a + b)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact (nat_ble_eq_true_iff _ _).1 heq
  · rename_i heq
    have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
    exact ⟨Nat.not_le.2 hlt,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_of_lt hlt)⟩

theorem checkedAddU32_wp (a b : Nat) :
    wpMirSym 8 checkedAddU32Mir
      (initMachineStateWithCallees checkedAddU32Mir (scalarArgs2 4 a b) [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 4 })
        (4294967296 ≤ a + b)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact (nat_ble_eq_true_iff _ _).1 heq
  · rename_i heq
    have hlt : a + b < 4294967296 := (nat_ble_eq_false_iff _ _).1 heq
    exact ⟨Nat.not_le.2 hlt,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 4 }) (wrapScalarBits_of_lt hlt)⟩

/-- `fn div(a: u8, b: u8) -> u8 { a / b }`:
`bb0: _3 = Eq(copy _2, const 0_u8); assert(!move _3) -> bb1`,
`bb1: _0 = Div(copy _1, copy _2); return`. -/
def checkedDivU8Mir : CapturedMir :=
  mkBody "panic_tests::checked_div_u8" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut boolTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign (local_ 3)
              (.binaryOp .eq (.copy (local_ 2)) (u8Const 0))) ]
        terminator := mkTerm (.assert (.move (local_ 3)) false 1 .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.binaryOp .div (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem checkedDivU8_wp (a b : Nat) (ha : a < 256) :
    wpMirSym 8 checkedDivU8Mir
      (initMachineStateWithCallees checkedDivU8Mir (scalarArgs2 1 a b) [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a / b, sizeBytes := 1 })
        (b = 0)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact (nat_beq_eq_true_iff _ _).1 heq
  · rename_i _ heq₁ _ heq₂
    exact Bool.noConfusion (heq₁.symm.trans heq₂)
  · rename_i _ heq _ _
    have hne : b ≠ 0 := (nat_beq_eq_false_iff _ _).1 heq
    have hlt : a / b < 256 := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
    exact ⟨hne,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_of_lt hlt)⟩

def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def u8Array4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 0 }

def usizeConst (n : Nat) : Operand :=
  .constant { ty := usizeTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

/-- `fn get(arr: [u8; 4], i: usize) -> u8 { arr[i] }`:
`bb0: _3 = Lt(copy _2, const 4_usize); assert(move _3) -> bb1`,
`bb1: _0 = copy _1[_2]; return`. -/
def checkedIndexMir : CapturedMir :=
  mkBody "panic_tests::checked_index" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Array4Ty, mkDecl .not usizeTy, mkDecl .mut boolTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign (local_ 3)
              (.binaryOp .lt (.copy (local_ 2)) (usizeConst 4))) ]
        terminator := mkTerm (.assert (.move (local_ 3)) true 1 .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.copy { local_ := 1, projection := [.index 2] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Arguments of `checkedIndexMir`: a four-element `u8` array and a `usize` index. -/
def indexArgs (e₀ e₁ e₂ e₃ i : Nat) : List Value :=
  [ .aggregate 0
      [ .scalar { bits := e₀, sizeBytes := 1 }, .scalar { bits := e₁, sizeBytes := 1 }
      , .scalar { bits := e₂, sizeBytes := 1 }, .scalar { bits := e₃, sizeBytes := 1 } ]
  , .scalar { bits := i, sizeBytes := 8 } ]

/-- The array element selected by the index argument of `checkedIndexMir`. -/
def indexedElem : List Value → Value
  | [.aggregate _ elems, .scalar i] => elems.getD i.bits .uninit
  | _ => .uninit

/-- Bits of the `n`-th argument when it is a scalar. -/
def argBits (args : List Value) (n : Nat) : Nat :=
  match args[n]? with
  | some (.scalar sc) => sc.bits
  | _ => 0

theorem checkedIndex_wp (e₀ e₁ e₂ e₃ i : Nat) :
    wpMirSym 8 checkedIndexMir
      (initMachineStateWithCallees checkedIndexMir (indexArgs e₀ e₁ e₂ e₃ i) [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = indexedElem (indexArgs e₀ e₁ e₂ e₃ i))
        (4 ≤ argBits (indexArgs e₀ e₁ e₂ e₃ i) 1)) := by
  match i with
  | 0 | 1 | 2 | 3 =>
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    all_goals exact ⟨Nat.not_le.2 (Nat.le_of_ble_eq_true rfl), rfl⟩
  | i + 4 =>
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    exact Nat.le_add_left 4 i

/-! ### Contracts -/

/-- Two well-typed scalar arguments of byte width `w`. -/
def scalarPre2 (w : Nat) (args : List Value) : Prop :=
  ∃ a b, a < scalarModulus w ∧ b < scalarModulus w ∧ args = scalarArgs2 w a b

/-- Mathematical sum of the two scalar arguments. -/
def argSum (args : List Value) : Nat := argBits args 0 + argBits args 1

/-- The return value is the unwrapped sum at byte width `w`. -/
def sumPost (w : Nat) (args : List Value) (r : MirReturn) : Prop :=
  r.1 = .scalar { bits := argSum args, sizeBytes := w }

/-- The sum does not fit in `w` bytes. -/
def overflows (w : Nat) (args : List Value) : Prop := scalarModulus w ≤ argSum args

/--
Checked `u8` addition satisfies the total exact panic contract on all
`2^8 × 2^8` inputs: it panics exactly when `a + b ≥ 2^8`, and otherwise returns
`a + b`.
-/
theorem checkedAddU8_totalExact :
    TotalExactPanicContract (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1)
      (overflows 1) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    exact checkedAddU8_wp a b)

theorem checkedAddU8_exact :
    ExactPanicContract (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1) (overflows 1) :=
  checkedAddU8_totalExact.exact

/--
Checked `u32` addition satisfies the total exact panic contract on all
`2^32 × 2^32` inputs.
-/
theorem checkedAddU32_totalExact :
    TotalExactPanicContract (mirTrees checkedAddU32Mir) (scalarPre2 4) (sumPost 4)
      (overflows 4) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    exact checkedAddU32_wp a b)

theorem checkedAddU32_exact :
    ExactPanicContract (mirTrees checkedAddU32Mir) (scalarPre2 4) (sumPost 4) (overflows 4) :=
  checkedAddU32_totalExact.exact

/--
Dichotomy of checked `u8` addition, stated on the trusted tree: every input is
fault-free on every branch, an input panics exactly when `a + b ≥ 256`, and an
input returns exactly when `a + b < 256`, with value `a + b`.
-/
theorem checkedAddU8_dichotomy (a b : Nat) (ha : a < 256) (hb : b < 256) :
    NoFault (mirCallTree checkedAddU8Mir (scalarArgs2 1 a b)) ∧
      (256 ≤ a + b ↔
        ∃ tr, ReachesRet (mirCallTree checkedAddU8Mir (scalarArgs2 1 a b)) tr .panic) ∧
      (¬ 256 ≤ a + b ↔
        ∃ tr r, ReachesRet (mirCallTree checkedAddU8Mir (scalarArgs2 1 a b)) tr (.normal r) ∧
          r.1 = .scalar { bits := a + b, sizeBytes := 1 }) ∧
      ∀ tr, ¬ ReachesRet (mirCallTree checkedAddU8Mir (scalarArgs2 1 a b)) tr .abort :=
  have hPre : scalarPre2 1 (scalarArgs2 1 a b) := ⟨a, b, ha, hb, rfl⟩
  ⟨checkedAddU8_exact.1.noFault hPre, checkedAddU8_totalExact.panics_iff hPre,
    checkedAddU8_totalExact.returns_iff hPre,
    fun _ => checkedAddU8_exact.1.not_reaches_abort hPre⟩

/-- Division by zero guard: `a / b` panics exactly when `b = 0`. -/
theorem checkedDivU8_totalExact :
    TotalExactPanicContract (mirTrees checkedDivU8Mir) (scalarPre2 1)
      (fun args r => r.1 = .scalar { bits := argBits args 0 / argBits args 1, sizeBytes := 1 })
      (fun args => argBits args 1 = 0) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, ha, -, rfl⟩
    exact checkedDivU8_wp a b ha)

theorem checkedDivU8_exact :
    ExactPanicContract (mirTrees checkedDivU8Mir) (scalarPre2 1)
      (fun args r => r.1 = .scalar { bits := argBits args 0 / argBits args 1, sizeBytes := 1 })
      (fun args => argBits args 1 = 0) :=
  checkedDivU8_totalExact.exact

/-- Well-typed arguments of `checkedIndexMir`. -/
def indexPre (args : List Value) : Prop :=
  ∃ e₀ e₁ e₂ e₃ i, args = indexArgs e₀ e₁ e₂ e₃ i

/-- Bounds-checked indexing: `arr[i]` panics exactly when `i ≥ 4`. -/
theorem checkedIndex_totalExact :
    TotalExactPanicContract (mirTrees checkedIndexMir) indexPre
      (fun args r => r.1 = indexedElem args) (fun args => 4 ≤ argBits args 1) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨e₀, e₁, e₂, e₃, i, rfl⟩
    exact checkedIndex_wp e₀ e₁ e₂ e₃ i)

theorem checkedIndex_exact :
    ExactPanicContract (mirTrees checkedIndexMir) indexPre
      (fun args r => r.1 = indexedElem args) (fun args => 4 ≤ argBits args 1) :=
  checkedIndex_totalExact.exact

/-! ### Interoperation with `Trusted.VerificationResult` -/

/-- Partial-correctness claim of checked `u8` addition: a normal return is the sum. -/
def checkedAddU8Claim : Claim where
  body := checkedAddU8Mir
  pre := scalarPre2 1
  post args ret := ret = .scalar { bits := argSum args, sizeBytes := 1 }

/-- The panic contract yields the existing partial-correctness certificate. -/
theorem checkedAddU8_verificationResult : VerificationResult checkedAddU8Claim :=
  PanicsOnlyIf.toVerificationResult checkedAddU8Claim checkedAddU8_exact.1

/-- On inputs whose sum fits, checked `u8` addition never panics. -/
theorem checkedAddU8_neverPanics_inRange :
    NeverPanics (mirTrees checkedAddU8Mir)
      (fun args => scalarPre2 1 args ∧ ¬ overflows 1 args) (sumPost 1) :=
  (panicsOnlyIf_iff_neverPanics_of_not_panicCond (fun _ h => h.2)).1
    (checkedAddU8_exact.1.mono (fun _ h => h.1) (fun _ _ _ hv => hv) (fun _ _ hp => hp))

/--
`NeverPanics` is strictly stronger than the partial-correctness certificate: the
certificate holds on all inputs, while `NeverPanics` fails on an overflowing one.
-/
theorem checkedAddU8_not_neverPanics :
    ¬ NeverPanics (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1) := by
  intro h
  have hPre : scalarPre2 1 (scalarArgs2 1 255 1) := ⟨255, 1, by decide, by decide, rfl⟩
  obtain ⟨tr, hr⟩ := checkedAddU8_exact.2 _ hPre (by decide : (256 : Nat) ≤ 255 + 1)
  exact h.not_reaches_panic hPre hr

/-! ## 2. Caller–Callee Composition -/

def checkedAddU8Path : DefPath := "panic_tests::checked_add_u8"

/-- Constant function-item operand naming `defPath`. -/
def fnItemOp (defPath : DefPath) (typeArgs : List RigidTy := []) : Operand :=
  .constant { ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }, val := .zeroSized }

/--
`fn add_caller(a: u8, b: u8) -> u8 { checked_add_u8(a, b) }`:
`bb0: _0 = checked_add_u8(copy _1, copy _2) -> [return: bb1, unwind]`,
`bb1: return`, and the cleanup block `bb2: resume`.
-/
def addCallerMir (unwind : UnwindAction) : CapturedMir :=
  mkBody "panic_tests::add_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) unwind)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false }
    , { statements := [], terminator := mkTerm .unwindResume, isCleanup := true } ]

/--
Panic call contract of `checked_add_u8` at a call site with the empty memory:
it returns the sum when the sum fits, unwinds only on overflow, and hands back
the request memory in both cases.
-/
def checkedAddU8Contract : PanicMirCallContract where
  pre req :=
    req.defPath = checkedAddU8Path ∧ scalarPre2 1 req.args ∧ req.memory = emptyMemory
  post req retVal memAfter :=
    retVal = .scalar { bits := argSum req.args, sizeBytes := 1 } ∧
      ¬ overflows 1 req.args ∧ memAfter = req.memory
  panicCond req := overflows 1 req.args
  panicMemInv req memAfter := memAfter = req.memory

/-- The contract the caller is verified against: `checkedAddU8Contract` with trait preservation. -/
def checkedAddU8MirContract : MirCallContract :=
  checkedAddU8Contract.withTraitsPreserved.toMirCallContract

/-- Inputs of the composition tests: two well-typed `u8` arguments and the empty memory. -/
def addCallerPre (x : MirInput) : Prop := scalarPre2 1 x.1 ∧ x.2 = emptyMemory

/--
Call-free evaluation of the callee on a request satisfying the contract: the
answer `linkCalleeHandler` presents satisfies the contract's postcondition.
-/
theorem checkedAddU8_callee_wp (typeArgs : List RigidTy) (a b : Nat) :
    wpMirNoCallSym 8 checkedAddU8Mir
      (initMachineStateWithMemory checkedAddU8Mir (scalarArgs2 1 a b) emptyMemory)
      (fun out =>
        checkedAddU8MirContract.post
          { defPath := checkedAddU8Path, typeArgs := typeArgs, args := scalarArgs2 1 a b,
            memory := emptyMemory }
          (outcomeToCallAns emptyMemory out)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact ⟨(nat_ble_eq_true_iff _ _).1 heq, rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
  · rename_i heq
    have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
    exact ⟨⟨congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
        (wrapScalarBits_of_lt hlt), Nat.not_le.2 hlt, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩

/--
The callee implements its contract totally: from every request satisfying the
contract's `pre`, the call-free callee tree terminates within the contract.
-/
theorem checkedAddU8_holdsTotallyOn (fallback : ExternalCallHandler) :
    checkedAddU8MirContract.holdsTotallyOn (linkCalleeHandler checkedAddU8Mir fallback) :=
  holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallSym checkedAddU8MirContract
    checkedAddU8Mir fallback 8 (fun _ h => h.1) (by
      rintro ⟨_, typeArgs, _, _⟩ ⟨rfl, ⟨a, b, -, -, rfl⟩, rfl⟩
      exact checkedAddU8_callee_wp typeArgs a b)

/-- The callee implements its contract. -/
theorem checkedAddU8_holdsOn (fallback : ExternalCallHandler) :
    checkedAddU8MirContract.holdsOn (linkCalleeHandler checkedAddU8Mir fallback) :=
  holdsOn_of_holdsTotallyOn (checkedAddU8_holdsTotallyOn fallback)

/--
Modular evaluation of the caller under `UnwindAction.continue_` and under
`UnwindAction.cleanup` into a `resume` block: the callee's panic becomes the
caller's panic.
-/
theorem addCaller_unwinding_wp (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2) (a b : Nat)
    (ha : a < 256) (hb : b < 256) :
    wpMirModularSym checkedAddU8MirContract 8 (addCallerMir unwind)
      (initMachineStateWithMemoryAndCallees (addCallerMir unwind) (scalarArgs2 1 a b)
        emptyMemory [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 })
        (256 ≤ a + b)) := by
  rcases hUnwind with rfl | rfl <;>
  · (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩, rfl⟩, fun ans hPost => ?_⟩
    cases ans with
    | returned retVal memAfter =>
      obtain ⟨⟨hVal, hFit, hMem⟩, _⟩ := hPost
      subst hVal hMem
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      exact ⟨hFit, rfl⟩
    | panicked memAfter =>
      obtain ⟨hOver, hMem, _⟩ := hPost
      subst hMem
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      exact hOver
    | aborted => exact False.elim hPost

/-- Postcondition of the composition tests: the caller returns the sum. -/
def addCallerPost (x : MirInput) (r : MirReturn) : Prop := sumPost 1 x.1 r

/-- Panic condition of the composition tests: the sum overflows `u8`. -/
def addCallerOverflows (x : MirInput) : Prop := overflows 1 x.1

/--
The caller alone, against every handler implementing the callee contract, panics
only on overflow.
-/
theorem addCaller_modular_panicsOnlyIf (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2) :
    MirModularPanicsOnlyIf (addCallerMir unwind) checkedAddU8MirContract.holdsOn
      addCallerPre addCallerPost addCallerOverflows :=
  mirModularPanicsOnlyIf_of_dwlp checkedAddU8MirContract (by
    rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact DWLP.mono (fun _ _ h => h.toPanicOutcomeOk)
      (dwp_of_wpMirModularSym (addCaller_unwinding_wp unwind hUnwind a b ha hb)).toDWLP)

/-- The callee's closed trees satisfy the only-if contract `panicsOnlyIf_call_compose` asks for. -/
theorem checkedAddU8_closedCallee_panicsOnlyIf :
    PanicsOnlyIf (mirClosedCalleeTrees checkedAddU8Mir)
      (fun req =>
        checkedAddU8Contract.withTraitsPreserved.pre req ∧
          req.defPath = checkedAddU8Mir.defPath)
      (fun req r => checkedAddU8Contract.withTraitsPreserved.post req r.1 r.2)
      (fun req =>
        checkedAddU8Contract.withTraitsPreserved.panicCond req ∧
          checkedAddU8Contract.withTraitsPreserved.panicMemInv req req.memory) :=
  panicsWithPolicyOnlyIf_forbidAbort_iff.1
    (mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp (by
      rintro ⟨_, typeArgs, _, _⟩ ⟨⟨rfl, ⟨a, b, -, -, rfl⟩, rfl⟩, -⟩
      exact DWLP.mono
        (fun out _ h =>
          (checkedAddU8Contract.withTraitsPreserved.toPolicy_post_outcomeToCallAns_iff
            .forbidAbort _ out).1 h)
        (dwp_of_wpMirNoCallSym (checkedAddU8_callee_wp typeArgs a b)).toDWLP))

/--
Horizontal composition through `panicsOnlyIf_call_compose`: the caller linked
with the callee is fault-free on every input, never aborts, and panics only on
overflow.
-/
theorem addCaller_linked_panicsOnlyIf (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2)
    (fallback : ExternalCallHandler) :
    PanicsOnlyIf
      (mirHandledTrees (addCallerMir unwind) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre addCallerPost addCallerOverflows :=
  panicsOnlyIf_call_compose checkedAddU8Contract.withTraitsPreserved
    (addCaller_modular_panicsOnlyIf unwind hUnwind)
    checkedAddU8_closedCallee_panicsOnlyIf
    (fun _ hPre hNe => False.elim (hNe hPre.1))

/--
Exact horizontal composition: the linked system panics exactly on overflow and
returns the sum otherwise, for `UnwindAction.continue_` and for
`UnwindAction.cleanup` into a `resume` block.
-/
theorem addCaller_linked_totalExact (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2)
    (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees (addCallerMir unwind) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre addCallerPost addCallerOverflows :=
  totalExactPolicyPanicContract_forbidAbort_iff.1
    (mirHandled_totalExactPolicyPanicContract_of_dwp checkedAddU8MirContract
      (checkedAddU8_holdsTotallyOn fallback) (by
        rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
        exact DWP.mono
          (fun out _ h => (exactPolicyOutcome_forbidAbort_iff _ _ _ out).2 h)
          (dwp_of_wpMirModularSym (addCaller_unwinding_wp unwind hUnwind a b ha hb))))

/--
Modular evaluation of the caller under `UnwindAction.terminate` (`-C panic=abort`
at the call site): the callee's panic becomes the caller's abort.
-/
theorem addCaller_terminate_wp (a b : Nat) (ha : a < 256) (hb : b < 256) :
    wpMirModularSym checkedAddU8MirContract 8 (addCallerMir .terminate)
      (initMachineStateWithMemoryAndCallees (addCallerMir .terminate) (scalarArgs2 1 a b)
        emptyMemory [])
      (ExactPolicyOutcome (.abortOnlyIf addCallerOverflows)
        ((scalarArgs2 1 a b, emptyMemory) : MirInput)
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 })
        False) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩, rfl⟩, fun ans hPost => ?_⟩
  cases ans with
  | returned retVal memAfter =>
    obtain ⟨⟨hVal, hFit, hMem⟩, _⟩ := hPost
    subst hVal hMem
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    exact ⟨fun h => h, hFit, rfl⟩
  | panicked memAfter =>
    obtain ⟨hOver, hMem, _⟩ := hPost
    subst hMem
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    exact ⟨hOver, fun h => h⟩
  | aborted => exact False.elim hPost

/--
Exact composition under `UnwindAction.terminate`: the linked system never
panics, aborts exactly on overflow, and returns the sum otherwise.
-/
theorem addCaller_terminate_linked_totalExact (fallback : ExternalCallHandler) :
    TotalExactPolicyPanicContract
      (mirHandledTrees (addCallerMir .terminate) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre addCallerPost (fun _ => False) (.abortOnlyIf addCallerOverflows) :=
  mirHandled_totalExactPolicyPanicContract_of_dwp checkedAddU8MirContract
    (checkedAddU8_holdsTotallyOn fallback) (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact dwp_of_wpMirModularSym (addCaller_terminate_wp a b ha hb))

/-- The linked system under `UnwindAction.terminate` satisfies `ExactPanicAbortContract`. -/
theorem addCaller_terminate_linked_exactPanicAbort (fallback : ExternalCallHandler) :
    ExactPanicAbortContract
      (mirHandledTrees (addCallerMir .terminate) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre addCallerPost (fun _ => False) addCallerOverflows :=
  exactPolicyPanicContract_abortOnlyIf_iff.1
    (addCaller_terminate_linked_totalExact fallback).exact

/-! ## 3. `-C panic=abort` Fixtures -/

/-- Checked `u8` addition whose overflow assertion has `UnwindAction.terminate`. -/
def checkedAddTerminateMir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_terminate" u8Ty u8CheckedTy .terminate

/--
Checked `u8` addition whose overflow assertion unwinds into a cleanup block that
ends in `TerminatorKind.unwindTerminate`.
-/
def checkedAddUnwindTerminateMir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_unwind_terminate" u8Ty u8CheckedTy (.cleanup 2)
    [ { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := true } ]

def neverTy : Ty := { kind := .never, layoutIdx := 0 }

/--
`fn nonzero(x: u8) -> u8 { if x == 0 { panic_nounwind() } x }`:
`bb0: switchInt(copy _1) -> [0: bb1, otherwise: bb2]`,
`bb1: _2 = core::panicking::panic_nounwind() -> unwind unreachable`,
`bb2: _0 = copy _1; return`.
-/
def nounwindGuardMir : CapturedMir :=
  mkBody "panic_tests::nounwind_guard" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut neverTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1)], otherwise := 2 })
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic_nounwind") [] (local_ 2) .none
            .unreachable)
        isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem checkedAddTerminate_wp (a b : Nat) :
    wpMirSym 8 checkedAddTerminateMir
      (initMachineStateWithCallees checkedAddTerminateMir (scalarArgs2 1 a b) [])
      (ExactPolicyOutcome (.abortOnlyIf (overflows 1)) (scalarArgs2 1 a b)
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 }) False) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact ⟨(nat_ble_eq_true_iff _ _).1 heq, fun h => h⟩
  · rename_i heq
    have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
    exact ⟨fun h => h, Nat.not_le.2 hlt,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_of_lt hlt)⟩

theorem checkedAddUnwindTerminate_wp (a b : Nat) :
    wpMirSym 8 checkedAddUnwindTerminateMir
      (initMachineStateWithCallees checkedAddUnwindTerminateMir (scalarArgs2 1 a b) [])
      (ExactPolicyOutcome (.abortOnlyIf (overflows 1)) (scalarArgs2 1 a b)
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 }) False) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact ⟨(nat_ble_eq_true_iff _ _).1 heq, fun h => h⟩
  · rename_i heq
    have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
    exact ⟨fun h => h, Nat.not_le.2 hlt,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_of_lt hlt)⟩

/-- One well-typed `u8` argument. -/
def scalarPre1 (args : List Value) : Prop :=
  ∃ x, x < 256 ∧ args = [.scalar { bits := x, sizeBytes := 1 }]

theorem nounwindGuard_wp (x : Nat) :
    wpMirSym 8 nounwindGuardMir
      (initMachineStateWithCallees nounwindGuardMir [.scalar { bits := x, sizeBytes := 1 }] [])
      (ExactPolicyOutcome (.abortOnlyIf (fun args : List Value => argBits args 0 = 0))
        [.scalar { bits := x, sizeBytes := 1 }]
        (fun r : MirReturn => r.1 = .scalar { bits := x, sizeBytes := 1 }) False) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact ⟨(nat_beq_eq_true_iff _ _).1 heq, fun h => h⟩
  · rename_i heq
    exact ⟨fun h => h, (nat_beq_eq_false_iff _ _).1 heq, rfl⟩

/--
`UnwindAction.terminate` on the overflow assertion: the function never panics,
aborts exactly on overflow, and returns the sum otherwise.
-/
theorem checkedAddTerminate_totalExact :
    TotalExactPolicyPanicContract (mirTrees checkedAddTerminateMir) (scalarPre2 1)
      (sumPost 1) (fun _ => False) (.abortOnlyIf (overflows 1)) :=
  totalExactPolicyPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    exact checkedAddTerminate_wp a b)

theorem checkedAddTerminate_exactPanicAbort :
    ExactPanicAbortContract (mirTrees checkedAddTerminateMir) (scalarPre2 1) (sumPost 1)
      (fun _ => False) (overflows 1) :=
  exactPolicyPanicContract_abortOnlyIf_iff.1 checkedAddTerminate_totalExact.exact

/--
Unwinding into a cleanup block that ends in `unwindTerminate`: the function
never panics, aborts exactly on overflow, and returns the sum otherwise.
-/
theorem checkedAddUnwindTerminate_totalExact :
    TotalExactPolicyPanicContract (mirTrees checkedAddUnwindTerminateMir) (scalarPre2 1)
      (sumPost 1) (fun _ => False) (.abortOnlyIf (overflows 1)) :=
  totalExactPolicyPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    exact checkedAddUnwindTerminate_wp a b)

theorem checkedAddUnwindTerminate_exactPanicAbort :
    ExactPanicAbortContract (mirTrees checkedAddUnwindTerminateMir) (scalarPre2 1)
      (sumPost 1) (fun _ => False) (overflows 1) :=
  exactPolicyPanicContract_abortOnlyIf_iff.1 checkedAddUnwindTerminate_totalExact.exact

/--
A direct diverging call to `core::panicking::panic_nounwind`: the function never
panics, aborts exactly when `x = 0`, and returns `x` otherwise.
-/
theorem nounwindGuard_totalExact :
    TotalExactPolicyPanicContract (mirTrees nounwindGuardMir) scalarPre1
      (fun args r => r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 })
      (fun _ => False) (.abortOnlyIf (fun args => argBits args 0 = 0)) :=
  totalExactPolicyPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨x, -, rfl⟩
    exact nounwindGuard_wp x)

theorem nounwindGuard_exactPanicAbort :
    ExactPanicAbortContract (mirTrees nounwindGuardMir) scalarPre1
      (fun args r => r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 })
      (fun _ => False) (fun args => argBits args 0 = 0) :=
  exactPolicyPanicContract_abortOnlyIf_iff.1 nounwindGuard_totalExact.exact

/-- Under `UnwindAction.terminate` no input of checked addition panics. -/
theorem checkedAddTerminate_never_panics (a b : Nat) (ha : a < 256) (hb : b < 256)
    (tr : List (Event MirEffect)) :
    ¬ ReachesRet (mirCallTree checkedAddTerminateMir (scalarArgs2 1 a b)) tr .panic :=
  fun hr =>
    checkedAddTerminate_totalExact.exact.1.panicCond_of_panics
      (x := scalarArgs2 1 a b) ⟨a, b, ha, hb, rfl⟩ hr

/-! ## 4. Refutations -/

/-! ### Undefined behavior on the panic path -/

/-- Checked `u8` addition whose overflow assertion has `UnwindAction.unreachable`. -/
def checkedAddUnreachableMir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_unreachable" u8Ty u8CheckedTy .unreachable

/--
Checked `u8` addition whose overflow assertion unwinds into a cleanup block that
executes `TerminatorKind.unreachable`.
-/
def checkedAddUbCleanupMir : CapturedMir :=
  checkedAddMir "panic_tests::checked_add_ub_cleanup" u8Ty u8CheckedTy (.cleanup 2)
    [ { statements := [], terminator := mkTerm .unreachable, isCleanup := true } ]

theorem overflowingArgs_pre : scalarPre2 1 (scalarArgs2 1 255 1) :=
  ⟨255, 1, by decide, by decide, rfl⟩

/--
`UnwindAction.unreachable` on a failing assertion is undefined behavior, so the
function satisfies no panic contract at all on a precondition that admits an
overflowing input: not with `panicCond := True`, and not under the unconditional
abort waiver.
-/
theorem checkedAddUnreachable_not_panicsWithPolicyOnlyIf
    (post : List Value → MirReturn → Prop) (panicCond : List Value → Prop)
    (policy : AbortPolicy (List Value)) :
    ¬ PanicsWithPolicyOnlyIf (mirTrees checkedAddUnreachableMir) (scalarPre2 1) post
      panicCond policy :=
  fun h =>
    reachesFaultBounded_not_treeSafe 8 checkedAddUnreachableMir
      (initMachineStateWithCallees checkedAddUnreachableMir (scalarArgs2 1 255 1) []) rfl
      (h _ overflowingArgs_pre).1

theorem checkedAddUnreachable_not_panicsOnlyIf_true :
    ¬ PanicsOnlyIf (mirTrees checkedAddUnreachableMir) (scalarPre2 1) (sumPost 1)
      (fun _ => True) :=
  fun h =>
    checkedAddUnreachable_not_panicsWithPolicyOnlyIf _ _ .forbidAbort
      (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h)

/--
A cleanup block that reaches `unreachable` is undefined behavior on the panic
path, so the function satisfies no panic contract on a precondition that admits
an overflowing input.
-/
theorem checkedAddUbCleanup_not_panicsWithPolicyOnlyIf
    (post : List Value → MirReturn → Prop) (panicCond : List Value → Prop)
    (policy : AbortPolicy (List Value)) :
    ¬ PanicsWithPolicyOnlyIf (mirTrees checkedAddUbCleanupMir) (scalarPre2 1) post
      panicCond policy :=
  fun h =>
    reachesFaultBounded_not_treeSafe 8 checkedAddUbCleanupMir
      (initMachineStateWithCallees checkedAddUbCleanupMir (scalarArgs2 1 255 1) []) rfl
      (h _ overflowingArgs_pre).1

theorem checkedAddUbCleanup_not_panicsOnlyIf_true :
    ¬ PanicsOnlyIf (mirTrees checkedAddUbCleanupMir) (scalarPre2 1) (sumPost 1)
      (fun _ => True) :=
  fun h =>
    checkedAddUbCleanup_not_panicsWithPolicyOnlyIf _ _ .forbidAbort
      (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h)

/--
The same bodies are fault-free on the non-overflowing inputs: excluding the
panicking inputs from the precondition hides the undefined behavior, which is
what a panic contract over all inputs prevents.
-/
theorem checkedAddUnreachable_neverPanics_inRange :
    NeverPanics (mirTrees checkedAddUnreachableMir)
      (fun args => scalarPre2 1 args ∧ ¬ overflows 1 args) (sumPost 1) :=
  neverPanics_of_wpMirSym 8 (by
    rintro _ ⟨⟨a, b, -, -, rfl⟩, hFit⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq
      exact hFit ((nat_ble_eq_true_iff _ _).1 heq)
    · rename_i heq
      have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
      exact ⟨_, rfl,
        congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_of_lt hlt)⟩)

/-! ### Over-approximated panic condition -/

/-- With `panicCond := True` the only-if contract of checked addition still holds. -/
theorem checkedAddU8_panicsOnlyIf_true :
    PanicsOnlyIf (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1) (fun _ => True) :=
  checkedAddU8_exact.1.mono (fun _ h => h) (fun _ _ _ hv => hv) (fun _ _ _ => trivial)

theorem zeroArgs_pre : scalarPre2 1 (scalarArgs2 1 0 0) :=
  ⟨0, 0, by decide, by decide, rfl⟩

/--
The trigger rejects the over-approximation: checked addition returns normally on
`(0, 0)`, so `panicCond := True` is not a panic trigger.
-/
theorem checkedAddU8_not_panicsIf_true :
    ¬ PanicsIf (mirTrees checkedAddU8Mir) (scalarPre2 1) (fun _ => True) := by
  intro h
  obtain ⟨tr, hr⟩ := h _ zeroArgs_pre trivial
  have hOver : overflows 1 (scalarArgs2 1 0 0) :=
    checkedAddU8_exact.1.panicCond_of_panics zeroArgs_pre hr
  exact absurd hOver (show ¬ ((256 : Nat) ≤ 0) by decide)

theorem checkedAddU8_not_exact_true :
    ¬ ExactPanicContract (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1)
      (fun _ => True) :=
  fun h => checkedAddU8_not_panicsIf_true h.2

/-! ### Dropped panic guard -/

/--
Mutant of checked `u8` addition without the overflow assertion:
`bb0: _0 = Add(copy _1, copy _2); return`.
-/
def wrappingAddU8Mir : CapturedMir :=
  mkBody "panic_tests::wrapping_add_u8" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements :=
          [ mkStmt (.assign (local_ 0)
              (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- The mutant returns the wrapped sum on every input and never panics. -/
theorem wrappingAddU8_neverPanics :
    NeverPanics (mirTrees wrappingAddU8Mir) (scalarPre2 1)
      (fun args r => r.1 = .scalar { bits := argSum args % 256, sizeBytes := 1 }) :=
  neverPanics_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    exact ⟨_, rfl,
      congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 }) (wrapScalarBits_eq_mod _ _)⟩)

/--
The trigger kills the mutant: without the assertion the overflowing input
`(255, 1)` returns, so the overflow condition is no longer a panic trigger.
-/
theorem wrappingAddU8_not_panicsIf :
    ¬ PanicsIf (mirTrees wrappingAddU8Mir) (scalarPre2 1) (overflows 1) :=
  not_panicsIf_of_neverPanics overflowingArgs_pre
    (show (256 : Nat) ≤ 255 + 1 by decide) wrappingAddU8_neverPanics

theorem wrappingAddU8_not_exact :
    ¬ ExactPanicContract (mirTrees wrappingAddU8Mir) (scalarPre2 1) (sumPost 1)
      (overflows 1) :=
  fun h => wrappingAddU8_not_panicsIf h.2

/--
The only-if contract alone does not kill the mutant's missing panic: with a
postcondition that admits the wrapped sum, the mutant satisfies `PanicsOnlyIf`
for the original panic condition.
-/
theorem wrappingAddU8_panicsOnlyIf :
    PanicsOnlyIf (mirTrees wrappingAddU8Mir) (scalarPre2 1)
      (fun args r => r.1 = .scalar { bits := argSum args % 256, sizeBytes := 1 })
      (overflows 1) :=
  wrappingAddU8_neverPanics.toPanicsOnlyIf (overflows 1)

/-! ### Reactive self-loops -/

/-- A tree that emits the observation `0` forever. -/
def reactiveLoopTree : ITree MirEffect MirOutcome :=
  ITree.cofix
    (fun _ : PUnit => .vis (.inr (.inl (.emit (.event 0)))) (fun _ => PUnit.unit))
    PUnit.unit

/--
The reactive loop is productive and never diverges silently, yet it has no
completed execution and refutes every panic trigger.
-/
theorem reactiveLoopTree_trap :
    Productive reactiveLoopTree ∧ ¬ MayDiverge reactiveLoopTree ∧
      ¬ PanicsIf (fun _ : Unit => reactiveLoopTree) (fun _ => True) (fun _ => True) :=
  not_panicsIf_of_selfLoop (tree := fun _ : Unit => reactiveLoopTree) (x := ())
    rfl rfl trivial trivial

/--
`loop { observe(0) }` in MIR: `bb0: switchInt(const 0_u8) -> [otherwise: bb0]`.
Each iteration emits the branch observation and returns to the same state.
-/
def reactiveSwitchLoopMir : CapturedMir :=
  mkBody "panic_tests::reactive_switch_loop" 0
    [ mkDecl .mut unitTy ]
    [ { statements := []
        terminator := mkTerm (.switchInt (u8Const 0) { branches := [], otherwise := 0 })
        isCleanup := false } ]

/-- One step of the MIR loop is a visible observation that returns to the initial state. -/
theorem reactiveSwitchLoopMir_step :
    stepMirState reactiveSwitchLoopMir
        (.running (initMachineStateWithCallees reactiveSwitchLoopMir [] [])) =
      .vis (.inr (.inl (.emit (.event 0))))
        (fun _ => .running (initMachineStateWithCallees reactiveSwitchLoopMir [] [])) :=
  rfl

/--
The MIR reactive loop is fault-free, productive, and never diverges silently,
yet it never panics: `Productive ∧ ¬ MayDiverge` is not a panic trigger.
-/
theorem reactiveSwitchLoopMir_trap :
    Productive (mirCallTree reactiveSwitchLoopMir []) ∧
      ¬ MayDiverge (mirCallTree reactiveSwitchLoopMir []) ∧
      ¬ PanicsIf (mirTrees reactiveSwitchLoopMir) (fun _ => True) (fun _ => True) := by
  have h := not_panicsIf_of_selfLoop (tree := mirTrees reactiveSwitchLoopMir) (x := [])
    (pre := fun _ => True) (panicCond := fun _ => True) rfl reactiveSwitchLoopMir_step
    trivial trivial
  exact h

/-- The MIR reactive loop has no completed execution, so it satisfies every only-if contract. -/
theorem reactiveSwitchLoopMir_neverPanics :
    NeverPanics (mirTrees reactiveSwitchLoopMir) (fun args => args = []) (fun _ _ => False) := by
  refine neverPanics_iff.2 ?_
  rintro _ rfl
  refine ⟨fun tr u hr hFault => ?_, fun tr out hr =>
    False.elim (not_reachesRet_cofix_selfLoop reactiveSwitchLoopMir_step tr out hr)⟩
  have hu := reaches_cofix_selfLoop reactiveSwitchLoopMir_step hr
  subst hu
  obtain ⟨u', i, k, hTau, hObs, hF⟩ := hFault
  have hu' := reaches_cofix_selfLoop reactiveSwitchLoopMir_step
    (Reaches.of_tauStar hTau (.refl u'))
  subst hu'
  rw [ITree.observe_cofix, reactiveSwitchLoopMir_step] at hObs
  injection hObs with hi _
  subst hi
  exact hF

/-! ## 5. Call-Boundary Guards (`kani#5095`) -/

/-! ### Both layers hold for the caller -/

/-- The captured caller keeps its call site and the callee is not linked. -/
theorem addCaller_callBoundaryPreserved (unwind : UnwindAction) :
    CallBoundaryPreserved (addCallerMir unwind) [] checkedAddU8Path :=
  (callBoundaryPreserved_iff _ _ _).1 rfl

/-- The runtime guard holds in the caller's initial memory. -/
theorem addCaller_calleeTableExcludes (unwind : UnwindAction) (args : List Value) :
    CalleeTableExcludes
      (initMachineStateWithCallees (addCallerMir unwind) args []).memory checkedAddU8Path :=
  (addCaller_callBoundaryPreserved unwind).calleeTableExcludes_init args

/-- The empty memory excludes the callee. -/
theorem emptyMemory_calleeTableExcludes : CalleeTableExcludes emptyMemory checkedAddU8Path :=
  calleeTableExcludes_of_callees_nil rfl rfl

/--
Under the guard the caller's call terminator emits the `MirCallE` request for
the callee with the call-site memory, instead of stepping into a body.
-/
theorem addCaller_call_emits_request (unwind : UnwindAction) (a b : Nat) :
    evalTerminator
        (initMachineStateWithMemory (addCallerMir unwind) (scalarArgs2 1 a b) emptyMemory)
        (mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
          (local_ 0) (.some 1) unwind))
        (.some (addCallerMir unwind)) =
      MirStepNode.extCall
        { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 a b,
          memory := emptyMemory }
        (resumeExternalCall
          (initMachineStateWithMemory (addCallerMir unwind) (scalarArgs2 1 a b) emptyMemory)
          (initMachineStateWithMemory (addCallerMir unwind) (scalarArgs2 1 a b)
            emptyMemory).frame.locals
          (local_ 0) 1 unwind) :=
  evalTerminator_extCall_of_call_site
    (s := initMachineStateWithMemory (addCallerMir unwind) (scalarArgs2 1 a b) emptyMemory)
    (func := fnItemOp checkedAddU8Path) (argOps := [.copy (local_ 1), .copy (local_ 2)])
    (destination := local_ 0) (targetBb := 1) (unwind := unwind)
    (targetDefPath := checkedAddU8Path) (argVals := scalarArgs2 1 a b)
    rfl rfl rfl emptyMemory_calleeTableExcludes rfl rfl

/-! ### Pre-capture inlining erases the boundary -/

/-- The caller after MIR inlining of `checked_add_u8`: the call site is gone. -/
def addCallerInlinedMir : CapturedMir :=
  checkedAddMir "panic_tests::add_caller" u8Ty u8CheckedTy .continue_

/-- The syntactic layer rejects the inlined caller. -/
theorem addCallerInlined_not_callBoundaryPreserved :
    ¬ CallBoundaryPreserved addCallerInlinedMir [] checkedAddU8Path := by
  intro h
  have hCheck := (callBoundaryPreserved_iff _ _ _).2 h
  have hFalse : callBoundaryPreserved addCallerInlinedMir [] checkedAddU8Path = false := rfl
  rw [hFalse] at hCheck
  nomatch hCheck

theorem addCallerInlined_not_bodyCallsDefPath :
    ¬ BodyCallsDefPath checkedAddU8Path addCallerInlinedMir :=
  fun h => addCallerInlined_not_callBoundaryPreserved ⟨h, rfl, rfl⟩

/--
A panic contract cannot detect the erasure: the inlined caller satisfies the
same total exact contract as the linked system. Only the boundary guard tells
them apart.
-/
theorem addCallerInlined_totalExact :
    TotalExactPanicContract (mirTrees addCallerInlinedMir) (scalarPre2 1) (sumPost 1)
      (overflows 1) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨a, b, -, -, rfl⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq
      exact (nat_ble_eq_true_iff _ _).1 heq
    · rename_i heq
      have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
      exact ⟨Nat.not_le.2 hlt,
        congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
          (wrapScalarBits_of_lt hlt)⟩)

/--
The inlined caller with an unreachable decoy block that still calls
`checked_add_u8`.
-/
def addCallerInlinedDeadCallMir : CapturedMir :=
  checkedAddMir "panic_tests::add_caller" u8Ty u8CheckedTy .continue_
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false } ]

/-- Scope limit of the syntactic layer: the dead-call decoy passes the check. -/
theorem addCallerInlinedDeadCall_callBoundaryPreserved :
    CallBoundaryPreserved addCallerInlinedDeadCallMir [] checkedAddU8Path :=
  (callBoundaryPreserved_iff _ _ _).1 rfl

/--
The decoy never exercises the boundary: the body evaluates under the
call-forbidding transformer, which rejects every `MirCallE` request, on all
inputs.
-/
theorem addCallerInlinedDeadCall_never_calls (a b : Nat) :
    wpMirNoCallSym 8 addCallerInlinedDeadCallMir
      (initMachineStateWithCallees addCallerInlinedDeadCallMir (scalarArgs2 1 a b) [])
      (fun _ => True) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals trivial

/--
The real caller does exercise the boundary: under the call-forbidding
transformer its evaluation is rejected at the call.
-/
theorem addCaller_calls (a b : Nat) :
    ¬ wpMirNoCallSym 8 (addCallerMir .continue_)
      (initMachineStateWithCallees (addCallerMir .continue_) (scalarArgs2 1 a b) [])
      (fun _ => True) := by
  intro h
  conv at h => whnf
  exact h

/-! ### Trait injection between sequential calls -/

def helperPath : DefPath := "panic_tests::helper"
def contractedPath : DefPath := "panic_tests::Contracted::run"
def evilImplPath : DefPath := "panic_tests::evil_impl"

/-- A body linked under an unrelated path. Executing it is undefined behavior. -/
def evilImplMir : CapturedMir :=
  mkBody evilImplPath 0 [ mkDecl .mut u8Ty ]
    [ { statements := [], terminator := mkTerm .unreachable, isCleanup := false } ]

/-- A trait implementation entry that dispatches the contracted callee to `evilImplMir`. -/
def injectedImpl : TraitImplEntry :=
  { traitRef := { defPath := contractedPath, args := [.uint .u8] }, implPath := evilImplPath }

/-- Memory at the first call: `evilImplMir` is linked and no trait implementation is registered. -/
def linkedMem : Memory := { emptyMemory with callees := [evilImplMir] }

/-- Memory a first callee could hand back: the same call frame with one more `TraitImplEntry`. -/
def injectedMem : Memory := { linkedMem with traitImpls := [injectedImpl] }

/--
`fn two_calls() -> u8 { helper(); Contracted::run::<u8>() }`:
`bb0: _0 = helper() -> bb1`, `bb1: _0 = Contracted::run::<u8>() -> bb2`,
`bb2: return`.
-/
def twoCallCallerMir : CapturedMir :=
  mkBody "panic_tests::two_calls" 0 [ mkDecl .mut u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp helperPath) [] (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call (fnItemOp contractedPath [.uint .u8]) [] (local_ 0) (.some 2)
            .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- Contract of the first callee, without any frame condition. -/
def helperContract : PanicMirCallContract where
  pre req := req.defPath = helperPath

/-- State of the caller at the first call. -/
def twoCallInit : MachineState := initMachineStateWithMemory twoCallCallerMir [] linkedMem

/-- The first call's request. -/
def helperReq : MirCallReq :=
  { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem }

/-- Before the first call the runtime guard holds for the contracted callee. -/
theorem linkedMem_calleeTableExcludes : CalleeTableExcludes linkedMem contractedPath :=
  calleeTableExcludes_of_no_callee_no_traitImpl rfl rfl

/-- The first call leaves the machine as a request carrying `linkedMem`. -/
theorem twoCall_first_call_emits_request :
    stepMirState twoCallCallerMir (.running twoCallInit) =
      MirStepNode.extCall helperReq
        (resumeExternalCall twoCallInit twoCallInit.frame.locals (local_ 0) 1 .continue_) :=
  rfl

/-- `callFramePreserved` accepts the injection: it does not mention `traitImpls`. -/
theorem injectedMem_callFramePreserved : callFramePreserved linkedMem injectedMem :=
  ⟨rfl, rfl, rfl, rfl, [], rfl⟩

/-- The frame-preserving contract accepts the answer that injects the trait implementation. -/
theorem helper_withFramePreserved_accepts_injection :
    helperContract.withFramePreserved.toMirCallContract.post helperReq
      (.returned (.scalar { bits := 0, sizeBytes := 1 }) injectedMem) :=
  ⟨trivial, injectedMem_callFramePreserved⟩

/-- After the injection `lookupCallee` resolves the contracted callee to `evilImplMir`. -/
theorem injectedMem_lookupCallee :
    lookupCallee injectedMem.callees emptyLayoutTable contractedPath [.uint .u8]
      injectedMem.traitImpls = .some evilImplMir :=
  rfl

/-- The injection breaks the runtime guard. -/
theorem injectedMem_not_calleeTableExcludes :
    ¬ CalleeTableExcludes injectedMem contractedPath := by
  intro h
  have hNone := h emptyLayoutTable [.uint .u8]
  rw [injectedMem_lookupCallee] at hNone
  nomatch hNone

/-- State of the caller at the second call when the first call returned `mem`. -/
def twoCallSecond (mem : Memory) : MachineState :=
  { frame :=
      { blockIdx := 1, stmtIdx := 0
        locals := [.init (.scalar { bits := 0, sizeBytes := 1 })] }
    memory := mem }

/-- The first call resumes the caller at the second call with the answer's memory. -/
theorem twoCall_resume_injected :
    resumeExternalCall twoCallInit twoCallInit.frame.locals (local_ 0) 1 .continue_
        (.returned (.scalar { bits := 0, sizeBytes := 1 }) injectedMem) =
      .running (twoCallSecond injectedMem) :=
  rfl

/--
Without trait preservation the second call is silently inlined: from the injected
memory the caller takes a silent step into `evilImplMir` instead of emitting a
request, and the execution reaches undefined behavior.
-/
theorem twoCall_injected_second_call_inlined :
    (∃ st, stepMirState twoCallCallerMir (.running (twoCallSecond injectedMem)) = .tau st) ∧
      ¬ TreeSafe (mirTree twoCallCallerMir (twoCallSecond injectedMem)) :=
  ⟨⟨_, rfl⟩,
    reachesFaultBounded_not_treeSafe 8 twoCallCallerMir (twoCallSecond injectedMem) rfl⟩

/-- The trait-preserving contract rejects the answer that injects the trait implementation. -/
theorem helper_withTraitsPreserved_rejects_injection :
    ¬ helperContract.withTraitsPreserved.toMirCallContract.post helperReq
      (.returned (.scalar { bits := 0, sizeBytes := 1 }) injectedMem) := by
  intro h
  have hTraits : [injectedImpl] = ([] : List TraitImplEntry) := h.2.2
  nomatch hTraits

/--
With trait preservation the guard survives the first call: every answer the
strengthened contract accepts keeps the contracted callee excluded.
-/
theorem twoCall_guard_preserved (retVal : Value) (memAfter : Memory)
    (hPost : helperContract.withTraitsPreserved.toMirCallContract.post helperReq
      (.returned retVal memAfter)) :
    CalleeTableExcludes memAfter contractedPath :=
  CalleeTableExcludes.of_withTraitsPreserved_returned helperContract .forbidAbort hPost
    linkedMem_calleeTableExcludes

/--
Under the guard the second call emits its request from any state: with trait
preservation, the contracted callee's boundary is still there after the first
call.
-/
theorem twoCall_second_call_emits_request (s : MachineState)
    (hExcl : CalleeTableExcludes s.memory contractedPath) :
    evalTerminator s
        (mkTerm (.call (fnItemOp contractedPath [.uint .u8]) [] (local_ 0) (.some 2)
          .continue_))
        (.some twoCallCallerMir) =
      MirStepNode.extCall
        { defPath := contractedPath, typeArgs := [.uint .u8], args := [],
          memory := s.memory }
        (resumeExternalCall s s.frame.locals (local_ 0) 2 .continue_) :=
  evalTerminator_extCall_of_call_site (s := s)
    (func := fnItemOp contractedPath [.uint .u8]) (argOps := []) (destination := local_ 0)
    (targetBb := 2) (unwind := .continue_) (targetDefPath := contractedPath)
    (argVals := []) rfl rfl rfl hExcl rfl rfl

/-! ### `AbortPolicy` separation -/

/-- A body that aborts immediately: `bb0: terminate`. -/
def alwaysAbortMir : CapturedMir :=
  mkBody "panic_tests::always_abort" 0 [ mkDecl .mut unitTy ]
    [ { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := false } ]

/-- The body aborts under every abort condition `cond` that holds of its input. -/
theorem alwaysAbort_totalExact (cond : List Value → Prop) (hCond : cond []) :
    TotalExactPolicyPanicContract (mirTrees alwaysAbortMir) (fun args => args = [])
      (fun _ _ => False) (fun _ => False) (.abortOnlyIf cond) :=
  totalExactPolicyPanicContract_of_wpMirSym 4 (by
    rintro _ rfl
    exact ⟨hCond, fun h => h⟩)

theorem alwaysAbort_reaches_abort :
    ∃ tr, ReachesRet (mirCallTree alwaysAbortMir []) tr .abort :=
  (alwaysAbort_totalExact (fun _ => True) trivial).exact.2.2 [] rfl trivial

/-- The unconditional waiver admits the abort. -/
theorem alwaysAbort_waiveAbortUnchecked :
    PanicsWithPolicyOnlyIf (mirTrees alwaysAbortMir) (fun args => args = [])
      (fun _ _ => False) (fun _ => False) .waiveAbortUnchecked :=
  (alwaysAbort_totalExact (fun _ => True) trivial).exact.1.mono (fun _ h => h)
    (fun _ _ _ h => h) (fun _ _ h => h) (AbortPolicy.le_waiveAbortUnchecked _)

/-- `forbidAbort` rejects the abort. -/
theorem alwaysAbort_not_forbidAbort :
    ¬ PanicsWithPolicyOnlyIf (mirTrees alwaysAbortMir) (fun args => args = [])
      (fun _ _ => False) (fun _ => False) .forbidAbort := by
  intro h
  obtain ⟨tr, hr⟩ := alwaysAbort_reaches_abort
  exact h.allowsAbort_of_aborts (x := []) rfl hr

/-- `PanicsOnlyIf` rejects the abort, even with `panicCond := True`. -/
theorem alwaysAbort_not_panicsOnlyIf :
    ¬ PanicsOnlyIf (mirTrees alwaysAbortMir) (fun args => args = [])
      (fun _ _ => True) (fun _ => True) := by
  intro h
  obtain ⟨tr, hr⟩ := alwaysAbort_reaches_abort
  exact h.not_reaches_abort (x := []) rfl hr

/-- `abortOnlyIf cond` admits the abort exactly when `cond` holds of the input. -/
theorem alwaysAbort_abortOnlyIf_iff (cond : List Value → Prop) :
    PanicsWithPolicyOnlyIf (mirTrees alwaysAbortMir) (fun args => args = [])
      (fun _ _ => False) (fun _ => False) (.abortOnlyIf cond) ↔ cond [] := by
  constructor
  · intro h
    obtain ⟨tr, hr⟩ := alwaysAbort_reaches_abort
    exact h.allowsAbort_of_aborts (x := []) rfl hr
  · intro hCond
    exact (alwaysAbort_totalExact cond hCond).exact.1

/--
An exact contract with the unconditional waiver demands an abort on every input,
so it rejects checked addition, which returns on `(0, 0)`.
-/
theorem checkedAddU8_not_exactPolicy_waiveAbortUnchecked :
    ¬ ExactPolicyPanicContract (mirTrees checkedAddU8Mir) (scalarPre2 1) (sumPost 1)
      (overflows 1) .waiveAbortUnchecked := by
  intro h
  obtain ⟨tr, hr⟩ := h.2.2 _ zeroArgs_pre trivial
  exact checkedAddU8_exact.1.not_reaches_abort zeroArgs_pre hr

/-! ## 6. Ground Semantics Probes -/

/-- Value of a successfully evaluated rvalue. -/
def rvalueValue? : RvalueEvalResult → Option Value
  | .ok v _ _ => some v
  | _ => none

/-- Whether evaluating an rvalue is undefined behavior. -/
def rvalueIsUb : RvalueEvalResult → Bool
  | .ub => true
  | _ => false

/-! ### `kani#5202`: `arith_offset` and `BinOp.offset` on dangling and zero-sized pointers -/

def ptrConstUnitTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
def ptrConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
def isizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }

/-- Locals `_1 : ptrTy` and `_2 : isize` of the offset probes. -/
def offsetDecls (ptrTy : Ty) : List LocalDecl :=
  [ mkDecl .mut ptrTy, mkDecl .not ptrTy, mkDecl .not isizeTy ]

def offsetLocals (ptr : Value) (count : Nat) : List LocalSlot :=
  [ .uninit, .init ptr, .init (.scalar { bits := count, sizeBytes := 8 }) ]

/-- `Offset(copy _1, copy _2)`. -/
def offsetRv : Rvalue := .binaryOp .offset (.copy (local_ 1)) (.copy (local_ 2))

/-- Provenance-free pointer value with address `addr`. -/
def addrPtr (addr : Nat) : Value := .scalar { bits := addr, sizeBytes := 8 }

/--
`BinOp.offset` on a provenance-free pointer to a zero-sized type accepts every
count and leaves the address unchanged: `NonNull::<()>::dangling()` (`1`), an
address aligned to `4`, and null.
-/
theorem kani5202_binop_offset_zst_scalar_ptr :
    rvalueValue? (evalRvalue (offsetLocals (addrPtr 1) 5) offsetRv emptyMemory
        (offsetDecls ptrConstUnitTy)) = some (addrPtr 1) ∧
      rvalueValue? (evalRvalue (offsetLocals (addrPtr 4) 5) offsetRv emptyMemory
        (offsetDecls ptrConstUnitTy)) = some (addrPtr 4) ∧
      rvalueValue? (evalRvalue (offsetLocals (addrPtr 0) 5) offsetRv emptyMemory
        (offsetDecls ptrConstUnitTy)) = some (addrPtr 0) :=
  ⟨rfl, rfl, rfl⟩

/--
`BinOp.offset` on a provenance-free pointer to `u8` accepts a zero count and is
undefined behavior for a non-zero count.
-/
theorem kani5202_binop_offset_u8_scalar_ptr :
    rvalueValue? (evalRvalue (offsetLocals (addrPtr 1) 0) offsetRv emptyMemory
        (offsetDecls ptrConstU8Ty)) = some (addrPtr 1) ∧
      rvalueIsUb (evalRvalue (offsetLocals (addrPtr 1) 1) offsetRv emptyMemory
        (offsetDecls ptrConstU8Ty)) = true :=
  ⟨rfl, rfl⟩

/--
The `arith_offset` intrinsic is undefined behavior on every provenance-free
pointer value, whatever the count, the pointee type, and the machine state: its
evaluator accepts only `Value.ptr`. `BinOp.offset` accepts the same pointers
whenever the byte offset is zero, so the two evaluators disagree on
`NonNull::<()>::dangling()`, on any aligned address of a zero-sized type, and on
null.
-/
theorem kani5202_arith_offset_scalar_ptr_ub (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand)
    (addr count : ScalarInt) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall .arithOffset s target bodyLocalDecls bodyLayouts argOps
        [.scalar addr, .scalar count] locals' destination targetBb =
      MirStepNode.fail .ub :=
  rfl

/-- A pointer whose provenance tag `42` names no borrow and no global allocation. -/
def danglingPtr : ProvenancePtr := { allocId := 42, offsetBytes := 0 }

def probeBorrow (tag target : Nat) (perm : TreeBorrowPerm) (allocDead : Bool) : BorrowEntry :=
  { tag := tag, targetLocal := target, targetProjection := [], perm := perm,
    allocDead := allocDead }

/-- A memory whose only borrow is unrelated to tag `42`. -/
def memUnrelatedBorrow : Memory :=
  { emptyMemory with borrows := [probeBorrow 7 0 .unique false] }

/-- A memory in which the allocation of tag `42` was freed. -/
def memFreedTag42 : Memory :=
  { emptyMemory with borrows := [probeBorrow 42 0 .disabled true] }

/-- A memory in which tag `42` borrows the live zero-sized local `_3`. -/
def memLiveZeroByteAlloc42 : Memory :=
  { emptyMemory with borrows := [probeBorrow 42 3 .unique false] }

def zstDecls : List LocalDecl := offsetDecls ptrConstU8Ty ++ [mkDecl .not unitTy]

def zstLocals (count : Nat) : List LocalSlot :=
  offsetLocals (.ptr danglingPtr 8) count ++ [.init .unit]

/--
`ptrAllocByteBound?` on an unknown tag: no bound in the completely empty memory,
and bound `0` as soon as an unrelated borrow exists, when the allocation was
freed, and for a live zero-byte allocation.
-/
theorem kani5202_ptrAllocByteBound_probes :
    ptrAllocByteBound? (offsetLocals (.ptr danglingPtr 8) 1) emptyMemory
        (offsetDecls ptrConstU8Ty) emptyLayoutTable danglingPtr = none ∧
      ptrAllocByteBound? (offsetLocals (.ptr danglingPtr 8) 1) memUnrelatedBorrow
        (offsetDecls ptrConstU8Ty) emptyLayoutTable danglingPtr = some 0 ∧
      ptrAllocByteBound? (offsetLocals (.ptr danglingPtr 8) 1) memFreedTag42
        (offsetDecls ptrConstU8Ty) emptyLayoutTable danglingPtr = some 0 ∧
      ptrAllocByteBound? (zstLocals 1) memLiveZeroByteAlloc42 zstDecls emptyLayoutTable
        danglingPtr = some 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
`BinOp.offset` is not monotone in unrelated memory: a non-zero offset of the
dangling pointer succeeds in the empty memory and is undefined behavior once an
unrelated borrow exists, after the allocation was freed, and on a live zero-byte
allocation. A zero count succeeds in all four memories.
-/
theorem kani5202_binop_offset_dangling_ptr :
    rvalueValue? (evalRvalue (offsetLocals (.ptr danglingPtr 8) 1) offsetRv emptyMemory
        (offsetDecls ptrConstU8Ty)) = some (.ptr { danglingPtr with offsetBytes := 1 } 8) ∧
      rvalueIsUb (evalRvalue (offsetLocals (.ptr danglingPtr 8) 1) offsetRv
        memUnrelatedBorrow (offsetDecls ptrConstU8Ty)) = true ∧
      rvalueIsUb (evalRvalue (offsetLocals (.ptr danglingPtr 8) 1) offsetRv memFreedTag42
        (offsetDecls ptrConstU8Ty)) = true ∧
      rvalueIsUb (evalRvalue (zstLocals 1) offsetRv memLiveZeroByteAlloc42 zstDecls) = true ∧
      rvalueValue? (evalRvalue (offsetLocals (.ptr danglingPtr 8) 0) offsetRv
        memUnrelatedBorrow (offsetDecls ptrConstU8Ty)) = some (.ptr danglingPtr 8) ∧
      rvalueValue? (evalRvalue (offsetLocals (.ptr danglingPtr 8) 0) offsetRv memFreedTag42
        (offsetDecls ptrConstU8Ty)) = some (.ptr danglingPtr 8) ∧
      rvalueValue? (evalRvalue (zstLocals 0) offsetRv memLiveZeroByteAlloc42 zstDecls) =
        some (.ptr danglingPtr 8) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `arith_offset` wraps on the dangling pointer without consulting any memory. -/
theorem kani5202_arith_offset_dangling_ptr :
    evalArithOffset danglingPtr 8 { bits := 1, sizeBytes := 8 } 1 =
      some { danglingPtr with offsetBytes := 1 } :=
  rfl

/-! ### `kani#5219`: `[MaybeUninit<u8>; 4]` subslices and union slots -/

def probeLayout (size : Nat) (fields : FieldsShape) (fieldLayouts : List Nat := []) :
    TypeLayout :=
  { size := { bytes := size }, align := { bytes := 1 }, backendRepr := .memory
    fields := fields, variants := .single 0, isUninhabited := false
    fieldLayouts := fieldLayouts }

/--
Layout table of the union probes: `0` is `u8`, `1` is `()`, `2` is the union
`MaybeUninit<u8>` with fields `uninit: ()` and `value: u8`, `3` is
`[MaybeUninit<u8>; 4]`, `4` is `usize`, and `5` is `&[MaybeUninit<u8>]`.
-/
def muLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true
    entries :=
      [ probeLayout 1 .primitive
      , probeLayout 0 .primitive
      , probeLayout 1 (.union 2) [1, 0]
      , probeLayout 4 (.array { bytes := 1 } 4) [2]
      , probeLayout 8 .primitive
      , probeLayout 16 .primitive ] }

def muKind : RigidTy := .adt "core::mem::MaybeUninit" [.uint .u8]
def muU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def muUnitTy : Ty := { kind := .tuple [], layoutIdx := 1 }
def muTy : Ty := { kind := muKind, layoutIdx := 2 }
def muArr4Ty : Ty := { kind := .array muKind 4, layoutIdx := 3 }
def muUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 4 }
def muSliceRefTy : Ty := { kind := .ref .not (.slice muKind), layoutIdx := 5 }

/-- Locals `_1 : [MaybeUninit<u8>; 4]` and `_3 : &[MaybeUninit<u8>]`. -/
def muDecls : List LocalDecl :=
  [ mkDecl .mut muTy, mkDecl .not muArr4Ty, mkDecl .mut muUsizeTy, mkDecl .not muSliceRefTy ]

/-- Union slot value of an uninitialized `MaybeUninit<u8>`: both fields hold `()`. -/
def muUninitSlot : Value := .aggregate 0 [.unit, .unit]

/-- Union slot value of `MaybeUninit::new(n)`. -/
def muInitSlot (n : Nat) : Value := .aggregate 0 [.unit, .scalar { bits := n, sizeBytes := 1 }]

/-- Array whose elements are raw `Value.uninit`. -/
def muRawArr : Value := .aggregate 0 [.uninit, .uninit, .uninit, .uninit]

/-- Array whose elements are union slot values of uninitialized `MaybeUninit<u8>`. -/
def muSlotArr : Value := .aggregate 0 [muUninitSlot, muUninitSlot, muUninitSlot, muUninitSlot]

/-- Array `[new(7), uninit slot, new(9), raw uninit]`. -/
def muPartArr : Value := .aggregate 0 [muInitSlot 7, muUninitSlot, muInitSlot 9, .uninit]

def muLocals (arr : Value) : List LocalSlot := [.uninit, .init arr, .uninit, .uninit]

/-- `copy _1.proj`. -/
def muRead (proj : List ProjectionElem) : Rvalue :=
  .use (.copy { local_ := 1, projection := proj })

/--
`tyProjTouchesUnion` does not report `.subslice` and `.constantIndex` on
`[MaybeUninit<u8>; 4]`: only a projection that continues into a union field is
union-aware.
-/
theorem kani5219_tyProjTouchesUnion_probes :
    tyProjTouchesUnion muDecls muLayouts muArr4Ty [.subslice 1 3 false] = false ∧
      tyProjTouchesUnion muDecls muLayouts muArr4Ty [.constantIndex 1 4 false] = false ∧
      placeTouchesUnion muDecls muLayouts
        { local_ := 1, projection := [.subslice 1 3 false] } = false ∧
      tyProjTouchesUnion muDecls muLayouts muArr4Ty
        [.constantIndex 1 4 false, .field 1 muU8Ty] = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Reads of an element and of a subslice: a raw `.uninit` element faults, a union
slot value succeeds.
-/
theorem kani5219_element_and_subslice_reads :
    rvalueIsUb (evalRvalue (muLocals muRawArr) (muRead [.constantIndex 1 4 false])
        emptyMemory muDecls muLayouts) = true ∧
      rvalueValue? (evalRvalue (muLocals muSlotArr) (muRead [.constantIndex 1 4 false])
        emptyMemory muDecls muLayouts) = some muUninitSlot ∧
      rvalueIsUb (evalRvalue (muLocals muRawArr) (muRead [.subslice 1 3 false])
        emptyMemory muDecls muLayouts) = true ∧
      rvalueValue? (evalRvalue (muLocals muSlotArr) (muRead [.subslice 1 3 false])
        emptyMemory muDecls muLayouts) = some (.aggregate 0 [muUninitSlot, muUninitSlot]) ∧
      rvalueValue? (evalRvalue (muLocals muPartArr) (muRead [.subslice 0 2 false])
        emptyMemory muDecls muLayouts) = some (.aggregate 0 [muInitSlot 7, muUninitSlot]) ∧
      rvalueIsUb (evalRvalue (muLocals muPartArr) (muRead [.subslice 2 4 false])
        emptyMemory muDecls muLayouts) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Reads of union fields through `.constantIndex`: the zero-sized `uninit: ()`
field reads from a union slot value and faults on a raw `.uninit` element, and
the `value: u8` field reads only from an initialized slot.
-/
theorem kani5219_union_field_reads :
    rvalueValue? (evalRvalue (muLocals muPartArr)
        (muRead [.constantIndex 1 4 false, .field 0 muUnitTy])
        emptyMemory muDecls muLayouts) = some .unit ∧
      rvalueIsUb (evalRvalue (muLocals muPartArr)
        (muRead [.constantIndex 3 4 false, .field 0 muUnitTy])
        emptyMemory muDecls muLayouts) = true ∧
      rvalueValue? (evalRvalue (muLocals muPartArr)
        (muRead [.constantIndex 0 4 false, .field 1 muU8Ty])
        emptyMemory muDecls muLayouts) = some (.scalar { bits := 7, sizeBytes := 1 }) ∧
      rvalueIsUb (evalRvalue (muLocals muPartArr)
        (muRead [.constantIndex 1 4 false, .field 1 muU8Ty])
        emptyMemory muDecls muLayouts) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
`Rvalue.len` and `evalPlaceLen` on a subslice: the length is returned for union
slot values and is undefined behavior when the subslice holds a raw `.uninit`
element, although a length does not read any element.
-/
theorem kani5219_len_probes :
    rvalueValue? (evalPlaceLen (muLocals muSlotArr)
        { local_ := 1, projection := [.subslice 1 3 false] } emptyMemory muDecls muLayouts) =
        some (.scalar { bits := 2, sizeBytes := 8 }) ∧
      rvalueIsUb (evalPlaceLen (muLocals muRawArr)
        { local_ := 1, projection := [.subslice 1 3 false] } emptyMemory muDecls muLayouts) =
        true ∧
      rvalueValue? (evalRvalue (muLocals muPartArr)
        (.len { local_ := 1, projection := [.subslice 0 2 false] })
        emptyMemory muDecls muLayouts) = some (.scalar { bits := 2, sizeBytes := 8 }) ∧
      rvalueIsUb (evalRvalue (muLocals muPartArr)
        (.len { local_ := 1, projection := [.subslice 2 4 false] })
        emptyMemory muDecls muLayouts) = true ∧
      rvalueValue? (evalPlaceLen (muLocals muSlotArr) (local_ 1) emptyMemory muDecls
        muLayouts) = some (.scalar { bits := 4, sizeBytes := 8 }) ∧
      rvalueIsUb (evalPlaceLen (muLocals muRawArr) (local_ 1) emptyMemory muDecls
        muLayouts) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `resolveProjectedTy` keeps the array type `[MaybeUninit<u8>; 4]` under `.subslice 1 3`. -/
theorem kani5219_resolveProjectedTy_subslice :
    (resolveProjectedTy muLayouts muArr4Ty [.subslice 1 3 false]).map (·.kind) =
      some (.array muKind 4) :=
  rfl

/-- Memory in which tag `5` is a shared borrow of the whole array `_1`. -/
def muSliceMem : Memory :=
  { emptyMemory with
    borrows := [probeBorrow 5 1 .frozen false]
    nextTag := 6 }

/-- Fat pointer `&_1[..]` of length `4` with tag `5`. -/
def muFatPtr : Value :=
  .aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar { bits := 4, sizeBytes := 8 }]

def muSliceLocals (arr : Value) : List LocalSlot :=
  [.uninit, .init arr, .uninit, .init muFatPtr]

/-- `copy (*_3).proj`. -/
def muSliceRead (proj : List ProjectionElem) : Rvalue :=
  .use (.copy { local_ := 3, projection := .deref :: proj })

/--
Whole-slice `.uninit` contagion on a borrow-backed `&[MaybeUninit<u8>]`: with
union slot values every operation succeeds, and one raw `.uninit` element makes
`Len`, an element read, and a subslice read fault, including reads of
initialized elements that succeed on the array local itself.
-/
theorem kani5219_borrow_backed_slice_contagion :
    rvalueValue? (evalRvalue (muSliceLocals muSlotArr)
        (.len { local_ := 3, projection := [.deref] }) muSliceMem muDecls muLayouts) =
        some (.scalar { bits := 4, sizeBytes := 8 }) ∧
      rvalueValue? (evalRvalue (muSliceLocals muSlotArr)
        (muSliceRead [.constantIndex 0 1 false]) muSliceMem muDecls muLayouts) =
        some muUninitSlot ∧
      rvalueValue? (evalRvalue (muSliceLocals muSlotArr)
        (muSliceRead [.subslice 2 4 false]) muSliceMem muDecls muLayouts) =
        some (.aggregate 0 [muUninitSlot, muUninitSlot]) ∧
      rvalueIsUb (evalRvalue (muSliceLocals muPartArr)
        (.len { local_ := 3, projection := [.deref] }) muSliceMem muDecls muLayouts) = true ∧
      rvalueIsUb (evalRvalue (muSliceLocals muPartArr)
        (muSliceRead [.constantIndex 0 1 false]) muSliceMem muDecls muLayouts) = true ∧
      rvalueIsUb (evalRvalue (muSliceLocals muPartArr)
        (muSliceRead [.subslice 0 2 false]) muSliceMem muDecls muLayouts) = true ∧
      rvalueValue? (evalRvalue (muLocals muPartArr) (muRead [.subslice 0 2 false])
        emptyMemory muDecls muLayouts) = some (.aggregate 0 [muInitSlot 7, muUninitSlot]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Pre-panic mutation: modular linking versus inlining -/

def u8MutRefTy : Ty := { kind := .ref .mut (.uint .u8), layoutIdx := 0 }

def boolConst (b : Bool) : Operand :=
  .constant
    { ty := boolTy, val := .scalar (.int { bits := if b then 1 else 0, sizeBytes := 1 }) }

def poisonPath : DefPath := "panic_tests::poison"

/--
`fn poison(p: &mut u8) { *p = 1; panic!() }`:
`bb0: (*_1) = const 1_u8; assert(const false) -> [success: bb1, unwind continue]`.
The callee writes through its `&mut` argument and then panics.
-/
def poisonMir : CapturedMir :=
  mkBody poisonPath 1 [ mkDecl .mut unitTy, mkDecl .not u8MutRefTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 1, projection := [.deref] } (.use (u8Const 1))) ]
        terminator := mkTerm (.assert (boolConst false) true 1 .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/--
`fn cleanup_reads(p: &mut u8) -> u8 { poison(p); 0 }` with a cleanup block that
inspects `*p`:
`bb0: _2 = poison(copy _1) -> [return: bb1, unwind: bb2]`,
`bb1: _0 = const 0_u8; return`,
`bb2 (cleanup): _0 = copy (*_1); switchInt(copy _0) -> [0: bb3, otherwise: bb4]`,
`bb3 (cleanup): resume`, `bb4 (cleanup): unreachable`.
The cleanup block is free of undefined behavior exactly when `*p` is still `0`.
-/
def cleanupReadsMir : CapturedMir :=
  mkBody "panic_tests::cleanup_reads" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8MutRefTy, mkDecl .mut unitTy ]
    [ { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp poisonPath) [.copy (local_ 1)] (local_ 2) (.some 1)
            (.cleanup 2))
        isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (u8Const 0))) ]
        terminator := mkTerm .return_
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.copy { local_ := 1, projection := [.deref] }))) ]
        terminator :=
          mkTerm (.switchInt (.copy (local_ 0)) { branches := [(0, 3)], otherwise := 4 })
        isCleanup := true }
    , { statements := [], terminator := mkTerm .unwindResume, isCleanup := true }
    , { statements := [], terminator := mkTerm .unreachable, isCleanup := true } ]

/--
Initial memory: tag `1` is a unique borrow of the caller-owned referent slot
`5`, which holds `0_u8`.
-/
def referentMem : Memory :=
  { emptyMemory with
    borrows := [probeBorrow 1 5 .unique false]
    nextTag := 2
    callerLocals :=
      [ .dead, .dead, .dead, .dead, .dead, .init (.scalar { bits := 0, sizeBytes := 1 }) ] }

/-- The argument `p`: a pointer with tag `1`. -/
def referentArgs : List Value := [.ptr { allocId := 1, offsetBytes := 0 } 8]

/-- The request `cleanup_reads` emits for `poison(p)`. -/
def poisonReq : MirCallReq :=
  { defPath := poisonPath, typeArgs := [], args := referentArgs, memory := referentMem }

/-- Contract of the call: `poison` unwinds and presents the request memory. -/
def poisonContract : MirCallContract where
  pre req := req = poisonReq
  post req ans := ans = .panicked req.memory

/--
The linked callee implements `poisonContract`: it writes `1` through `p`,
panics, and `outcomeToCallAns` presents the request memory, in which `*p` is
still `0`.
-/
theorem poison_holdsTotallyOn (fallback : ExternalCallHandler) :
    poisonContract.holdsTotallyOn (linkCalleeHandler poisonMir fallback) :=
  holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallSym poisonContract poisonMir fallback 8
    (fun _ h => h ▸ rfl) (by
      rintro _ rfl
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      all_goals rfl)

/-- The only answer of the linked callee is an unwind with the request memory. -/
theorem poison_linked_answer (fallback : ExternalCallHandler)
    (tr : List (Event MirClosedEffect)) (ans : MirCallAns)
    (hr : ReachesRet (linkCalleeHandler poisonMir fallback poisonReq) tr ans) :
    ans = .panicked referentMem :=
  (holdsOn_of_holdsTotallyOn (poison_holdsTotallyOn fallback) poisonReq rfl).2 tr ans hr

/-- Input of the rollback probe. -/
def rollbackPre (x : MirInput) : Prop := x.1 = referentArgs ∧ x.2 = referentMem

/--
Modular linking: the cleanup block runs on the request memory, reads `*p = 0`,
and resumes unwinding. The linked system is fault-free and panics.
-/
theorem rollback_modular_totalExact (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees cleanupReadsMir (linkCalleeHandler poisonMir fallback))
      rollbackPre (fun _ _ => False) (fun _ => True) :=
  totalExactPolicyPanicContract_forbidAbort_iff.1
    (mirHandled_totalExactPolicyPanicContract_of_wpMirModularSym poisonContract
      (poison_holdsTotallyOn fallback) 16 (by
        rintro ⟨_, _⟩ ⟨rfl, rfl⟩
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        refine ⟨rfl, fun ans hPost => ?_⟩
        subst hPost
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        all_goals exact ⟨trivial, fun h => h⟩))

/--
Inlining: the callee's write reaches the caller's cleanup block, which reads
`*p = 1` and executes `unreachable`.
-/
theorem rollback_inlined_not_treeSafe :
    ¬ TreeSafe (mirStatefulTreeWithCallees cleanupReadsMir referentArgs referentMem
      [poisonMir]) :=
  reachesFaultBounded_not_treeSafe 24 cleanupReadsMir
    (initMachineStateWithMemoryAndCallees cleanupReadsMir referentArgs referentMem
      [poisonMir]) rfl

/--
Pre-panic mutation rollback divergence. For the same caller, callee, and input:
linked through `linkCalleeHandler`, the system is fault-free and panics, because
`MirOutcome.panic` carries no memory and the cleanup block sees the request
memory; with the callee inlined, the cleanup block sees the callee's write and
reaches undefined behavior. A modular proof of the cleanup path therefore does
not transfer to the inlined program.
-/
theorem outcomeToCallAns_prePanic_mutation_rollback_divergence
    (fallback : ExternalCallHandler) :
    (TreeSafe (mirHandledTree cleanupReadsMir referentArgs referentMem
        (linkCalleeHandler poisonMir fallback)) ∧
      ∃ tr, ReachesRet (mirHandledTree cleanupReadsMir referentArgs referentMem
        (linkCalleeHandler poisonMir fallback)) tr .panic) ∧
      ¬ TreeSafe (mirStatefulTreeWithCallees cleanupReadsMir referentArgs referentMem
        [poisonMir]) :=
  have hPre : rollbackPre (referentArgs, referentMem) := ⟨rfl, rfl⟩
  ⟨⟨(rollback_modular_totalExact fallback).exact.1.treeSafe hPre,
      (rollback_modular_totalExact fallback).exact.2 _ hPre trivial⟩,
    rollback_inlined_not_treeSafe⟩

/-! ### `TerminatorKind.tailCall` -/

def tailTargetPath : DefPath := "panic_tests::tail_target"

/-- `fn tail_caller(x: u8) -> u8 { become tail_target(x) }`. -/
def tailCallerMir : CapturedMir :=
  mkBody "panic_tests::tail_caller" 1 [ mkDecl .mut u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator := mkTerm (.tailCall (fnItemOp tailTargetPath) [.copy (local_ 1)])
        isCleanup := false } ]

/-- A memory with an unprotected unique borrow of the frame local `_1`. -/
def tailUnprotectedMem : Memory :=
  { emptyMemory with borrows := [probeBorrow 1 1 .unique false], nextTag := 2 }

/-- A memory in which the unique borrow of `_1` carries the active protector `1`. -/
def tailProtectedMem : Memory :=
  { emptyMemory with
    borrows := [{ probeBorrow 1 1 .unique false with protector := some 1 }]
    nextTag := 2
    activeProtectors := [1] }

def tailArgs : List Value := [.scalar { bits := 3, sizeBytes := 1 }]

theorem tailUnprotectedMem_calleeTableExcludes :
    CalleeTableExcludes tailUnprotectedMem tailTargetPath :=
  calleeTableExcludes_of_callees_nil rfl rfl

/--
Under the guard and without a protector conflict, the tail call tears down the
caller frame and then emits the `MirCallE` request: the request memory has the
frame's borrow disabled and its allocation marked dead.
-/
theorem tailCall_emits_request_after_teardown :
    evalTerminator (initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
        (mkTerm (.tailCall (fnItemOp tailTargetPath) [.copy (local_ 1)]))
        (.some tailCallerMir) =
      MirStepNode.extCall
        { defPath := tailTargetPath, typeArgs := [], args := tailArgs
          memory :=
            { tailUnprotectedMem with borrows := [probeBorrow 1 1 .disabled true] } }
        resumeExternalTailCall :=
  evalTerminator_tailCall_extCall_of_calleeTableExcludes
    (s := initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
    (func := fnItemOp tailTargetPath) (argOps := [.copy (local_ 1)])
    (target :=
      { defPath := tailTargetPath, typeArgs := [], fnSig := .none, isIndirect := false })
    (argVals := tailArgs) rfl rfl rfl rfl tailUnprotectedMem_calleeTableExcludes

/--
With a protector conflict on the frame being torn down, the tail call is
undefined behavior and emits no request.
-/
theorem tailCall_protectorConflict_ub :
    evalTerminator (initMachineStateWithMemory tailCallerMir tailArgs tailProtectedMem)
        (mkTerm (.tailCall (fnItemOp tailTargetPath) [.copy (local_ 1)]))
        (.some tailCallerMir) =
      MirStepNode.fail .ub :=
  evalTerminator_tailCall_ub_of_protectorConflict
    (s := initMachineStateWithMemory tailCallerMir tailArgs tailProtectedMem)
    (func := fnItemOp tailTargetPath) (argOps := [.copy (local_ 1)])
    (target :=
      { defPath := tailTargetPath, typeArgs := [], fnSig := .none, isIndirect := false })
    (argVals := tailArgs) rfl rfl rfl rfl

/-- The same two facts on the stepped machine. -/
theorem tailCall_step_probes :
    (∃ k, stepMirState tailCallerMir
        (.running (initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)) =
        MirStepNode.extCall
          { defPath := tailTargetPath, typeArgs := [], args := tailArgs
            memory :=
              { tailUnprotectedMem with borrows := [probeBorrow 1 1 .disabled true] } }
          k) ∧
      stepMirState tailCallerMir
        (.running (initMachineStateWithMemory tailCallerMir tailArgs tailProtectedMem)) =
        MirStepNode.fail .ub :=
  ⟨⟨_, rfl⟩, rfl⟩

/-! ## 7. Bundle -/

/--
Conjunction of every theorem in this file, each at its stated type. The axiom
check below therefore covers all positive contracts, compositions, refutations,
call-boundary guards, and ground semantics probes at once.
-/
theorem all_panic_contracts_tests :
    (type_of% @checkedAddU8_wp) ∧
    (type_of% @checkedAddU32_wp) ∧
    (type_of% @checkedDivU8_wp) ∧
    (type_of% @checkedIndex_wp) ∧
    (type_of% @checkedAddU8_totalExact) ∧
    (type_of% @checkedAddU8_exact) ∧
    (type_of% @checkedAddU32_totalExact) ∧
    (type_of% @checkedAddU32_exact) ∧
    (type_of% @checkedAddU8_dichotomy) ∧
    (type_of% @checkedDivU8_totalExact) ∧
    (type_of% @checkedDivU8_exact) ∧
    (type_of% @checkedIndex_totalExact) ∧
    (type_of% @checkedIndex_exact) ∧
    (type_of% @checkedAddU8_verificationResult) ∧
    (type_of% @checkedAddU8_neverPanics_inRange) ∧
    (type_of% @checkedAddU8_not_neverPanics) ∧
    (type_of% @checkedAddU8_callee_wp) ∧
    (type_of% @checkedAddU8_holdsTotallyOn) ∧
    (type_of% @checkedAddU8_holdsOn) ∧
    (type_of% @addCaller_unwinding_wp) ∧
    (type_of% @addCaller_modular_panicsOnlyIf) ∧
    (type_of% @checkedAddU8_closedCallee_panicsOnlyIf) ∧
    (type_of% @addCaller_linked_panicsOnlyIf) ∧
    (type_of% @addCaller_linked_totalExact) ∧
    (type_of% @addCaller_terminate_wp) ∧
    (type_of% @addCaller_terminate_linked_totalExact) ∧
    (type_of% @addCaller_terminate_linked_exactPanicAbort) ∧
    (type_of% @checkedAddTerminate_wp) ∧
    (type_of% @checkedAddUnwindTerminate_wp) ∧
    (type_of% @nounwindGuard_wp) ∧
    (type_of% @checkedAddTerminate_totalExact) ∧
    (type_of% @checkedAddTerminate_exactPanicAbort) ∧
    (type_of% @checkedAddUnwindTerminate_totalExact) ∧
    (type_of% @checkedAddUnwindTerminate_exactPanicAbort) ∧
    (type_of% @nounwindGuard_totalExact) ∧
    (type_of% @nounwindGuard_exactPanicAbort) ∧
    (type_of% @checkedAddTerminate_never_panics) ∧
    (type_of% @overflowingArgs_pre) ∧
    (type_of% @checkedAddUnreachable_not_panicsWithPolicyOnlyIf) ∧
    (type_of% @checkedAddUnreachable_not_panicsOnlyIf_true) ∧
    (type_of% @checkedAddUbCleanup_not_panicsWithPolicyOnlyIf) ∧
    (type_of% @checkedAddUbCleanup_not_panicsOnlyIf_true) ∧
    (type_of% @checkedAddUnreachable_neverPanics_inRange) ∧
    (type_of% @checkedAddU8_panicsOnlyIf_true) ∧
    (type_of% @zeroArgs_pre) ∧
    (type_of% @checkedAddU8_not_panicsIf_true) ∧
    (type_of% @checkedAddU8_not_exact_true) ∧
    (type_of% @wrappingAddU8_neverPanics) ∧
    (type_of% @wrappingAddU8_not_panicsIf) ∧
    (type_of% @wrappingAddU8_not_exact) ∧
    (type_of% @wrappingAddU8_panicsOnlyIf) ∧
    (type_of% @reactiveLoopTree_trap) ∧
    (type_of% @reactiveSwitchLoopMir_step) ∧
    (type_of% @reactiveSwitchLoopMir_trap) ∧
    (type_of% @reactiveSwitchLoopMir_neverPanics) ∧
    (type_of% @addCaller_callBoundaryPreserved) ∧
    (type_of% @addCaller_calleeTableExcludes) ∧
    (type_of% @emptyMemory_calleeTableExcludes) ∧
    (type_of% @addCaller_call_emits_request) ∧
    (type_of% @addCallerInlined_not_callBoundaryPreserved) ∧
    (type_of% @addCallerInlined_not_bodyCallsDefPath) ∧
    (type_of% @addCallerInlined_totalExact) ∧
    (type_of% @addCallerInlinedDeadCall_callBoundaryPreserved) ∧
    (type_of% @addCallerInlinedDeadCall_never_calls) ∧
    (type_of% @addCaller_calls) ∧
    (type_of% @linkedMem_calleeTableExcludes) ∧
    (type_of% @twoCall_first_call_emits_request) ∧
    (type_of% @injectedMem_callFramePreserved) ∧
    (type_of% @helper_withFramePreserved_accepts_injection) ∧
    (type_of% @injectedMem_lookupCallee) ∧
    (type_of% @injectedMem_not_calleeTableExcludes) ∧
    (type_of% @twoCall_resume_injected) ∧
    (type_of% @twoCall_injected_second_call_inlined) ∧
    (type_of% @helper_withTraitsPreserved_rejects_injection) ∧
    (type_of% @twoCall_guard_preserved) ∧
    (type_of% @twoCall_second_call_emits_request) ∧
    (type_of% @alwaysAbort_totalExact) ∧
    (type_of% @alwaysAbort_reaches_abort) ∧
    (type_of% @alwaysAbort_waiveAbortUnchecked) ∧
    (type_of% @alwaysAbort_not_forbidAbort) ∧
    (type_of% @alwaysAbort_not_panicsOnlyIf) ∧
    (type_of% @alwaysAbort_abortOnlyIf_iff) ∧
    (type_of% @checkedAddU8_not_exactPolicy_waiveAbortUnchecked) ∧
    (type_of% @kani5202_binop_offset_zst_scalar_ptr) ∧
    (type_of% @kani5202_binop_offset_u8_scalar_ptr) ∧
    (type_of% @kani5202_arith_offset_scalar_ptr_ub) ∧
    (type_of% @kani5202_ptrAllocByteBound_probes) ∧
    (type_of% @kani5202_binop_offset_dangling_ptr) ∧
    (type_of% @kani5202_arith_offset_dangling_ptr) ∧
    (type_of% @kani5219_tyProjTouchesUnion_probes) ∧
    (type_of% @kani5219_element_and_subslice_reads) ∧
    (type_of% @kani5219_union_field_reads) ∧
    (type_of% @kani5219_len_probes) ∧
    (type_of% @kani5219_resolveProjectedTy_subslice) ∧
    (type_of% @kani5219_borrow_backed_slice_contagion) ∧
    (type_of% @poison_holdsTotallyOn) ∧
    (type_of% @poison_linked_answer) ∧
    (type_of% @rollback_modular_totalExact) ∧
    (type_of% @rollback_inlined_not_treeSafe) ∧
    (type_of% @outcomeToCallAns_prePanic_mutation_rollback_divergence) ∧
    (type_of% @tailUnprotectedMem_calleeTableExcludes) ∧
    (type_of% @tailCall_emits_request_after_teardown) ∧
    (type_of% @tailCall_protectorConflict_ub) ∧
    (type_of% @tailCall_step_probes) :=
  ⟨@checkedAddU8_wp,
    @checkedAddU32_wp,
    @checkedDivU8_wp,
    @checkedIndex_wp,
    @checkedAddU8_totalExact,
    @checkedAddU8_exact,
    @checkedAddU32_totalExact,
    @checkedAddU32_exact,
    @checkedAddU8_dichotomy,
    @checkedDivU8_totalExact,
    @checkedDivU8_exact,
    @checkedIndex_totalExact,
    @checkedIndex_exact,
    @checkedAddU8_verificationResult,
    @checkedAddU8_neverPanics_inRange,
    @checkedAddU8_not_neverPanics,
    @checkedAddU8_callee_wp,
    @checkedAddU8_holdsTotallyOn,
    @checkedAddU8_holdsOn,
    @addCaller_unwinding_wp,
    @addCaller_modular_panicsOnlyIf,
    @checkedAddU8_closedCallee_panicsOnlyIf,
    @addCaller_linked_panicsOnlyIf,
    @addCaller_linked_totalExact,
    @addCaller_terminate_wp,
    @addCaller_terminate_linked_totalExact,
    @addCaller_terminate_linked_exactPanicAbort,
    @checkedAddTerminate_wp,
    @checkedAddUnwindTerminate_wp,
    @nounwindGuard_wp,
    @checkedAddTerminate_totalExact,
    @checkedAddTerminate_exactPanicAbort,
    @checkedAddUnwindTerminate_totalExact,
    @checkedAddUnwindTerminate_exactPanicAbort,
    @nounwindGuard_totalExact,
    @nounwindGuard_exactPanicAbort,
    @checkedAddTerminate_never_panics,
    @overflowingArgs_pre,
    @checkedAddUnreachable_not_panicsWithPolicyOnlyIf,
    @checkedAddUnreachable_not_panicsOnlyIf_true,
    @checkedAddUbCleanup_not_panicsWithPolicyOnlyIf,
    @checkedAddUbCleanup_not_panicsOnlyIf_true,
    @checkedAddUnreachable_neverPanics_inRange,
    @checkedAddU8_panicsOnlyIf_true,
    @zeroArgs_pre,
    @checkedAddU8_not_panicsIf_true,
    @checkedAddU8_not_exact_true,
    @wrappingAddU8_neverPanics,
    @wrappingAddU8_not_panicsIf,
    @wrappingAddU8_not_exact,
    @wrappingAddU8_panicsOnlyIf,
    @reactiveLoopTree_trap,
    @reactiveSwitchLoopMir_step,
    @reactiveSwitchLoopMir_trap,
    @reactiveSwitchLoopMir_neverPanics,
    @addCaller_callBoundaryPreserved,
    @addCaller_calleeTableExcludes,
    @emptyMemory_calleeTableExcludes,
    @addCaller_call_emits_request,
    @addCallerInlined_not_callBoundaryPreserved,
    @addCallerInlined_not_bodyCallsDefPath,
    @addCallerInlined_totalExact,
    @addCallerInlinedDeadCall_callBoundaryPreserved,
    @addCallerInlinedDeadCall_never_calls,
    @addCaller_calls,
    @linkedMem_calleeTableExcludes,
    @twoCall_first_call_emits_request,
    @injectedMem_callFramePreserved,
    @helper_withFramePreserved_accepts_injection,
    @injectedMem_lookupCallee,
    @injectedMem_not_calleeTableExcludes,
    @twoCall_resume_injected,
    @twoCall_injected_second_call_inlined,
    @helper_withTraitsPreserved_rejects_injection,
    @twoCall_guard_preserved,
    @twoCall_second_call_emits_request,
    @alwaysAbort_totalExact,
    @alwaysAbort_reaches_abort,
    @alwaysAbort_waiveAbortUnchecked,
    @alwaysAbort_not_forbidAbort,
    @alwaysAbort_not_panicsOnlyIf,
    @alwaysAbort_abortOnlyIf_iff,
    @checkedAddU8_not_exactPolicy_waiveAbortUnchecked,
    @kani5202_binop_offset_zst_scalar_ptr,
    @kani5202_binop_offset_u8_scalar_ptr,
    @kani5202_arith_offset_scalar_ptr_ub,
    @kani5202_ptrAllocByteBound_probes,
    @kani5202_binop_offset_dangling_ptr,
    @kani5202_arith_offset_dangling_ptr,
    @kani5219_tyProjTouchesUnion_probes,
    @kani5219_element_and_subslice_reads,
    @kani5219_union_field_reads,
    @kani5219_len_probes,
    @kani5219_resolveProjectedTy_subslice,
    @kani5219_borrow_backed_slice_contagion,
    @poison_holdsTotallyOn,
    @poison_linked_answer,
    @rollback_modular_totalExact,
    @rollback_inlined_not_treeSafe,
    @outcomeToCallAns_prePanic_mutation_rollback_divergence,
    @tailUnprotectedMem_calleeTableExcludes,
    @tailCall_emits_request_after_teardown,
    @tailCall_protectorConflict_ub,
    @tailCall_step_probes⟩

/--
info: 'Anneal.PanicContractsTests.all_panic_contracts_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms all_panic_contracts_tests

end Anneal.PanicContractsTests
