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

/--
Both sides of the dichotomy are inhabited on concrete inputs: `(255, 1)` reaches
`.panic` and `(1, 2)` returns `3`, so neither trigger of the exact contract is
vacuous.
-/
theorem checkedAddU8_ground_witnesses :
    (∃ tr, ReachesRet (mirTrees checkedAddU8Mir [] (scalarArgs2 1 255 1)) tr .panic) ∧
      (∃ tr mem, ReachesRet (mirTrees checkedAddU8Mir [] (scalarArgs2 1 1 2)) tr
        (.normal (.scalar { bits := 3, sizeBytes := 1 }, mem))) := by
  refine ⟨checkedAddU8_exact.2 _ ⟨255, 1, by decide, by decide, rfl⟩
    (show (256 : Nat) ≤ 255 + 1 by decide), ?_⟩
  obtain ⟨tr, r, hr⟩ := checkedAddU8_totalExact.returnsIf (scalarArgs2 1 1 2)
    ⟨1, 2, by decide, by decide, rfl⟩ (show ¬ ((256 : Nat) ≤ 1 + 2) by decide)
  have hPost := checkedAddU8_exact.1.post_of_returns ⟨1, 2, by decide, by decide, rfl⟩ hr
  obtain ⟨v, mem⟩ := r
  cases (show v = .scalar { bits := 3, sizeBytes := 1 } from hPost)
  exact ⟨tr, mem, hr⟩

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
  calleeTableExcludes_of_callees_nil rfl

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

/-! ### Partial inlining and call-site counts -/

/--
`fn two_sites(a: u8, b: u8) -> u8 { checked_add_u8(checked_add_u8(a, b), b) }`:
`bb0: _3 = checked_add_u8(copy _1, copy _2) -> bb1`,
`bb1: _0 = checked_add_u8(copy _3, copy _2) -> bb2`, `bb2: return`.
-/
def twoSiteCallerMir : CapturedMir :=
  mkBody "panic_tests::two_sites" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 3) (.some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 3), .copy (local_ 2)]
            (local_ 0) (.some 2) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- The same caller after pre-capture inlining of its first call only. -/
def twoSiteHalfInlinedMir : CapturedMir :=
  mkBody "panic_tests::two_sites" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut u8Ty
    , mkDecl .mut u8CheckedTy ]
    [ { statements :=
          [ mkStmt (.storageLive 4)
          , mkStmt (.assign (local_ 4)
              (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 4, projection := [.field 1 boolTy] }) false 1 .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 3)
              (.use (.move { local_ := 4, projection := [.field 0 u8Ty] }))) ]
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 3), .copy (local_ 2)]
            (local_ 0) (.some 2) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- Both call sites survive in the captured caller. -/
theorem twoSiteCaller_callSitesPreserved :
    CallSitesPreserved twoSiteCallerMir [] checkedAddU8Path 2 :=
  (callSitesPreserved_iff _ _ _ _).1 rfl

/--
`CallBoundaryPreserved` accepts the half-inlined caller: the one remaining call
site is all it asks for.
-/
theorem twoSiteHalfInlined_callBoundaryPreserved :
    CallBoundaryPreserved twoSiteHalfInlinedMir [] checkedAddU8Path :=
  (callBoundaryPreserved_iff _ _ _).1 rfl

/-- The counted guard rejects the half-inlined caller: one of the two call sites is gone. -/
theorem twoSiteHalfInlined_not_callSitesPreserved :
    ¬ CallSitesPreserved twoSiteHalfInlinedMir [] checkedAddU8Path 2 :=
  have hCount : bodyCallSiteCount checkedAddU8Path twoSiteHalfInlinedMir = 1 := rfl
  not_callSitesPreserved_of_count_ne (fun h => absurd (hCount.symm.trans h) (by decide))

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

/--
Contract of both callees of `two_calls`: each returns `0` and leaves `borrows`
completely unconstrained (handlers may mint fresh borrows or modify borrows
arbitrarily). It carries no frame condition of its own.
-/
def twoCallContract : PanicMirCallContract where
  pre req := req.defPath = helperPath ∨ req.defPath = contractedPath
  post _ retVal _ := retVal = .scalar { bits := 0, sizeBytes := 1 }

/--
A handler that answers every request at once and registers `injectedImpl` in the
memory it hands back.
-/
def injectingHandler : ExternalCallHandler := fun req =>
  pure (.returned (.scalar { bits := 0, sizeBytes := 1 })
    { req.memory with traitImpls := [injectedImpl] })

/-- The injecting handler implements the contract strengthened with `callFramePreserved` only. -/
theorem injectingHandler_holdsOn_withFramePreserved :
    twoCallContract.withFramePreserved.toMirCallContract.holdsOn injectingHandler :=
  holdsOn_pure_handler _ _ (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, [], rfl⟩)

/--
End-to-end refutation without trait preservation: against the frame-preserving
contract alone, no rely–guarantee panic contract of the two-call caller holds,
whatever `post`, `panicCond`, and `policy` are. The injecting handler satisfies
the rely, its first answer redirects the second call into `evilImplMir`, and the
linked execution reaches undefined behavior.
-/
theorem twoCall_frameOnly_not_modular (post : MirInput → MirReturn → Prop)
    (panicCond : MirInput → Prop) (policy : AbortPolicy MirInput) :
    ¬ MirModularPanicsWithPolicyOnlyIf twoCallCallerMir
        twoCallContract.withFramePreserved.toMirCallContract.holdsOn
        (fun x => x = ([], linkedMem)) post panicCond policy :=
  not_mirModularPanicsWithPolicyOnlyIf_of_reachesLinkedFault
    injectingHandler_holdsOn_withFramePreserved rfl
    (.call rfl (reachesRet_pure_handler _) (.of_reachesFaultExecBounded _ 8 rfl))

private theorem twoCall_traitsPreserved_wp :
    wpMirModularSym twoCallContract.withTraitsPreserved.toMirCallContract 8
      twoCallCallerMir twoCallInit
      (fun out => ∃ r, out = .normal r ∧ r.1 = .scalar { bits := 0, sizeBytes := 1 }) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  refine ⟨Or.inl rfl, fun ans hPost => ?_⟩
  cases ans with
  | returned retVal memAfter =>
    obtain ⟨hVal, ⟨hC, hCS, hAC, hAP, -⟩, hT⟩ := hPost
    subst hVal
    cases memAfter with
    | mk nextAllocId globals borrows nextTag callees traitImpls callStack activeCallee
        activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
      simp only at hC hCS hAC hAP hT
      subst hC hCS hAC hAP hT
      cases borrows <;> (
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        refine ⟨Or.inr rfl, fun ans2 hPost2 => ?_⟩
        cases ans2 with
        | returned retVal2 memAfter2 =>
          obtain ⟨hVal2, ⟨hC2, hCS2, hAC2, hAP2, -⟩, hT2⟩ := hPost2
          subst hVal2
          cases memAfter2 with
          | mk nextAllocId2 globals2 borrows2 nextTag2 callees2 traitImpls2 callStack2
              activeCallee2 activeProtectors2 nextProtector2 callerLocals2 fnPtrs2
              exposedAllocIds2 =>
            simp only at hC2 hCS2 hAC2 hAP2 hT2
            subst hC2 hCS2 hAC2 hAP2 hT2
            cases borrows2 <;> (
              (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
              exact ⟨_, rfl, rfl⟩)
        | panicked memAfter2 => exact False.elim hPost2.1
        | aborted => exact False.elim hPost2)
  | panicked memAfter => exact False.elim hPost.1
  | aborted => exact False.elim hPost

/--
End-to-end verification with trait preservation: against every handler that
implements the contract strengthened with `withTraitsPreserved`, the two-call
caller is fault-free, never panics, and returns `0`. Both answers carry
completely arbitrary `borrows` (including fresh borrows), and the second call
still leaves the machine as a request.
-/
theorem twoCall_traitsPreserved_modular_neverPanics :
    MirModularNeverPanics twoCallCallerMir
      twoCallContract.withTraitsPreserved.toMirCallContract.holdsOn
      (fun x => x = ([], linkedMem))
      (fun _ r => r.1 = .scalar { bits := 0, sizeBytes := 1 }) :=
  mirModularNeverPanics_of_wpMirModularSym _ 8 (by
    rintro _ rfl
    exact twoCall_traitsPreserved_wp)

/--
`handlerPreservesTables_of_withTraitsPreserved` asks the contract's
precondition to hold of every request. That is false for `twoCallContract`, as
for every contract that names its callees.
-/
theorem twoCallContract_pre_not_universal : ¬ ∀ req, twoCallContract.pre req := fun h =>
  match h { defPath := "", typeArgs := [], args := [], memory := emptyMemory } with
  | .inl hEq => nomatch hEq
  | .inr hEq => nomatch hEq

/--
The relativized guard needs no such condition: against every handler that
implements the `withTraitsPreserved` contract, every state reachable through
calls in the contract's precondition keeps the contracted callee excluded.
-/
theorem twoCall_reachableOn_guard (h : ExternalCallHandler)
    (hHolds : twoCallContract.withTraitsPreserved.toMirCallContract.holdsOn h)
    (s' : MachineState)
    (hReach : ReachableExecStateOn twoCallCallerMir h twoCallContract.pre
      (.running twoCallInit) (.running s')) :
    CalleeTableExcludes s'.memory contractedPath :=
  ReachableExecStateOn.calleeTableExcludes_of_withTraitsPreserved twoCallContract .forbidAbort
    hHolds hReach linkedMem_calleeTableExcludes

/--
Automatic unconstrained runtime guard from the modular proof: no manual
`ReachableExecStateOn` assumption and no universal `∀ req, P.pre req` condition
are needed. Every running state `s'` reachable under **any** handler
implementing `twoCallContract.withTraitsPreserved` preserves `CalleeTableExcludes`.
-/
theorem twoCall_reachable_guard_of_modular_proof (h : ExternalCallHandler)
    (hHolds : twoCallContract.withTraitsPreserved.toMirCallContract.holdsOn h)
    (s' : MachineState)
    (hReach : ReachableExecState twoCallCallerMir h (.running twoCallInit) (.running s')) :
    CalleeTableExcludes s'.memory contractedPath :=
  hReach.calleeTableExcludes_of_wpMirModularSym_withTraitsPreserved
    twoCallContract .forbidAbort hHolds twoCall_traitsPreserved_wp
    linkedMem_calleeTableExcludes

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
  calleeTableExcludes_of_callees_nil rfl

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

/--
Unlike `TerminatorKind.call`, `TerminatorKind.tailCall` performs no inline
intrinsic or panic-entrypoint intercept: targeting `panic_nounwind` or
`core::intrinsics::exact_div` still emits `MirCallE` after frame teardown.
-/
theorem tailCall_no_inline_intercept_panic_and_exactDiv :
    evalTerminator (initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
        (mkTerm (.tailCall (fnItemOp "core::panicking::panic_nounwind") [.copy (local_ 1)]))
        (.some tailCallerMir) =
      MirStepNode.extCall
        { defPath := "core::panicking::panic_nounwind", typeArgs := [], args := tailArgs
          memory :=
            { tailUnprotectedMem with borrows := [probeBorrow 1 1 .disabled true] } }
        resumeExternalTailCall ∧
      evalTerminator (initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
        (mkTerm (.tailCall (fnItemOp "core::intrinsics::exact_div") [.copy (local_ 1)]))
        (.some tailCallerMir) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::exact_div", typeArgs := [], args := tailArgs
          memory :=
            { tailUnprotectedMem with borrows := [probeBorrow 1 1 .disabled true] } }
        resumeExternalTailCall :=
  ⟨evalTerminator_tailCall_extCall_of_call_site
      (s := initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
      (func := fnItemOp "core::panicking::panic_nounwind") (argOps := [.copy (local_ 1)])
      (targetDefPath := "core::panicking::panic_nounwind") (argVals := tailArgs)
      rfl rfl rfl rfl (calleeTableExcludes_of_callees_nil rfl),
   evalTerminator_tailCall_extCall_of_call_site
      (s := initMachineStateWithMemory tailCallerMir tailArgs tailUnprotectedMem)
      (func := fnItemOp "core::intrinsics::exact_div") (argOps := [.copy (local_ 1)])
      (targetDefPath := "core::intrinsics::exact_div") (argVals := tailArgs)
      rfl rfl rfl rfl (calleeTableExcludes_of_callees_nil rfl)⟩

/-- Root-frame tail-call resumption for normal return, panic, and abort answers. -/
theorem tailCall_resume_outcomes (retVal : Value) :
    resumeExternalTailCall (.returned retVal emptyMemory) =
        .halted (.normal (retVal, emptyMemory)) ∧
      resumeExternalTailCall (.panicked emptyMemory) = .halted .panic ∧
      resumeExternalTailCall .aborted = .halted .abort :=
  ⟨resumeExternalTailCall_returned_root emptyMemory retVal rfl,
   resumeExternalTailCall_panicked_root emptyMemory rfl,
   resumeExternalTailCall_aborted⟩

/-! ## 6b. Hardening & Extended Coverage (General Memory, Call Boundaries, Pass Variance, Parity) -/

/-! ### General-memory caller–callee composition & contract-level exact composition -/

/--
General-memory precondition for composition: arbitrary `nextAllocId`, `globals`,
`nextTag`, `traitImpls`, `nextProtector`, `callerLocals`, `fnPtrs`, and
`exposedAllocIds`, with empty borrows/callStack/callees/protectors and no
pre-active callee.
-/
def generalMemPre (x : MirInput) : Prop :=
  scalarPre2 1 x.1 ∧
    x.2.borrows = .nil ∧
    x.2.callees = .nil ∧
    x.2.callStack = .nil ∧
    x.2.activeCallee = .none ∧
    x.2.activeProtectors = .nil

/-- General-memory panic call contract for `checked_add_u8` (not pinned to `emptyMemory`). -/
def checkedAddU8GeneralContract : PanicMirCallContract where
  pre req :=
    req.defPath = checkedAddU8Path ∧
      scalarPre2 1 req.args ∧
      req.memory.borrows = .nil ∧
      req.memory.callStack = .nil ∧
      req.memory.activeCallee = .none ∧
      req.memory.activeProtectors = .nil
  post req retVal memAfter :=
    retVal = .scalar { bits := argSum req.args, sizeBytes := 1 } ∧
      ¬ overflows 1 req.args ∧ memAfter = req.memory
  panicCond req := overflows 1 req.args
  panicMemInv req memAfter := memAfter = req.memory

def checkedAddU8GeneralMirContract : MirCallContract :=
  checkedAddU8GeneralContract.withTraitsPreserved.toMirCallContract

theorem checkedAddU8_generalMem_callee_wp (typeArgs : List RigidTy) (a b : Nat)
    (mem : Memory) (hB : mem.borrows = .nil) (hCS : mem.callStack = .nil)
    (hAC : mem.activeCallee = .none) (hAP : mem.activeProtectors = .nil) :
    wpMirNoCallSym 8 checkedAddU8Mir
      (initMachineStateWithMemory checkedAddU8Mir (scalarArgs2 1 a b) mem)
      (fun out =>
        checkedAddU8GeneralMirContract.post
          { defPath := checkedAddU8Path, typeArgs := typeArgs, args := scalarArgs2 1 a b,
            memory := mem }
          (outcomeToCallAns mem out)) := by
  cases mem with
  | mk nextAllocId globals borrows nextTag callees callStack activeCallee traitImpls
      activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
    simp only at hB hCS hAC hAP
    subst hB hCS hAC hAP
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq
      exact ⟨(nat_ble_eq_true_iff _ _).1 heq, rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
    · rename_i heq
      have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
      exact ⟨⟨congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
          (wrapScalarBits_of_lt hlt), Nat.not_le.2 hlt, rfl⟩,
        ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩

/-- `checked_add_u8` implements its general-memory trait-preserving contract totally. -/
theorem checkedAddU8_generalMem_holdsTotallyOn (fallback : ExternalCallHandler) :
    checkedAddU8GeneralMirContract.holdsTotallyOn (linkCalleeHandler checkedAddU8Mir fallback) :=
  holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallSym checkedAddU8GeneralMirContract
    checkedAddU8Mir fallback 8 (fun _ h => h.1) (by
      rintro ⟨_, typeArgs, _, mem⟩ ⟨rfl, ⟨a, b, -, -, rfl⟩, hB, hCS, hAC, hAP⟩
      exact checkedAddU8_generalMem_callee_wp typeArgs a b mem hB hCS hAC hAP)

/--
General-memory modular caller verification: symbolic over arbitrary caller
`globals`, `callerLocals`, `traitImpls`, `fnPtrs`, and counters.
-/
theorem addCaller_generalMem_unwinding_wp (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2) (a b : Nat)
    (ha : a < 256) (hb : b < 256) (mem : Memory)
    (hB : mem.borrows = .nil) (hC : mem.callees = .nil) (hCS : mem.callStack = .nil)
    (hAC : mem.activeCallee = .none) (hAP : mem.activeProtectors = .nil) :
    wpMirModularSym checkedAddU8GeneralMirContract 8 (addCallerMir unwind)
      (initMachineStateWithMemoryAndCallees (addCallerMir unwind) (scalarArgs2 1 a b)
        mem [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 })
        (256 ≤ a + b)) := by
  cases mem with
  | mk nextAllocId globals borrows nextTag callees callStack activeCallee traitImpls
      activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
    simp only at hB hC hCS hAC hAP
    subst hB hC hCS hAC hAP
    rcases hUnwind with rfl | rfl <;>
    · (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩, rfl, rfl, rfl, rfl⟩, fun ans hPost => ?_⟩
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

/--
General-memory exact horizontal composition: works across arbitrary `globals`,
`callerLocals`, `traitImpls`, and `fnPtrs`, without pinning `emptyMemory`.
-/
theorem addCaller_generalMem_linked_totalExact (unwind : UnwindAction)
    (hUnwind : unwind = .continue_ ∨ unwind = .cleanup 2)
    (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees (addCallerMir unwind) (linkCalleeHandler checkedAddU8Mir fallback))
      generalMemPre addCallerPost addCallerOverflows :=
  mirHandled_totalExactPanicContract_of_wpMirModularSym checkedAddU8GeneralMirContract
    (checkedAddU8_generalMem_holdsTotallyOn fallback) 8 (by
      rintro ⟨_, mem⟩ ⟨⟨a, b, ha, hb, rfl⟩, hB, hC, hCS, hAC, hAP⟩
      exact addCaller_generalMem_unwinding_wp unwind hUnwind a b ha hb mem hB hC hCS hAC hAP)

/--
Frame-general panic call contract for `checked_add_u8`: the request memory may
carry any `callees`, `traitImpls`, `callStack`, `activeCallee`, and
`activeProtectors`. Only `borrows` is pinned, so that the callee's frame
teardown reduces symbolically.
-/
def checkedAddU8FrameGeneralContract : PanicMirCallContract where
  pre req :=
    req.defPath = checkedAddU8Path ∧ scalarPre2 1 req.args ∧ req.memory.borrows = .nil
  post req retVal memAfter :=
    retVal = .scalar { bits := argSum req.args, sizeBytes := 1 } ∧
      ¬ overflows 1 req.args ∧ memAfter = req.memory
  panicCond req := overflows 1 req.args
  panicMemInv req memAfter := memAfter = req.memory

def checkedAddU8FrameGeneralMirContract : MirCallContract :=
  checkedAddU8FrameGeneralContract.withTraitsPreserved.toMirCallContract

/--
The isolated callee (`enterExternalCalleeState`) meets the frame-general
contract on the frame-restored answer (`outcomeToRestoredCallAns`), for an
arbitrary caller call frame.
-/
theorem checkedAddU8_frameGeneral_callee_wp (typeArgs : List RigidTy) (a b : Nat)
    (mem : Memory) (hB : mem.borrows = .nil) :
    wpMirNoCallSym 8 checkedAddU8Mir
      (enterExternalCalleeState checkedAddU8Mir (scalarArgs2 1 a b) mem [])
      (fun out =>
        checkedAddU8FrameGeneralMirContract.post
          { defPath := checkedAddU8Path, typeArgs := typeArgs, args := scalarArgs2 1 a b,
            memory := mem }
          (outcomeToRestoredCallAns mem out)) := by
  cases mem with
  | mk nextAllocId globals borrows nextTag callees callStack activeCallee traitImpls
      activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
    simp only at hB
    subst hB
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq
      exact ⟨(nat_ble_eq_true_iff _ _).1 heq, rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
    · rename_i heq
      have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
      exact ⟨⟨congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
          (wrapScalarBits_of_lt hlt), Nat.not_le.2 hlt, rfl⟩,
        ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩

/--
`checked_add_u8` linked through the frame-restoring
`linkCalleeWithCalleesHandler` implements the frame-general contract totally:
the request may come from a nested frame of a caller with linked callees.
-/
theorem checkedAddU8_frameGeneral_holdsTotallyOn (fallback : ExternalCallHandler) :
    checkedAddU8FrameGeneralMirContract.holdsTotallyOn
      (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) :=
  holdsTotallyOn_linkCalleeWithCalleesHandler_of_wpMirNoCallSym
    checkedAddU8FrameGeneralMirContract checkedAddU8Mir [] fallback 8 (fun _ h => h.1) (by
      rintro ⟨_, typeArgs, _, mem⟩ ⟨rfl, ⟨a, b, -, -, rfl⟩, hB⟩
      exact checkedAddU8_frameGeneral_callee_wp typeArgs a b mem hB)

/--
Contract-level total-exact composition exercising
`totalExactPolicyPanicContract_call_compose_of_callee_contract`: composes a
caller directly against a callee's `TotalExactPolicyPanicContract` on its closed
trees rather than raw `DWP mirNoCallWP`.
-/
theorem checkedAddU8_closedCallee_totalExactPolicy :
    TotalExactPolicyPanicContract (mirClosedCalleeTrees checkedAddU8Mir)
      (fun req =>
        checkedAddU8Contract.withTraitsPreserved.pre req ∧
          req.defPath = checkedAddU8Mir.defPath)
      (fun req r => checkedAddU8Contract.withTraitsPreserved.post req r.1 r.2)
      checkedAddU8Contract.withTraitsPreserved.panicCond .forbidAbort :=
  totalExactPolicyPanicContract_of_dwp (ewp := mirClosedWP)
    mirClosedEffect_nonFault_nonempty (by
      rintro ⟨_, typeArgs, _, _⟩ ⟨⟨rfl, ⟨a, b, -, -, rfl⟩, rfl⟩, -⟩
      refine dwp_interp failUnlinkedCalls
        (fun i Q u hwp => by
          cases i with
          | inl _ => exact False.elim hwp
          | inr i' =>
            cases i' with
            | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
            | inr _ => exact False.elim hwp)
        (DWP.mono (fun out _ h => ?_)
          (dwp_of_wpMirNoCallSym (checkedAddU8_callee_wp typeArgs a b)))
      cases out with
      | normal r => exact ⟨h.1.2.1, fun ha => ha, h⟩
      | panic => exact ⟨h.1, fun ha => ha⟩
      | abort => exact False.elim h)

theorem addCaller_linked_totalExact_via_callee_contract (fallback : ExternalCallHandler) :
    TotalExactPolicyPanicContract
      (mirHandledTrees (addCallerMir .continue_) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre addCallerPost addCallerOverflows .forbidAbort :=
  totalExactPolicyPanicContract_call_compose_of_callee_contract
    checkedAddU8Contract.withTraitsPreserved .forbidAbort
    (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      refine DWP.mono
        (fun out _ h => (exactPolicyOutcome_forbidAbort_iff _ _ _ out).2 h)
        (dwp_of_wpMirModularSym (C := checkedAddU8Contract.withTraitsPreserved.toExactPolicyMirCallContract .forbidAbort) (fuel := 8) ?_)
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩, rfl⟩, fun ans hPost => ?_⟩
      cases ans with
      | returned retVal memAfter =>
        obtain ⟨_, _, ⟨hVal, hFit, hMem⟩, _⟩ := hPost
        subst hVal hMem
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        exact ⟨hFit, rfl⟩
      | panicked memAfter =>
        obtain ⟨⟨hOver, _⟩, hMem, _⟩ := hPost
        subst hMem
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        exact hOver
      | aborted => exact False.elim hPost.1)
    (fun _ _ _ _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩)
    checkedAddU8_closedCallee_totalExactPolicy
    (fun _ hPre hNe => False.elim (hNe hPre.1))

/-! ### External-call `UnwindAction.unreachable` UB refutation & explicit panic entrypoints -/

/--
Undefined behavior on a call's unwind edge (`addCallerMir .unreachable` linked
with `checkedAddU8Mir`): on the overflowing input `(255, 1)` the callee unwinds
and `resumeExternalCall` with `UnwindAction.unreachable` faults with `.ub`. The
`ReachesLinkedFault` trace refutes every panic contract of the linked system,
whatever `post`, `panicCond`, and `policy` are.
-/
theorem addCallerUnreachable_linked_not_panicsWithPolicyOnlyIf
    (fallback : ExternalCallHandler)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    ¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees (addCallerMir .unreachable) (linkCalleeHandler checkedAddU8Mir fallback))
      addCallerPre post panicCond policy := by
  have hPre : addCallerPre (scalarArgs2 1 255 1, emptyMemory) := ⟨overflowingArgs_pre, rfl⟩
  have hTot := checkedAddU8_holdsTotallyOn fallback
    { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 255 1,
      memory := emptyMemory } ⟨rfl, overflowingArgs_pre, rfl⟩
  obtain ⟨tr, ans, hr, hPost⟩ :=
    exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hTot
  cases ans with
  | returned _ _ => exact False.elim (hPost.1.2.1 (by decide : (256 : Nat) ≤ 255 + 1))
  | panicked memAfter =>
    exact not_panicsWithPolicyOnlyIf_of_reachesLinkedFault hPre (.call rfl hr (.fail rfl))
  | aborted => exact False.elim hPost

/--
Explicit diverging call to `core::panicking::panic`:
`bb0: switchInt(copy _1) -> [0: bb1, otherwise: bb2]`,
`bb1: _2 = core::panicking::panic() -> unwind`, `bb2: _0 = copy _1; return`.
-/
def explicitPanicMir (unwind : UnwindAction) : CapturedMir :=
  mkBody "panic_tests::explicit_panic" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut neverTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1)], otherwise := 2 })
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic") [] (local_ 2) .none unwind)
        isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Direct diverging `core::panicking::panic` with `.continue_` satisfies `TotalExactPanicContract`. -/
theorem explicitPanic_continue_totalExact :
    TotalExactPanicContract (mirTrees (explicitPanicMir .continue_)) scalarPre1
      (fun args r => r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 })
      (fun args => argBits args 0 = 0) :=
  totalExactPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨x, -, rfl⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq; exact (nat_beq_eq_true_iff _ _).1 heq
    · rename_i heq; exact ⟨(nat_beq_eq_false_iff _ _).1 heq, rfl⟩)

/-- Direct diverging `core::panicking::panic` with `.terminate` aborts cleanly on `x = 0`. -/
theorem explicitPanic_terminate_totalExact :
    TotalExactPolicyPanicContract (mirTrees (explicitPanicMir .terminate)) scalarPre1
      (fun args r => r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 })
      (fun _ => False) (.abortOnlyIf (fun args => argBits args 0 = 0)) :=
  totalExactPolicyPanicContract_of_wpMirSym 8 (by
    rintro _ ⟨x, -, rfl⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq; exact ⟨(nat_beq_eq_true_iff _ _).1 heq, fun h => h⟩
    · rename_i heq; exact ⟨fun h => h, (nat_beq_eq_false_iff _ _).1 heq, rfl⟩)

/-- Direct diverging `core::panicking::panic` with `.unreachable` faults `.ub` on `x = 0`. -/
theorem explicitPanic_unreachable_not_panicsWithPolicyOnlyIf
    (post : List Value → MirReturn → Prop) (panicCond : List Value → Prop)
    (policy : AbortPolicy (List Value)) :
    ¬ PanicsWithPolicyOnlyIf (mirTrees (explicitPanicMir .unreachable)) scalarPre1
      post panicCond policy :=
  fun h =>
    reachesFaultBounded_not_treeSafe 8 (explicitPanicMir .unreachable)
      (initMachineStateWithCallees (explicitPanicMir .unreachable)
        [.scalar { bits := 0, sizeBytes := 1 }] []) rfl
      (h _ ⟨0, by decide, rfl⟩).1

/-! ### `TotalVerificationResult` vs `TotalExactPanicContract` separation -/

/--
`reactiveSwitchLoopMir` satisfies `Trusted.VerificationResult.TotalVerificationResult`
(it is `TreeSafe`, `Productive`, `¬ MayDiverge`, and has no `ReachesRet`), yet it
refutes `TotalExactPanicContract ... (fun _ => False)` because `TotalExactPanicContract`
demands a completed normal return (`ReturnsIf`).
-/
theorem reactiveSwitchLoopMir_totalVerificationResult_not_totalExact :
    TotalVerificationResult
        { body := reactiveSwitchLoopMir
          pre := fun args mem => args = [] ∧ mem = emptyMemory
          post := fun _ _ _ _ => False } ∧
      ¬ TotalExactPanicContract (mirStatefulTrees reactiveSwitchLoopMir)
        (fun x => x.1 = [] ∧ x.2 = emptyMemory) (fun _ _ => False) (fun _ => False) := by
  have hStep :
      stepMirState reactiveSwitchLoopMir
          (.running (initMachineStateWithMemoryAndCallees reactiveSwitchLoopMir [] emptyMemory [])) =
        .vis (.inr (.inl (.emit (.event 0))))
          (fun _ => .running
            (initMachineStateWithMemoryAndCallees reactiveSwitchLoopMir [] emptyMemory [])) :=
    rfl
  refine ⟨?_, ?_⟩
  · refine (totalVerificationResult_iff_neverPanics _).2 ⟨?_, ?_⟩
    · refine neverPanics_iff.2 ?_
      rintro ⟨_, _⟩ ⟨rfl, rfl⟩
      refine ⟨fun tr u hr hFault => ?_, fun tr out hr =>
        False.elim (not_reachesRet_cofix_selfLoop hStep tr out hr)⟩
      have hu := reaches_cofix_selfLoop hStep hr
      subst hu
      obtain ⟨u', i, k, hTau, hObs, hF⟩ := hFault
      have hu' := reaches_cofix_selfLoop hStep (Reaches.of_tauStar hTau (.refl u'))
      subst hu'
      rw [ITree.observe_cofix, hStep] at hObs
      injection hObs with hi _
      subst hi
      exact hF
    · rintro ⟨_, _⟩ ⟨rfl, rfl⟩
      exact ⟨productive_cofix_selfLoop hStep, not_mayDiverge_cofix_selfLoop hStep⟩
  · intro hTot
    obtain ⟨tr, r, hr⟩ := hTot.returnsIf ([], emptyMemory) ⟨rfl, rfl⟩ (fun h => h)
    exact not_reachesRet_cofix_selfLoop hStep tr (.normal r) hr

/-! ### `CalleesCallBoundaryPreserved`, stateful init boundary, and indirect/fn-item calls -/

def midHelperPath : DefPath := "panic_tests::mid_helper"

/-- Transitive helper that calls `checked_add_u8`. -/
def midHelperMir : CapturedMir :=
  mkBody midHelperPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- Inlined mutant of `midHelperMir` where `checked_add_u8` was erased. -/
def midHelperInlinedMir : CapturedMir :=
  checkedAddMir midHelperPath u8Ty u8CheckedTy .continue_

/-- Outer caller that calls `mid_helper` (not `checked_add_u8` directly). -/
def outerCallerMir : CapturedMir :=
  mkBody "panic_tests::outer_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp midHelperPath) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- Positive transitive guard: `midHelperMir` is linked, calls `checked_add_u8`, and `checked_add_u8` is unlinked. -/
theorem outerCaller_calleesCallBoundaryPreserved :
    CalleesCallBoundaryPreserved outerCallerMir [midHelperMir] [midHelperPath] checkedAddU8Path ∧
      (∀ args, CalleeTableExcludes
        (initMachineStateWithCallees outerCallerMir args [midHelperMir]).memory checkedAddU8Path) ∧
      (∀ args mem, CalleeTableExcludes
        (initMachineStateWithMemoryAndCallees outerCallerMir args mem [midHelperMir]).memory
        checkedAddU8Path) :=
  have hPres :
      CalleesCallBoundaryPreserved outerCallerMir [midHelperMir] [midHelperPath] checkedAddU8Path :=
    (calleesCallBoundaryPreserved_iff _ _ _ _).1 rfl
  ⟨hPres, fun args => hPres.calleeTableExcludes_init args,
   fun args mem => hPres.calleeTableExcludes_initStateful_of_ne_nil (by decide) args mem⟩

/-- Negative transitive guard cases: inlined helper, missing helper (non-vacuity), and linked target (soundness). -/
theorem outerCaller_calleesCallBoundaryPreserved_refutations :
    ¬ CalleesCallBoundaryPreserved outerCallerMir [midHelperInlinedMir] [midHelperPath]
        checkedAddU8Path ∧
      ¬ CalleesCallBoundaryPreserved outerCallerMir [] [midHelperPath] checkedAddU8Path ∧
      ¬ CalleesCallBoundaryPreserved outerCallerMir [midHelperMir, checkedAddU8Mir]
        [midHelperPath] checkedAddU8Path := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hCheck := (calleesCallBoundaryPreserved_iff _ _ _ _).2 h
    have hFalse :
        calleesCallBoundaryPreserved outerCallerMir [midHelperInlinedMir] [midHelperPath]
          checkedAddU8Path = false := rfl
    rw [hFalse] at hCheck; nomatch hCheck
  · exact not_calleesCallBoundaryPreserved_of_missing_caller
      (List.mem_singleton.2 rfl) (fun _ hMem => nomatch hMem)
  · exact not_calleesCallBoundaryPreserved_of_linked_target (targetBody := checkedAddU8Mir) rfl

/--
Boundary warning for `mirStatefulTrees ... []`: `CallBoundaryPreserved callerBody [] target`
holds, yet `initMachineStateWithMemoryAndCallees callerBody args mem []` keeps
pre-populated `mem.callees`, so `CalleeTableExcludes` fails if `target` is already
in `mem.callees`.
-/
theorem callBoundaryPreserved_emptyCallees_does_not_guard_prepopulated_mem :
    CallBoundaryPreserved (addCallerMir .continue_) [] checkedAddU8Path ∧
      ¬ CalleeTableExcludes
        (initMachineStateWithMemoryAndCallees (addCallerMir .continue_)
          (scalarArgs2 1 1 2) { emptyMemory with callees := [checkedAddU8Mir] } []).memory
        checkedAddU8Path := by
  refine ⟨addCaller_callBoundaryPreserved .continue_, ?_⟩
  intro h
  have hNone := h emptyLayoutTable []
  change lookupCallee [checkedAddU8Mir] emptyLayoutTable checkedAddU8Path [] [] = none at hNone
  have hSome :
      lookupCallee [checkedAddU8Mir] emptyLayoutTable checkedAddU8Path [] [] =
        .some checkedAddU8Mir := rfl
  rw [hSome] at hNone
  nomatch hNone

/-- End-to-end call-resumption guard preservation on `twoCallCallerMir`. -/
theorem twoCall_resumed_state_guard_preserved (retVal : Value) (memAfter : Memory)
    (nextState : MachineState)
    (hPost : helperContract.withTraitsPreserved.toMirCallContract.post helperReq
      (.returned retVal memAfter))
    (hRes : resumeExternalCall twoCallInit twoCallInit.frame.locals (local_ 0) 1 .continue_
      (.returned retVal memAfter) = .running nextState) :
    CalleeTableExcludes nextState.memory contractedPath :=
  CalleeTableExcludes.of_resumeExternalCall_withTraitsPreserved helperContract .forbidAbort
    hPost hRes linkedMem_calleeTableExcludes

def fnItemTy : Ty := { kind := .fnDef checkedAddU8Path [], layoutIdx := 0 }
def fnPtrSig : RigidTy := .fnPtr [.uint .u8, .uint .u8] (.uint .u8) .safe .rust
def fnPtrTy : Ty := { kind := fnPtrSig, layoutIdx := 0 }

def fnItemLocalMir : CapturedMir :=
  mkBody "panic_tests::fn_item_local_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .not fnItemTy ]
    [ { statements := []
        terminator :=
          mkTerm (.call (.copy (local_ 3)) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

def fnPtrCallerMir : CapturedMir :=
  mkBody "panic_tests::fn_ptr_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .not fnPtrTy ]
    [ { statements := []
        terminator :=
          mkTerm (.call (.move (local_ 3)) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

def fnPtrEntry : FnPtrEntry :=
  { allocId := 99, defPath := checkedAddU8Path, typeArgs := [], fnSig := .some fnPtrSig }

def fnPtrMem : Memory :=
  { emptyMemory with fnPtrs := [fnPtrEntry] }

/--
Runtime guard covers local ZST `fnDef` calls (both `.unit` and `.aggregate 0 []`)
and indirect `mem.fnPtrs` calls, even though the syntactic checker returns `false`
on `Operand.copy`/`Operand.move`.
-/
theorem indirect_and_fnItem_local_boundary_probes (a b : Nat) :
    let sUnit : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.scalar { bits := a, sizeBytes := 1 }),
                              .init (.scalar { bits := b, sizeBytes := 1 }), .init .unit] }
        memory := emptyMemory }
    let sAgg : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.scalar { bits := a, sizeBytes := 1 }),
                              .init (.scalar { bits := b, sizeBytes := 1 }),
                              .init (.aggregate 0 [])] }
        memory := emptyMemory }
    let sPtr : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.scalar { bits := a, sizeBytes := 1 }),
                              .init (.scalar { bits := b, sizeBytes := 1 }),
                              .init (.ptr { allocId := 99, offsetBytes := 0 } 8)] }
        memory := fnPtrMem }
    let termCopy :=
      mkTerm (.call (.copy (local_ 3)) [.copy (local_ 1), .copy (local_ 2)]
        (local_ 0) (.some 1) .continue_)
    let termMove :=
      mkTerm (.call (.move (local_ 3)) [.copy (local_ 1), .copy (local_ 2)]
        (local_ 0) (.some 1) .continue_)
    evalTerminator sUnit termCopy (.some fnItemLocalMir) =
        MirStepNode.extCall
          { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 a b,
            memory := emptyMemory }
          (resumeExternalCall sUnit sUnit.frame.locals (local_ 0) 1 .continue_) ∧
      evalTerminator sAgg termCopy (.some fnItemLocalMir) =
        MirStepNode.extCall
          { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 a b,
            memory := emptyMemory }
          (resumeExternalCall sAgg sAgg.frame.locals (local_ 0) 1 .continue_) ∧
      evalTerminator sPtr termMove (.some fnPtrCallerMir) =
        MirStepNode.extCall
          { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 a b,
            memory := fnPtrMem }
          (resumeExternalCall sPtr
            [.uninit, .init (.scalar { bits := a, sizeBytes := 1 }),
             .init (.scalar { bits := b, sizeBytes := 1 }), .uninit]
            (local_ 0) 1 .continue_) ∧
      terminatorCallsDefPath checkedAddU8Path termCopy = false ∧
      terminatorCallsDefPath checkedAddU8Path termMove = false := by
  intro sUnit sAgg sPtr termCopy termMove
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · exact evalTerminator_call_extCall_of_calleeTableExcludes
      (target := { defPath := checkedAddU8Path, typeArgs := [], fnSig := .none, isIndirect := false })
      rfl
      (resolveCallTarget_fnItem_local sUnit (.copy (local_ 3)) checkedAddU8Path [] 2
        fnItemLocalMir.localDecls fnItemLocalMir.layouts sUnit.frame.locals rfl rfl rfl)
      rfl emptyMemory_calleeTableExcludes rfl (Or.inr rfl)
  · exact evalTerminator_call_extCall_of_calleeTableExcludes
      (target := { defPath := checkedAddU8Path, typeArgs := [], fnSig := .none, isIndirect := false })
      rfl
      (resolveCallTarget_fnItem_local_aggregate sAgg (.copy (local_ 3)) checkedAddU8Path [] 2
        fnItemLocalMir.localDecls fnItemLocalMir.layouts sAgg.frame.locals rfl rfl rfl)
      rfl emptyMemory_calleeTableExcludes rfl (Or.inr rfl)
  · exact evalTerminator_call_extCall_of_calleeTableExcludes
      (target := { defPath := checkedAddU8Path, typeArgs := [], fnSig := .some fnPtrSig,
                   isIndirect := true })
      rfl
      (resolveCallTarget_fnPtr sPtr (.move (local_ 3)) 2 fnPtrCallerMir.localDecls
        fnPtrCallerMir.layouts { allocId := 99, offsetBytes := 0 } fnPtrEntry
        [.uninit, .init (.scalar { bits := a, sizeBytes := 1 }),
         .init (.scalar { bits := b, sizeBytes := 1 }), .uninit]
        rfl rfl rfl rfl rfl rfl)
      rfl (calleeTableExcludes_of_callees_nil rfl) rfl (Or.inl rfl)

/-! ### Transitive helper: frame-general contract through `linkCalleeWithCalleesHandler` -/

/--
Modular evaluation of `outerCallerMir` with `midHelperMir` linked in `callees`:
the outer call steps into the helper, and the helper's call to `checked_add_u8`
leaves the machine as a request from a nested frame (non-empty `callStack`,
`activeCallee := some midHelperMir`, `callees := [midHelperMir]`). The
frame-general contract applies there, and the callee's unwind propagates
through both frames.
-/
theorem outerCaller_wp (a b : Nat) (ha : a < 256) (hb : b < 256) :
    wpMirModularSym checkedAddU8FrameGeneralMirContract 16 outerCallerMir
      (initMachineStateWithMemoryAndCallees outerCallerMir (scalarArgs2 1 a b)
        emptyMemory [midHelperMir])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := a + b, sizeBytes := 1 })
        (256 ≤ a + b)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
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

/--
Exact composition across a linked helper: the outer caller, the helper linked in
`callees`, and `checked_add_u8` linked through the frame-restoring handler panic
exactly on overflow and return the sum otherwise.
-/
theorem outerCaller_linked_totalExact (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees outerCallerMir
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) [midHelperMir])
      addCallerPre addCallerPost addCallerOverflows :=
  mirHandled_totalExactPanicContract_of_wpMirModularSym checkedAddU8FrameGeneralMirContract
    (checkedAddU8_frameGeneral_holdsTotallyOn fallback) 16 (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact outerCaller_wp a b ha hb)

/--
The same composition through `panicsOnlyIf_call_compose_withCallees`: the
rely–guarantee contract of the outer caller and the only-if contract of the
isolated callee trees (`mirExternalClosedCalleeTrees`) compose.
-/
theorem outerCaller_linked_panicsOnlyIf (fallback : ExternalCallHandler) :
    PanicsOnlyIf
      (mirHandledTrees outerCallerMir
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) [midHelperMir])
      addCallerPre addCallerPost addCallerOverflows :=
  panicsOnlyIf_call_compose_withCallees
    checkedAddU8FrameGeneralContract.withTraitsPreserved []
    (mirModularPanicsOnlyIf_of_dwlp checkedAddU8FrameGeneralMirContract (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact DWLP.mono (fun _ _ h => h.toPanicOutcomeOk)
        (dwp_of_wpMirModularSym (outerCaller_wp a b ha hb)).toDWLP))
    (panicsWithPolicyOnlyIf_forbidAbort_iff.1
      (mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp (by
        rintro ⟨_, typeArgs, _, mem⟩ ⟨⟨rfl, ⟨a, b, -, -, rfl⟩, hB⟩, -⟩
        exact DWLP.mono
          (fun out _ h =>
            (checkedAddU8FrameGeneralContract.withTraitsPreserved
              |>.toPolicy_post_outcomeToRestoredCallAns_iff .forbidAbort _ out).1 h)
          (dwp_of_wpMirNoCallSym
            (checkedAddU8_frameGeneral_callee_wp typeArgs a b mem hB)).toDWLP)))
    (fun _ hPre hNe => False.elim (hNe hPre.1))

/--
`linkCalleeHandler` from a nested frame: the request for `checked_add_u8` comes
from inside `midHelperMir` (`activeCallee := some midHelperMir`), and
`linkCalleeHandler` runs the callee from the request memory unchanged. The
machine therefore steps `midHelperMir`'s code (`stepMirFn_eq_of_activeCallee_some`)
on the callee's locals, whose call to `checked_add_u8` is unlinked inside the
handler and faults. No panic contract of this linked system holds, whereas the
frame-resetting `linkCalleeWithCalleesHandler` gives the total exact contract
(`outerCaller_linked_totalExact`).
-/
theorem outerCaller_linkCalleeHandler_not_panicsWithPolicyOnlyIf
    (fallback : ExternalCallHandler)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    ¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees outerCallerMir (linkCalleeHandler checkedAddU8Mir fallback) [midHelperMir])
      addCallerPre post panicCond policy := by
  have hPre : addCallerPre (scalarArgs2 1 1 2, emptyMemory) :=
    ⟨⟨1, 2, by decide, by decide, rfl⟩, rfl⟩
  refine not_panicsWithPolicyOnlyIf_of_reachesLinkedFault hPre ?_
  repeat (first | refine .handler rfl ?_ | refine .tau rfl ?_)
  refine not_treeSafe_linkCalleeHandler_of_reachesLinkedFault fallback rfl ?_
  repeat (first | exact .handler rfl (not_treeSafe_failAllCalls _) | refine .tau rfl ?_)

/-- The two handlers disagree on the same caller, helper, and callee. -/
theorem outerCaller_linkCalleeHandler_vs_withCallees (fallback : ExternalCallHandler) :
    TotalExactPanicContract
        (mirHandledTrees outerCallerMir
          (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) [midHelperMir])
        addCallerPre addCallerPost addCallerOverflows ∧
      ¬ PanicsOnlyIf
        (mirHandledTrees outerCallerMir (linkCalleeHandler checkedAddU8Mir fallback)
          [midHelperMir])
        addCallerPre addCallerPost addCallerOverflows :=
  ⟨outerCaller_linked_totalExact fallback, fun h =>
    outerCaller_linkCalleeHandler_not_panicsWithPolicyOnlyIf fallback addCallerPost
      addCallerOverflows .forbidAbort (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h)⟩

/-! ### Concrete `ExactPolicy` mutual exclusion & `waiveAbortUnchecked` handler refutation -/

/--
Concrete handler refutation: `checkedAddU8Mir` linked via `linkCalleeHandler`
returns normally on `(0, 0)`, so it refutes
`(checkedAddU8Contract.toExactPolicyMirCallContract .waiveAbortUnchecked).holdsOn`.
-/
theorem checkedAddU8_not_holdsOn_toExactPolicy_waiveAbortUnchecked
    (fallback : ExternalCallHandler) :
    ¬ (checkedAddU8Contract.toExactPolicyMirCallContract .waiveAbortUnchecked).holdsOn
      (linkCalleeHandler checkedAddU8Mir fallback) := by
  have hReq : checkedAddU8Contract.pre
      { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 0 0,
        memory := emptyMemory } :=
    ⟨rfl, zeroArgs_pre, rfl⟩
  have hTot := checkedAddU8_holdsTotallyOn fallback _ hReq
  obtain ⟨tr, ans, hr, hPost⟩ := exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hTot
  cases ans with
  | returned retVal memAfter =>
    exact PanicMirCallContract.not_holdsOn_toExactPolicy_waiveAbortUnchecked_of_returns
      hReq hr
  | panicked _ => exact False.elim (show ¬ ((256 : Nat) ≤ 0 + 0) by decide <| hPost.1)
  | aborted => exact False.elim hPost

/--
A body with an unwinding and an aborting failure:
`bb0: switchInt(copy _1) -> [0: bb1, 1: bb2, otherwise: bb3]`,
`bb1: core::panicking::panic() -> unwind continue`, `bb2: terminate`,
`bb3: _0 = copy _1; return`.
-/
def panicOrAbortMir : CapturedMir :=
  mkBody "panic_tests::panic_or_abort" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut neverTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (.copy (local_ 1))
            { branches := [(0, 1), (1, 2)], otherwise := 3 })
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic") [] (local_ 2) .none .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem panicOrAbort_wp (x : Nat) :
    wpMirNoCallSym 8 panicOrAbortMir
      (initMachineStateWithCallees panicOrAbortMir [.scalar { bits := x, sizeBytes := 1 }] [])
      (ExactPolicyOutcome (.abortOnlyIf (fun args : List Value => argBits args 0 = 1))
        [.scalar { bits := x, sizeBytes := 1 }]
        (fun r : MirReturn => r.1 = .scalar { bits := x, sizeBytes := 1 })
        (x = 0)) := by
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    have hx : x = 0 := (nat_beq_eq_true_iff _ _).1 heq
    exact ⟨hx, fun (h : x = 1) => absurd (hx.symm.trans h) (by decide)⟩
  · rename_i heq0 _ heq1
    exact ⟨(nat_beq_eq_true_iff _ _).1 heq1, (nat_beq_eq_false_iff _ _).1 heq0⟩
  · rename_i heq0 _ heq1
    exact ⟨(nat_beq_eq_false_iff _ _).1 heq0, (nat_beq_eq_false_iff _ _).1 heq1, rfl⟩

/-- The body returns its argument. -/
def panicOrAbortPost (args : List Value) (r : MirReturn) : Prop :=
  r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 }

/-- The body panics exactly on `0`, aborts exactly on `1`, and returns otherwise. -/
theorem panicOrAbort_totalExact :
    TotalExactPolicyPanicContract (mirTrees panicOrAbortMir) scalarPre1 panicOrAbortPost
      (fun args => argBits args 0 = 0) (.abortOnlyIf (fun args => argBits args 0 = 1)) :=
  totalExactPolicyPanicContract_of_wpMirNoCallSym 8 (by
    rintro _ ⟨x, -, rfl⟩
    exact panicOrAbort_wp x)

theorem panicOrAbort_exactPanicAbort :
    ExactPanicAbortContract (mirTrees panicOrAbortMir) scalarPre1 panicOrAbortPost
      (fun args => argBits args 0 = 0) (fun args => argBits args 0 = 1) :=
  exactPolicyPanicContract_abortOnlyIf_iff.1 panicOrAbort_totalExact.exact

/-- The call-free body has deterministic outcomes. -/
theorem panicOrAbort_deterministicRet (x : Nat) :
    DeterministicRet (mirTrees panicOrAbortMir [] [.scalar { bits := x, sizeBytes := 1 }]) :=
  deterministicRet_of_dwlp_mirNoCallWP (dwp_of_wpMirNoCallSym (panicOrAbort_wp x)).toDWLP

/--
Mutual exclusion rejects an over-claimed abort condition: no exact contract can
say that the input `0` both panics and aborts.
-/
theorem panicOrAbort_not_exactPanicAbort_overlapping :
    ¬ ExactPanicAbortContract (mirTrees panicOrAbortMir) scalarPre1 panicOrAbortPost
      (fun args => argBits args 0 = 0) (fun args => argBits args 0 ≤ 1) := fun h =>
  h.conds_disjoint_of_deterministic (x := [.scalar { bits := 0, sizeBytes := 1 }])
    ⟨0, by decide, rfl⟩ (panicOrAbort_deterministicRet 0) ⟨rfl, by decide⟩

/-- The total exact policy contract makes its panic and abort conditions disjoint on `pre`. -/
theorem panicOrAbort_conds_disjoint (args : List Value) (hPre : scalarPre1 args) :
    ¬ (argBits args 0 = 0 ∧ argBits args 0 = 1) :=
  panicOrAbort_totalExact.conds_disjoint hPre

/-! ### Concrete `Anneal.Pass` variance instantiation (NOP insertion / elimination) -/

/--
NOP-inserted variant of `checkedAddU8Mir`: prepends `StatementKind.nop` to
`bb0`, adding one extra silent `.tau` step before executing the identical
overflow check and return.
-/
def checkedAddU8NopMir : CapturedMir :=
  mkBody "panic_tests::checked_add_u8_nop" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut u8CheckedTy ]
    [ { statements :=
          [ mkStmt .nop
          , mkStmt (.storageLive 3)
          , mkStmt (.assign (local_ 3)
              (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolTy] }) false 1 .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.move { local_ := 3, projection := [.field 0 u8Ty] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

private theorem cofix_eq_of_step_ret {step : MirExecState → MirStepNode} {st : MirExecState}
    {out : MirOutcome} (h : step st = .ret out) :
    ITree.cofix step st = .ret out := by
  apply ITree.eq_of_observe_eq
  rw [ITree.observe_cofix, h, ITree.observe_ret]
  rfl

private theorem cofix_eq_of_step_tau {step : MirExecState → MirStepNode} {st st' : MirExecState}
    (h : step st = .tau st') :
    ITree.cofix step st = .tau (ITree.cofix step st') := by
  apply ITree.eq_of_observe_eq
  rw [ITree.observe_cofix, h, ITree.observe_tau]
  rfl

private theorem cofix_eq_of_step_fail {step : MirExecState → MirStepNode} {st : MirExecState}
    {fk : FailureKind} (h : step st = MirStepNode.fail fk) :
    ITree.cofix step st = ITree.fail (E := MirEffect) fk := by
  apply ITree.eq_of_observe_eq
  rw [ITree.observe_cofix, h]
  unfold ITree.fail ITree.triggerSub
  rw [vis_bind, ITree.observe_vis]
  dsimp only [MirStepNode.fail, ITreeF.map, Subeffect.injReq]
  congr 1
  funext o
  exact PEmpty.elim o

private theorem evalScalarBinOp_addWithOverflow_mem {lhs rhs : ScalarInt}
    {locals locals' : List LocalSlot} {mem mem' : Memory} {isSigned : Bool} {val : Value}
    (h : evalScalarBinOp .addWithOverflow lhs rhs locals mem isSigned = .ok val locals' mem') :
    mem' = mem := by
  unfold evalScalarBinOp at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases isSigned <;> (simp only [] at h; injection h with _ _ hMem; exact hMem.symm)

private theorem evalRvalue_addWithOverflow_mem {locals : List LocalSlot}
    {lhs rhs : Operand} {mem mem' : Memory} {decls : List LocalDecl}
    {layouts : LayoutTable} {val : Value} {locals' : List LocalSlot}
    (h : evalRvalue locals (.binaryOp .addWithOverflow lhs rhs) mem decls layouts =
      .ok val locals' mem') :
    mem' = mem := by
  unfold evalRvalue at h
  simp only [] at h
  cases hL : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack with
  | ub => simp only [hL] at h; nomatch h
  | unsupported => simp only [hL] at h; nomatch h
  | ok lv l1 =>
    simp only [hL] at h
    cases hR : evalOperand l1 rhs mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack with
    | ub => simp only [hR] at h; nomatch h
    | unsupported => simp only [hR] at h; nomatch h
    | ok rv l2 =>
      simp only [hR] at h
      cases lv with
      | scalar ls =>
        cases rv with
        | scalar rs =>
          cases hFl : Bool.or (isFloatOptTy (operandTy decls layouts lhs))
              (isFloatOptTy (operandTy decls layouts rhs)) with
          | true =>
            simp only [hFl, evalFloatScalarBinOp] at h
            repeat' split at h
            all_goals nomatch h
          | false =>
            simp only [hFl] at h
            exact evalScalarBinOp_addWithOverflow_mem h
        | ptr _ _ => nomatch h
        | _ => nomatch h
      | ptr _ _ =>
        cases rv with
        | scalar _ => nomatch h
        | ptr _ _ => nomatch h
        | _ => nomatch h
      | aggregate _ _ =>
        cases rv with
        | aggregate _ _ =>
          simp only [evalWidePtrAggregateRelBinOp, isRelationalBinOp] at h
          split at h <;> nomatch h
        | _ => nomatch h
      | _ => nomatch h

private theorem evalRvalue_use_move_local_mem {locals : List LocalSlot}
    {loc : Local} {proj : List ProjectionElem} {mem mem' : Memory}
    {decls : List LocalDecl} {layouts : LayoutTable} {val : Value}
    {locals' : List LocalSlot}
    (hNoDeref : ∀ p rest, proj = p :: rest → p ≠ .deref)
    (h : evalRvalue locals (.use (.move { local_ := loc, projection := proj })) mem decls layouts =
      .ok val locals' mem') :
    mem' = mem := by
  unfold evalRvalue at h
  simp only [] at h
  cases hEval : evalOperand locals (.move { local_ := loc, projection := proj })
      mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack with
  | ub => simp only [hEval] at h; nomatch h
  | unsupported => simp only [hEval] at h; nomatch h
  | ok v l' =>
    simp only [hEval] at h
    cases hVal : validateLoadedValue layouts decls
        (.move { local_ := loc, projection := proj }) v with
    | false => simp only [hVal] at h; nomatch h
    | true =>
      simp only [hVal] at h
      cases proj with
      | nil => injection h with _ _ hMem; exact hMem.symm
      | cons p rest =>
        have hNe := hNoDeref p rest rfl
        cases p with
        | deref => exact False.elim (hNe rfl)
        | _ => injection h with _ _ hMem; exact hMem.symm

private theorem eutt_tau_tau {E : Effect.{u}} {R : Type u} {t u : ITree E R}
    (h : Eutt t u) : Eutt (.tau t) (.tau u) := by
  rw [Eutt.eq_def]
  exact Or.inr (Or.inr ⟨t, u, ITree.observe_tau t, ITree.observe_tau u, h⟩)

private theorem eutt_tau_right_of {E : Effect.{u}} {R : Type u} {t u : ITree E R}
    (h : Eutt t u) : Eutt t (.tau u) := by
  refine Eutt.coinduct (fun a b => Eutt a b ∨ ∃ b', b.observe = .tau b' ∧ Eutt a b') ?_ t (.tau u)
    (Or.inr ⟨u, ITree.observe_tau u, h⟩)
  intro a b hab
  rcases hab with hEq | ⟨b', hb', hEq⟩
  · rw [Eutt.eq_def] at hEq
    rcases hEq with ⟨a', b', r, ha, hb, har, hbr⟩ |
      ⟨a', b', i, k₁, k₂, ha, hb, hav, hbv, hk⟩ | ⟨a', b', ha, hb, h'⟩
    · exact Or.inl ⟨a', b', r, ha, hb, har, hbr⟩
    · exact Or.inr (Or.inl ⟨a', b', i, k₁, k₂, ha, hb, hav, hbv, fun o => Or.inl (hk o)⟩)
    · exact Or.inr (Or.inr ⟨a', b', ha, hb, Or.inl h'⟩)
  · rw [Eutt.eq_def] at hEq
    rcases hEq with ⟨a', c', r, ha, hb, har, hbr⟩ |
      ⟨a', c', i, k₁, k₂, ha, hb, hav, hbv, hk⟩ | ⟨a', c', ha, hb, h'⟩
    · exact Or.inl ⟨a', c', r, ha, .step hb' hb, har, hbr⟩
    · exact Or.inr (Or.inl ⟨a', c', i, k₁, k₂, ha, .step hb' hb, hav, hbv, fun o => Or.inl (hk o)⟩)
    · exact Or.inr (Or.inr ⟨a', b', ha, hb', Or.inr ⟨c', hb, h'⟩⟩)

private theorem checkedAddU8_bb1_eutt (locals : List LocalSlot) :
    Eutt
      (ITree.cofix (stepMirState checkedAddU8Mir)
        (.running { frame := { blockIdx := 1, stmtIdx := 0, locals := locals },
                    memory := emptyMemory }))
      (ITree.cofix (stepMirState checkedAddU8NopMir)
        (.running { frame := { blockIdx := 1, stmtIdx := 0, locals := locals },
                    memory := emptyMemory })) := by
  let s : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 0, locals := locals }, memory := emptyMemory }
  have hStep1 :
      stepMirState checkedAddU8Mir (.running s) =
        evalStmt s (mkStmt (.assign (local_ 0)
            (.use (.move { local_ := 3, projection := [.field 0 u8Ty] }))))
          checkedAddU8Mir.localDecls checkedAddU8Mir.layouts := rfl
  have hStep2 :
      stepMirState checkedAddU8NopMir (.running s) =
        evalStmt s (mkStmt (.assign (local_ 0)
            (.use (.move { local_ := 3, projection := [.field 0 u8Ty] }))))
          checkedAddU8Mir.localDecls checkedAddU8Mir.layouts := rfl
  cases hRv : evalRvalue locals (.use (.move { local_ := 3, projection := [.field 0 u8Ty] }))
      emptyMemory checkedAddU8Mir.localDecls checkedAddU8Mir.layouts with
  | ub =>
    rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
          (by rw [hStep1]; simp only [evalStmt, mkStmt, s, hRv]),
        cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
          (by rw [hStep2]; simp only [evalStmt, mkStmt, s, hRv])]
    exact Eutt.refl _
  | unsupported =>
    rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .unsupported)
          (by rw [hStep1]; simp only [evalStmt, mkStmt, s, hRv]; rfl),
        cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .unsupported)
          (by rw [hStep2]; simp only [evalStmt, mkStmt, s, hRv]; rfl)]
    exact Eutt.refl _
  | ok val locals₁ mem₁ =>
    have hMemEq : mem₁ = emptyMemory :=
      evalRvalue_use_move_local_mem (fun _ _ hEq => by injection hEq with hp; subst hp; intro h; nomatch h) hRv
    subst hMemEq
    cases hGet : Trusted.Sequence.get? locals₁ 0 with
    | none =>
      rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
            (by rw [hStep1]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet]),
          cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
            (by rw [hStep2]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet])]
      exact Eutt.refl _
    | some slot =>
      cases slot with
      | dead =>
        rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
              (by rw [hStep1]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet]),
            cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
              (by rw [hStep2]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet])]
        exact Eutt.refl _
      | uninit | init _ =>
        cases hSet : Trusted.Sequence.set? locals₁ 0 (.init val) with
        | none =>
          rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                (by rw [hStep1]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet, hSet]),
              cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                (by rw [hStep2]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet, hSet])]
          exact Eutt.refl _
        | some locals₂ =>
          let sNext : MachineState :=
            { frame := { blockIdx := 1, stmtIdx := 1, locals := locals₂ }, memory := emptyMemory }
          rw [cofix_eq_of_step_tau (step := stepMirState checkedAddU8Mir) (st' := .running sNext)
                (by rw [hStep1]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet, hSet]; rfl),
              cofix_eq_of_step_tau (step := stepMirState checkedAddU8NopMir) (st' := .running sNext)
                (by rw [hStep2]; simp only [evalStmt, mkStmt, local_, s, hRv, hGet, hSet]; rfl)]
          apply eutt_tau_tau
          have hRet1 : stepMirState checkedAddU8Mir (.running sNext) =
              evalTerminator sNext (mkTerm .return_) (.some checkedAddU8Mir) := rfl
          have hRet2 : stepMirState checkedAddU8NopMir (.running sNext) =
              evalTerminator sNext (mkTerm .return_) (.some checkedAddU8Mir) := rfl
          cases hNode : evalTerminator sNext (mkTerm .return_) (.some checkedAddU8Mir) with
          | ret out =>
            rw [cofix_eq_of_step_ret (step := stepMirState checkedAddU8Mir) (hRet1.trans hNode),
                cofix_eq_of_step_ret (step := stepMirState checkedAddU8NopMir) (hRet2.trans hNode)]
            exact Eutt.refl _
          | tau st' =>
            simp only [evalTerminator, mkTerm, sNext] at hNode
            repeat (split at hNode <;> try contradiction)
          | vis i k =>
            have hFk : ∃ fk, evalTerminator sNext (mkTerm .return_) (.some checkedAddU8Mir) =
                MirStepNode.fail fk := by
              simp only [evalTerminator, mkTerm, sNext] at hNode ⊢
              repeat (split at hNode <;> try contradiction)
              all_goals (try exact ⟨.ub, rfl⟩)
            obtain ⟨fk, hF⟩ := hFk
            rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (hRet1.trans hF),
                cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (hRet2.trans hF)]
            exact Eutt.refl _

/-- Every `args : List Value` gives an `Eutt`-equivalent tree under NOP insertion. -/
theorem checkedAddU8_nop_eutt (args : List Value) :
    Eutt (mirTrees checkedAddU8Mir [] args) (mirTrees checkedAddU8NopMir [] args) := by
  let s₀ : MachineState := initMachineStateWithCallees checkedAddU8Mir args []
  -- Step 0 of `checkedAddU8NopMir`: `.nop` advances `stmtIdx` from `0` to `1`.
  have hNop0 :
      mirTrees checkedAddU8NopMir [] args =
        .tau (ITree.cofix (stepMirState checkedAddU8NopMir)
          (.running { s₀ with frame := { s₀.frame with stmtIdx := 1 } })) :=
    cofix_eq_of_step_tau (step := stepMirState checkedAddU8NopMir)
      (st := .running s₀) (st' := .running { s₀ with frame := { s₀.frame with stmtIdx := 1 } }) rfl
  rw [hNop0]
  apply eutt_tau_right_of
  -- Step 1 (`storageLive 3`): identical locals update in both bodies.
  have hLiveStepA :
      stepMirState checkedAddU8Mir (.running s₀) =
        evalStmt s₀ (mkStmt (.storageLive 3)) checkedAddU8Mir.localDecls
          checkedAddU8Mir.layouts := rfl
  have hLiveStepB :
      stepMirState checkedAddU8NopMir
          (.running { s₀ with frame := { s₀.frame with stmtIdx := 1 } }) =
        evalStmt { s₀ with frame := { s₀.frame with stmtIdx := 1 } }
          (mkStmt (.storageLive 3)) checkedAddU8Mir.localDecls
          checkedAddU8Mir.layouts := rfl
  cases hGet3 : Trusted.Sequence.get? s₀.frame.locals 3 with
  | none =>
    change Eutt (ITree.cofix (stepMirState checkedAddU8Mir) (.running s₀)) _
    rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
          (by rw [hLiveStepA]; simp only [evalStmt, mkStmt, hGet3]),
        cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
          (by rw [hLiveStepB]; simp only [evalStmt, mkStmt, hGet3])]
    exact Eutt.refl _
  | some slot3 =>
    cases hSet3 : Trusted.Sequence.set? s₀.frame.locals 3 .uninit with
    | none =>
      change Eutt (ITree.cofix (stepMirState checkedAddU8Mir) (.running s₀)) _
      rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
            (by rw [hLiveStepA]; simp only [evalStmt, mkStmt, hGet3, hSet3]),
          cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
            (by rw [hLiveStepB]; simp only [evalStmt, mkStmt, hGet3, hSet3])]
      exact Eutt.refl _
    | some locals₁ =>
      let s₁A : MachineState :=
        { frame := { blockIdx := 0, stmtIdx := 1, locals := locals₁ }, memory := emptyMemory }
      let s₁B : MachineState :=
        { frame := { blockIdx := 0, stmtIdx := 2, locals := locals₁ }, memory := emptyMemory }
      have hLiveA :
          mirTrees checkedAddU8Mir [] args =
            .tau (ITree.cofix (stepMirState checkedAddU8Mir) (.running s₁A)) :=
        cofix_eq_of_step_tau (step := stepMirState checkedAddU8Mir) (by
          rw [hLiveStepA]; simp only [evalStmt, mkStmt, hGet3, hSet3]; rfl)
      have hLiveB :
          ITree.cofix (stepMirState checkedAddU8NopMir)
              (.running { s₀ with frame := { s₀.frame with stmtIdx := 1 } }) =
            .tau (ITree.cofix (stepMirState checkedAddU8NopMir) (.running s₁B)) :=
        cofix_eq_of_step_tau (step := stepMirState checkedAddU8NopMir) (by
          rw [hLiveStepB]; simp only [evalStmt, mkStmt, hGet3, hSet3]; rfl)
      rw [hLiveA, hLiveB]
      apply eutt_tau_tau
      -- Step 2 (`assign _3 = AddWithOverflow(_1, _2)`): same `evalRvalue` in both bodies.
      have hAsgnA :
          stepMirState checkedAddU8Mir (.running s₁A) =
            evalStmt s₁A (mkStmt (.assign (local_ 3)
                (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))))
              checkedAddU8Mir.localDecls checkedAddU8Mir.layouts := rfl
      have hAsgnB :
          stepMirState checkedAddU8NopMir (.running s₁B) =
            evalStmt s₁B (mkStmt (.assign (local_ 3)
                (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))))
              checkedAddU8Mir.localDecls checkedAddU8Mir.layouts := rfl
      cases hRv : evalRvalue locals₁
          (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))
          emptyMemory checkedAddU8Mir.localDecls checkedAddU8Mir.layouts with
      | ub =>
        rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
              (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]),
            cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
              (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv])]
        exact Eutt.refl _
      | unsupported =>
        rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .unsupported)
              (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]; rfl),
            cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .unsupported)
              (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv]; rfl)]
        exact Eutt.refl _
      | ok val locals₂ mem₂ =>
        have hMemEq : mem₂ = emptyMemory := evalRvalue_addWithOverflow_mem hRv
        subst hMemEq
        cases hGet : Trusted.Sequence.get? locals₂ 3 with
        | none =>
          rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]; simp only [local_, hGet]),
              cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv]; simp only [local_, hGet])]
          exact Eutt.refl _
        | some slot =>
          cases slot with
          | dead =>
            rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                  (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]; simp only [local_, hGet]),
                cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                  (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv]; simp only [local_, hGet])]
            exact Eutt.refl _
          | uninit | init _ =>
            cases hSet : Trusted.Sequence.set? locals₂ 3 (.init val) with
            | none =>
              rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                    (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]; simp only [local_, hGet, hSet]),
                  cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                    (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv]; simp only [local_, hGet, hSet])]
              exact Eutt.refl _
            | some locals₃ =>
              let s₂A : MachineState :=
                { frame := { blockIdx := 0, stmtIdx := 2, locals := locals₃ }, memory := emptyMemory }
              let s₂B : MachineState :=
                { frame := { blockIdx := 0, stmtIdx := 3, locals := locals₃ }, memory := emptyMemory }
              rw [cofix_eq_of_step_tau (step := stepMirState checkedAddU8Mir) (st' := .running s₂A)
                    (by rw [hAsgnA]; simp only [evalStmt, mkStmt, s₁A, hRv]; simp only [local_, hGet, hSet]; rfl),
                  cofix_eq_of_step_tau (step := stepMirState checkedAddU8NopMir) (st' := .running s₂B)
                    (by rw [hAsgnB]; simp only [evalStmt, mkStmt, s₁B, hRv]; simp only [local_, hGet, hSet]; rfl)]
              apply eutt_tau_tau
              -- Step 3 (`assert !(_3.1) -> bb1`): converges to identical `bb1` state or `.panic`/`.ub`.
              have hTermA :
                  stepMirState checkedAddU8Mir (.running s₂A) =
                    evalTerminator s₂A
                      (mkTerm (.assert (.move { local_ := 3, projection := [.field 1 boolTy] })
                        false 1 .continue_))
                      (.some checkedAddU8Mir) := rfl
              have hTermB :
                  stepMirState checkedAddU8NopMir (.running s₂B) =
                    evalTerminator s₂B
                      (mkTerm (.assert (.move { local_ := 3, projection := [.field 1 boolTy] })
                        false 1 .continue_))
                      (.some checkedAddU8NopMir) := rfl
              have hLay : checkedAddU8NopMir.layouts = checkedAddU8Mir.layouts := rfl
              cases hOp : evalOperand locals₃
                  (.move { local_ := 3, projection := [.field 1 boolTy] })
                  emptyMemory.borrows emptyMemory.globals checkedAddU8Mir.layouts
                  emptyMemory.callerLocals [] emptyMemory.callStack with
              | ub =>
                rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                      (by rw [hTermA]; simp only [evalTerminator, mkTerm, s₂A, hOp]),
                    cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                      (by rw [hTermB]; simp only [evalTerminator, mkTerm, s₂B, hLay, hOp])]
                exact Eutt.refl _
              | unsupported =>
                rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .unsupported)
                      (by rw [hTermA]; simp only [evalTerminator, mkTerm, s₂A, hOp]; rfl),
                    cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .unsupported)
                      (by rw [hTermB]; simp only [evalTerminator, mkTerm, s₂B, hLay, hOp]; rfl)]
                exact Eutt.refl _
              | ok condVal locals₄ =>
                cases condVal with
                | scalar sc =>
                  cases hBit : Nat.beq sc.bits 0 with
                  | true =>
                    let s₃ : MachineState :=
                      { frame := { blockIdx := 1, stmtIdx := 0, locals := locals₄ },
                        memory := emptyMemory }
                    rw [cofix_eq_of_step_tau (step := stepMirState checkedAddU8Mir) (st' := .running s₃)
                          (by rw [hTermA]; simp only [evalTerminator, mkTerm, s₂A, hOp, hBit]; rfl),
                        cofix_eq_of_step_tau (step := stepMirState checkedAddU8NopMir) (st' := .running s₃)
                          (by rw [hTermB]; simp only [evalTerminator, mkTerm, s₂B, hLay, hOp, hBit]; rfl)]
                    exact eutt_tau_tau (checkedAddU8_bb1_eutt locals₄)
                  | false =>
                    rw [cofix_eq_of_step_ret (step := stepMirState checkedAddU8Mir) (out := .panic)
                          (by rw [hTermA]; simp only [evalTerminator, mkTerm, s₂A, hOp, hBit]; rfl),
                        cofix_eq_of_step_ret (step := stepMirState checkedAddU8NopMir) (out := .panic)
                          (by rw [hTermB]; simp only [evalTerminator, mkTerm, s₂B, hLay, hOp, hBit]; rfl)]
                    exact Eutt.refl _
                | _ =>
                  rw [cofix_eq_of_step_fail (step := stepMirState checkedAddU8Mir) (fk := .ub)
                        (by rw [hTermA]; simp only [evalTerminator, mkTerm, s₂A, hOp]),
                      cofix_eq_of_step_fail (step := stepMirState checkedAddU8NopMir) (fk := .ub)
                        (by rw [hTermB]; simp only [evalTerminator, mkTerm, s₂B, hLay, hOp])]
                  exact Eutt.refl _

private def mirArgsMachine (args : List Value) :
    ITreeMachine CapturedMir MirExecState MirEffect MirOutcome where
  init body := .running (initMachineStateWithCallees body args [])
  step := stepMirState

/--
Concrete `ExactPass` between `checkedAddU8Mir` and its `.tau`-inserting NOP
variant `checkedAddU8NopMir` over stateless `mirTrees`.
-/
theorem checkedAddU8_nop_exactPass :
    ExactPass
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      id id checkedAddU8Mir checkedAddU8NopMir where
  up_refines _ args :=
    (exactPass_of_eutt (mirArgsMachine args) (mirArgsMachine args)
      (EffectObs.erase MirEffect PUnit) (checkedAddU8_nop_eutt args)).up_refines trivial
  down_refines _ args :=
    (exactPass_of_eutt (mirArgsMachine args) (mirArgsMachine args)
      (EffectObs.erase MirEffect PUnit) (checkedAddU8_nop_eutt args)).down_refines trivial

/--
Concrete `Anneal.Pass` variance transfers:
1. `PanicsOnlyIf` transfers forward via `CompilerPass`,
2. `PanicsIf` transfers backward via `CompilerPass`,
3. `ExactPanicContract` transfers bidirectionally via `ExactPass`, and
4. `TotalExactPanicContract` transfers forward via `ExactPass` plus target termination.
-/
theorem checkedAddU8Nop_pass_variance_transfers :
    PanicsOnlyIf (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1) (overflows 1) ∧
      ExactPanicContract (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1) (overflows 1) ∧
      PanicsIf (mirTrees checkedAddU8Mir) (scalarPre2 1) (overflows 1) ∧
      TotalExactPanicContract (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1)
        (overflows 1) := by
  have hOnly :
      PanicsOnlyIf (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1) (overflows 1) :=
    PanicsOnlyIf.compilerPass_forward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      (checkedAddU8_nop_exactPass.toCompilerPass Spec.top)
      trivial checkedAddU8_exact.1
  have hExact :
      ExactPanicContract (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1) (overflows 1) :=
    (exactPanicContract_exactPass_iff
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      checkedAddU8_nop_exactPass).1 checkedAddU8_exact
  have hIfBack :
      PanicsIf (mirTrees checkedAddU8Mir) (scalarPre2 1) (overflows 1) :=
    PanicsIf.compilerPass_backward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      (checkedAddU8_nop_exactPass.toCompilerPass Spec.top)
      trivial (fun x hx => (checkedAddU8_exact.1 x hx).1) hExact.2
  have hTermNop : TerminatesOn (mirTrees checkedAddU8NopMir) (scalarPre2 1) :=
    terminatesOn_of_dwp (ewp := mirDefaultWP) (Q := fun _ _ => True) (by
      rintro _ ⟨a, b, -, -, rfl⟩
      refine dwp_cofix_of_wpCoalBounded 10 ?_
      change wpMirBounded 10 checkedAddU8NopMir _ _
      rw [← wpMirSym_eq_wpMirBounded]
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      all_goals trivial)
  have hTot :
      TotalExactPanicContract (mirTrees checkedAddU8NopMir) (scalarPre2 1) (sumPost 1)
        (overflows 1) :=
    TotalExactPanicContract.exactPass_forward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      checkedAddU8_nop_exactPass hTermNop checkedAddU8_totalExact
  exact ⟨hOnly, hExact, hIfBack, hTot⟩

/-! ### Extended `kani#5202` alignment-blindness & machine-level `arith_offset` probes -/

def ptrConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }

/--
Neither `BinOp.offset` nor `arith_offset` consults pointee alignment: on a
misaligned scalar `*const u32` pointer (`addr = 1`, `count = 0`), `BinOp.offset`
succeeds while `arith_offset` faults `.ub` (because it rejects all `Value.scalar`).
-/
theorem kani5202_misaligned_u32_scalar_ptr_alignment_blindness
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    rvalueValue? (evalRvalue (offsetLocals (addrPtr 1) 0) offsetRv emptyMemory
        (offsetDecls ptrConstU32Ty)) = some (addrPtr 1) ∧
      evalNonSelectIntrinsicCall .arithOffset s target bodyLocalDecls bodyLayouts argOps
        [addrPtr 1, .scalar { bits := 0, sizeBytes := 8 }] locals' destination targetBb =
        MirStepNode.fail .ub :=
  ⟨rfl, rfl⟩

/--
Full machine-level `evalNonSelectIntrinsicCall .arithOffset` on a dangling
`Value.ptr` succeeds in both `memFreedTag42` (`allocDead := true`) and
`memLiveZeroByteAlloc42` (live zero-byte allocation), while `BinOp.offset` with
the same non-zero count `1` faults `.ub`.
-/
theorem kani5202_arith_offset_intrinsic_dangling_ptr_succeeds :
    let target : ResolvedCallTarget :=
      { defPath := "core::intrinsics::arith_offset", typeArgs := [.uint .u8],
        fnSig := .none, isIndirect := false }
    let sFreed : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := offsetLocals (.ptr danglingPtr 8) 1 }
        memory := memFreedTag42 }
    let sZero : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := zstLocals 1 }
        memory := memLiveZeroByteAlloc42 }
    let argOps : List Operand := [.copy (local_ 1), .copy (local_ 2)]
    let argVals : List Value := [.ptr danglingPtr 8, .scalar { bits := 1, sizeBytes := 8 }]
    evalNonSelectIntrinsicCall .arithOffset sFreed target (offsetDecls ptrConstU8Ty)
        emptyLayoutTable argOps argVals sFreed.frame.locals (local_ 0) 1 =
      MirStepNode.step
        { frame := { blockIdx := 1, stmtIdx := 0,
                     locals := [.init (.ptr { danglingPtr with offsetBytes := 1 } 8),
                                .init (.ptr danglingPtr 8),
                                .init (.scalar { bits := 1, sizeBytes := 8 })] }
          memory := memFreedTag42 } ∧
    evalNonSelectIntrinsicCall .arithOffset sZero target zstDecls
        emptyLayoutTable argOps argVals sZero.frame.locals (local_ 0) 1 =
      MirStepNode.step
        { frame := { blockIdx := 1, stmtIdx := 0,
                     locals := [.init (.ptr { danglingPtr with offsetBytes := 1 } 8),
                                .init (.ptr danglingPtr 8),
                                .init (.scalar { bits := 1, sizeBytes := 8 }),
                                .init .unit] }
          memory := memLiveZeroByteAlloc42 } :=
  ⟨rfl, rfl⟩

/-! ### Extended `kani#5219` borrow-backed reborrow/write contagion & global-alloc slices -/

def muMutSliceRefTy : Ty := { kind := .ref .mut (.slice muKind), layoutIdx := 5 }

def muMutDecls : List LocalDecl :=
  muDecls ++ [mkDecl .mut muMutSliceRefTy]

def muMutSliceMem : Memory :=
  { emptyMemory with
    borrows := [probeBorrow 5 1 .unique false]
    nextTag := 6 }

def muMutSliceLocals (arr : Value) : List LocalSlot :=
  [.uninit, .init arr, .uninit, .init muFatPtr, .init muFatPtr]

/--
Reborrow and write contagion on borrow-backed `&[MaybeUninit<u8>]` /
`&mut [MaybeUninit<u8>]`: with union-slot elements both reborrowing
`&(*_3)[0..2]` and writing `(*_4)[0] = MaybeUninit::new(42)` succeed, whereas
a single raw `.uninit` element at index `3` makes both fault `.ub`.
-/
theorem kani5219_borrow_backed_reborrow_and_write_contagion :
    let reborrowRv : Rvalue :=
      .ref .shared { local_ := 3, projection := [.deref, .subslice 0 2 false] }
    let writeStmt : Statement :=
      mkStmt (.assign { local_ := 4, projection := [.deref, .constantIndex 0 1 false] }
        (.use (.constant { ty := muTy, val := .zeroSized })))
    (∃ v, rvalueValue? (evalRvalue (muSliceLocals muSlotArr) reborrowRv muSliceMem
        muDecls muLayouts) = some v) ∧
      rvalueIsUb (evalRvalue (muSliceLocals muPartArr) reborrowRv muSliceMem
        muDecls muLayouts) = true ∧
      (∃ st, evalStmt
          { frame := { blockIdx := 0, stmtIdx := 0, locals := muMutSliceLocals muSlotArr }
            memory := muMutSliceMem }
          writeStmt muMutDecls muLayouts = MirStepNode.step st) ∧
      evalStmt
          { frame := { blockIdx := 0, stmtIdx := 0, locals := muMutSliceLocals muPartArr }
            memory := muMutSliceMem }
          writeStmt muMutDecls muLayouts = MirStepNode.fail .ub :=
  ⟨⟨_, rfl⟩, rfl, ⟨_, rfl⟩, rfl⟩

/-- Global static allocation backing `[MaybeUninit<u8>; 4]` (4 initialized bytes). -/
def muGlobalAlloc : CapturedAllocation :=
  { allocId := 10
    bytes := [.some 7, .some 8, .some 9, .some 10]
    relocations := []
    align := { bytes := 1 }
    mutability := .not }

def muGlobalMem : Memory :=
  { emptyMemory with globals := [muGlobalAlloc], nextAllocId := 11 }

def muGlobalFatPtr : Value :=
  .aggregate 0 [.ptr { allocId := 10, offsetBytes := 0 } 8, .scalar { bits := 4, sizeBytes := 8 }]

def muGlobalLocals : List LocalSlot :=
  [.uninit, .uninit, .uninit, .init muGlobalFatPtr]

/--
`Memory.globals`-backed `&[MaybeUninit<u8>]` slice asymmetry: the metadata-only
`Rvalue.len` succeeds (returning `4`), whereas reading a union-typed element or
subslice out of the fully initialized global bytes is reported as undefined
behavior.
-/
theorem kani5219_global_alloc_slice_asymmetry :
    rvalueValue? (evalRvalue muGlobalLocals
        (.len { local_ := 3, projection := [.deref] }) muGlobalMem muDecls muLayouts) =
        some (.scalar { bits := 4, sizeBytes := 8 }) ∧
      rvalueIsUb (evalRvalue muGlobalLocals
        (muSliceRead [.constantIndex 0 1 false]) muGlobalMem muDecls muLayouts) = true ∧
      rvalueIsUb (evalRvalue muGlobalLocals
        (muSliceRead [.subslice 0 2 false]) muGlobalMem muDecls muLayouts) = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### Multi-step global `CalleeTableExcludes` invariance across intervening statements -/

/--
Multi-step caller with intervening `storageLive`, checked-addition assignment,
assertion, external helper call, second checked-addition + assertion, and final
call to the contracted trait method:
- `bb0`: `storageLive 3; _3 = AddWithOverflow(_1, _2); assert !(_3.1) -> bb1`
- `bb1`: `_4 = helper() -> bb2`
- `bb2`: `storageLive 5; _5 = AddWithOverflow(_3.0, _4); assert !(_5.1) -> bb3`
- `bb3`: `_0 = contracted::<u8>() -> bb4`
- `bb4`: `return`
-/
def multiStepCallerMir : CapturedMir :=
  mkBody "panic_tests::multi_step_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty
    , mkDecl .mut u8CheckedTy, mkDecl .mut u8Ty, mkDecl .mut u8CheckedTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign (local_ 3)
              (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolTy] }) false 1 .continue_)
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 4) ]
        terminator :=
          mkTerm (.call (fnItemOp helperPath) [] (local_ 4) (.some 2) .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 5)
          , mkStmt (.assign (local_ 5)
              (.binaryOp .addWithOverflow
                (.copy { local_ := 3, projection := [.field 0 u8Ty] })
                (.copy (local_ 4)))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 5, projection := [.field 1 boolTy] }) false 3 .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call (fnItemOp contractedPath [.uint .u8]) [] (local_ 0) (.some 4)
            .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/--
End-to-end multi-step runtime guard invariance: starting from `linkedMem` (which
excludes `contractedPath`), for **every** handler `h` preserving `callees` and
`traitImpls`, **every** `MachineState` reachable from the initial state of
`multiStepCallerMir` across all intervening statements, assertions, and calls
still satisfies `CalleeTableExcludes ... contractedPath`, and specifically when
`bb3` is reached (illustrated via a concrete multi-step trace through `bb0 ->
bb1 (helper) -> bb2 -> bb3`) the final call emits a `MirCallE` request instead
of stepping into `evilImplMir`.
-/
theorem multiStepCaller_reachable_preserves_calleeTableExcludes
    (h : ExternalCallHandler) (hH : HandlerPreservesTables h) :
    (∀ a b s',
      ReachableExecState multiStepCallerMir h
        (.running (initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 a b) linkedMem))
        (.running s') →
      CalleeTableExcludes s'.memory contractedPath) ∧
    (∀ tr,
      ReachesRet (h { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem })
        tr (.returned (.scalar { bits := 1, sizeBytes := 1 }) linkedMem) →
      ∃ s3,
        ReachableExecState multiStepCallerMir h
          (.running (initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 1 2) linkedMem))
          (.running s3) ∧
        CalleeTableExcludes s3.memory contractedPath ∧
        stepMirState multiStepCallerMir (.running s3) =
          MirStepNode.extCall
            { defPath := contractedPath, typeArgs := [.uint .u8], args := [],
              memory := s3.memory }
            (resumeExternalCall s3 s3.frame.locals (local_ 0) 4 .continue_)) := by
  refine ⟨fun a b s' hReach =>
      hReach.calleeTableExcludes hH linkedMem_calleeTableExcludes, ?_⟩
  intro tr hAns
  let s0 := initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 1 2) linkedMem
  let l1 : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := 1, sizeBytes := 1 })
    , .init (.scalar { bits := 2, sizeBytes := 1 }), .uninit, .dead, .dead ]
  let s1 : MachineState := { frame := { blockIdx := 0, stmtIdx := 1, locals := l1 }, memory := linkedMem }
  let pair3 : Value :=
    .aggregate 0 [.scalar { bits := 3, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }]
  let l2 : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := 1, sizeBytes := 1 })
    , .init (.scalar { bits := 2, sizeBytes := 1 }), .init pair3, .dead, .dead ]
  let s2 : MachineState := { frame := { blockIdx := 0, stmtIdx := 2, locals := l2 }, memory := linkedMem }
  let sBb1 : MachineState := { frame := { blockIdx := 1, stmtIdx := 0, locals := l2 }, memory := linkedMem }
  let l2' : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := 1, sizeBytes := 1 })
    , .init (.scalar { bits := 2, sizeBytes := 1 }), .init pair3, .uninit, .dead ]
  let sBb1_1 : MachineState := { frame := { blockIdx := 1, stmtIdx := 1, locals := l2' }, memory := linkedMem }
  let l4 : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := 1, sizeBytes := 1 })
    , .init (.scalar { bits := 2, sizeBytes := 1 }), .init pair3
    , .init (.scalar { bits := 1, sizeBytes := 1 }), .uninit ]
  let sBb2_1 : MachineState := { frame := { blockIdx := 2, stmtIdx := 1, locals := l4 }, memory := linkedMem }
  let pair5 : Value :=
    .aggregate 0 [.scalar { bits := 4, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }]
  let l5 : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := 1, sizeBytes := 1 })
    , .init (.scalar { bits := 2, sizeBytes := 1 }), .init pair3
    , .init (.scalar { bits := 1, sizeBytes := 1 }), .init pair5 ]
  let sBb2_2 : MachineState := { frame := { blockIdx := 2, stmtIdx := 2, locals := l5 }, memory := linkedMem }
  let sBb3 : MachineState := { frame := { blockIdx := 3, stmtIdx := 0, locals := l5 }, memory := linkedMem }
  have hReach : ReachableExecState multiStepCallerMir h (.running s0) (.running sBb3) :=
    .tau (st₁ := .running s1) rfl
      (.tau (st₁ := .running s2) rfl
        (.tau (st₁ := .running sBb1) rfl
          (.tau (st₁ := .running sBb1_1) rfl
            (.call (req := { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem })
              (k := resumeExternalCall sBb1_1 sBb1_1.frame.locals (local_ 4) 2 .continue_)
              rfl hAns
              (.tau (st₁ := .running sBb2_1) rfl
                (.tau (st₁ := .running sBb2_2) rfl
                  (.tau (st₁ := .running sBb3) rfl (.refl _))))))))
  have hExcl : CalleeTableExcludes sBb3.memory contractedPath :=
    hReach.calleeTableExcludes hH linkedMem_calleeTableExcludes
  exact ⟨sBb3, hReach, hExcl,
    evalTerminator_extCall_of_call_site (s := sBb3)
      (term := mkTerm (.call (fnItemOp contractedPath [.uint .u8]) [] (local_ 0) (.some 4) .continue_))
      (currentBody := .some multiStepCallerMir)
      (func := fnItemOp contractedPath [.uint .u8]) (argOps := []) (destination := local_ 0)
      (targetBb := 4) (unwind := .continue_) (targetDefPath := contractedPath)
      (argVals := []) rfl rfl rfl hExcl rfl rfl⟩

/--
A concrete handler meets the hypothesis of
`multiStepCaller_reachable_preserves_calleeTableExcludes`: `checked_add_u8`
linked through `linkCalleeWithCalleesHandler`, with every other call failing.
-/
theorem multiStepCaller_concrete_handler_guard (a b : Nat) (s' : MachineState)
    (hReach : ReachableExecState multiStepCallerMir
      (linkCalleeWithCalleesHandler checkedAddU8Mir [] failAllCalls)
      (.running (initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 a b) linkedMem))
      (.running s')) :
    CalleeTableExcludes s'.memory contractedPath :=
  (multiStepCaller_reachable_preserves_calleeTableExcludes _
    (handlerPreservesTables_linkCalleeWithCalleesHandler _ _ _
      handlerPreservesTables_failAllCalls)).1 a b s' hReach

/-- Concrete helper body for `helperPath` returning `1u8`. -/
def helperReturnOneMir : CapturedMir :=
  mkBody helperPath 0
    [ mkDecl .mut u8Ty ]
    [ { statements := [ mkStmt (.assign (local_ 0) (.use (u8Const 1))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Non-vacuous concrete multi-step handler guard: unlike `failAllCalls` alone
(which faults at `bb1` on `helperPath` and never reaches `bb2`/`bb3`), chaining
`helperReturnOneMir` into `linkCalleeWithCalleesHandler` actually answers
`helperPath` with `1`, preserves `CalleeTableExcludes` across **all** reachable
states, **and** concretely reaches `bb3` where the call to `contractedPath`
emits an external `MirCallE` request.
-/
theorem multiStepCaller_concrete_chained_handler_guard_reaches_bb3 :
    let hConcrete : ExternalCallHandler :=
      linkCalleeWithCalleesHandler helperReturnOneMir []
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] failAllCalls)
    (∀ a b s',
      ReachableExecState multiStepCallerMir hConcrete
        (.running (initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 a b) linkedMem))
        (.running s') →
      CalleeTableExcludes s'.memory contractedPath) ∧
    (∃ s3,
      ReachableExecState multiStepCallerMir hConcrete
        (.running (initMachineStateWithMemory multiStepCallerMir (scalarArgs2 1 1 2) linkedMem))
        (.running s3) ∧
      CalleeTableExcludes s3.memory contractedPath ∧
      stepMirState multiStepCallerMir (.running s3) =
        MirStepNode.extCall
          { defPath := contractedPath, typeArgs := [.uint .u8], args := [],
            memory := s3.memory }
          (resumeExternalCall s3 s3.frame.locals (local_ 0) 4 .continue_)) := by
  intro hConcrete
  have hH : HandlerPreservesTables hConcrete :=
    handlerPreservesTables_linkCalleeWithCalleesHandler _ _ _
      (handlerPreservesTables_linkCalleeWithCalleesHandler _ _ _
        handlerPreservesTables_failAllCalls)
  have hMain := multiStepCaller_reachable_preserves_calleeTableExcludes hConcrete hH
  have hAns :
      ∃ tr, ReachesRet
        (hConcrete { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem })
        tr (.returned (.scalar { bits := 1, sizeBytes := 1 }) linkedMem) := by
    have hEq := linkCalleeWithCalleesHandler_of_defPath_eq helperReturnOneMir []
      (linkCalleeWithCalleesHandler checkedAddU8Mir [] failAllCalls)
      (req := { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem }) rfl
    change ∃ tr, ReachesRet
      (linkCalleeWithCalleesHandler helperReturnOneMir []
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] failAllCalls)
        { defPath := helperPath, typeArgs := [], args := [], memory := linkedMem })
      tr _
    rw [hEq]
    have hDwp :
        DWP mirClosedWP
          (closeMirTreeRestoringFrame linkedMem
            (mirExternalCalleeTree helperReturnOneMir [] linkedMem []))
          (fun ans _ => ans = .returned (.scalar { bits := 1, sizeBytes := 1 }) linkedMem)
          PUnit.unit := by
      unfold closeMirTreeRestoringFrame
      apply DWP.bind
      refine DWP.mono (fun _ _ hEqAns => DWP.ret hEqAns)
        (dwp_interp (ewp₁ := mirNoCallWP) failUnlinkedCalls
          (fun i Q u hwp => by
            cases i with
            | inl _ => exact False.elim hwp
            | inr i' =>
              cases i' with
              | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
              | inr _ => exact False.elim hwp)
          (dwp_cofix_of_wpCoalBounded 4 ?_))
      change wpMirNoCallBounded 4 helperReturnOneMir _ _
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      conv => whnf
      rfl
    obtain ⟨tr, ans, hRet, hEqAns⟩ :=
      exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hDwp
    subst hEqAns
    exact ⟨tr, hRet⟩
  obtain ⟨tr, hRet⟩ := hAns
  exact ⟨hMain.1, hMain.2 tr hRet⟩

/-! ### Non-empty disjoint borrows & Lowering Boundary Gap #8 (depth-0 borrow collision) -/

/--
Disjoint-borrows panic call contract for `checked_add_u8`: allows arbitrary
non-empty `req.memory.borrows` (as well as arbitrary `callees`, `traitImpls`,
`callStack`, `activeCallee`, `activeProtectors`) provided no borrow targets a
local `< 4` in frame `0` (where the isolated callee runs).
-/
def checkedAddU8DisjointBorrowsContract : PanicMirCallContract where
  pre req :=
    req.defPath = checkedAddU8Path ∧ scalarPre2 1 req.args ∧
      ∀ b, b ∈ req.memory.borrows → b.targetFrameDepth ≠ 0 ∨ 4 ≤ b.targetLocal
  post req retVal memAfter :=
    retVal = .scalar { bits := argSum req.args, sizeBytes := 1 } ∧
      ¬ overflows 1 req.args ∧ memAfter = req.memory
  panicCond req := overflows 1 req.args
  panicMemInv req memAfter := memAfter = req.memory

def checkedAddU8DisjointBorrowsMirContract : MirCallContract :=
  checkedAddU8DisjointBorrowsContract.withTraitsPreserved.toMirCallContract

private theorem disableLocalBorrows_eq_self :
    ∀ (borrows : List BorrowEntry) (loc depth : Nat),
      (∀ b, b ∈ borrows → b.targetFrameDepth ≠ depth ∨ b.targetLocal ≠ loc) →
      disableLocalBorrows borrows loc depth = borrows
  | .nil, _, _, _ => rfl
  | entry :: rest, loc, depth, h => by
    unfold disableLocalBorrows
    have hHead := h entry List.mem_cons_self
    have hCond : Bool.and (Nat.beq entry.targetFrameDepth depth)
        (Nat.beq entry.targetLocal loc) = false := by
      rcases hHead with hNeD | hNeL
      · have hF : Nat.beq entry.targetFrameDepth depth = false := by
          cases hB : Nat.beq entry.targetFrameDepth depth with
          | false => rfl
          | true => exact False.elim (hNeD (Nat.eq_of_beq_eq_true hB))
        rw [hF]; rfl
      · have hF : Nat.beq entry.targetLocal loc = false := by
          cases hB : Nat.beq entry.targetLocal loc with
          | false => rfl
          | true => exact False.elim (hNeL (Nat.eq_of_beq_eq_true hB))
        rw [hF, Bool.and_false]
    rw [hCond]
    exact congrArg (entry :: ·)
      (disableLocalBorrows_eq_self rest loc depth
        (fun b hb => h b (List.mem_cons_of_mem entry hb)))

private theorem invalidateConflictingBorrows_eq_self :
    ∀ (borrows : List BorrowEntry) (loc depth : Nat) (writerTag : Option Nat),
      (∀ b, b ∈ borrows → b.targetFrameDepth ≠ depth ∨ b.targetLocal ≠ loc) →
      invalidateConflictingBorrows borrows loc writerTag depth = borrows
  | .nil, _, _, _, _ => rfl
  | entry :: rest, loc, depth, writerTag, h => by
    unfold invalidateConflictingBorrows updateBorrowPerm
    have hHead := h entry List.mem_cons_self
    have hCond : Bool.and (Nat.beq entry.targetFrameDepth depth)
        (Nat.beq entry.targetLocal loc) = false := by
      rcases hHead with hNeD | hNeL
      · have hF : Nat.beq entry.targetFrameDepth depth = false := by
          cases hB : Nat.beq entry.targetFrameDepth depth with
          | false => rfl
          | true => exact False.elim (hNeD (Nat.eq_of_beq_eq_true hB))
        rw [hF]; rfl
      · have hF : Nat.beq entry.targetLocal loc = false := by
          cases hB : Nat.beq entry.targetLocal loc with
          | false => rfl
          | true => exact False.elim (hNeL (Nat.eq_of_beq_eq_true hB))
        rw [hF, Bool.and_false]
    rw [hCond]
    exact congrArg (entry :: ·)
      (invalidateConflictingBorrows_eq_self rest loc depth writerTag
        (fun b hb => h b (List.mem_cons_of_mem entry hb)))

/--
`checked_add_u8` meets `checkedAddU8DisjointBorrowsMirContract` symbolically
over non-empty `borrows` satisfying the disjointness condition (no `borrows = .nil` pin).
-/
theorem checkedAddU8_disjointBorrows_callee_wp (typeArgs : List RigidTy) (a b : Nat)
    (mem : Memory)
    (hDisj : ∀ entry, entry ∈ mem.borrows → entry.targetFrameDepth ≠ 0 ∨ 4 ≤ entry.targetLocal) :
    wpMirNoCallSym 8 checkedAddU8Mir
      (enterExternalCalleeState checkedAddU8Mir (scalarArgs2 1 a b) mem [])
      (fun out =>
        checkedAddU8DisjointBorrowsMirContract.post
          { defPath := checkedAddU8Path, typeArgs := typeArgs, args := scalarArgs2 1 a b,
            memory := mem }
          (outcomeToRestoredCallAns mem out)) := by
  have hDisLocal : disableLocalBorrows mem.borrows 3 0 = mem.borrows :=
    disableLocalBorrows_eq_self mem.borrows 3 0 (fun entry hMem =>
      (hDisj entry hMem).imp id (fun hGe hEq => absurd (hEq ▸ hGe) (by decide)))
  have hDisInv3 : invalidateConflictingBorrows mem.borrows 3 .none 0 = mem.borrows :=
    invalidateConflictingBorrows_eq_self mem.borrows 3 0 .none (fun entry hMem =>
      (hDisj entry hMem).imp id (fun hGe hEq => absurd (hEq ▸ hGe) (by decide)))
  have hDisInv0 : invalidateConflictingBorrows mem.borrows 0 .none 0 = mem.borrows :=
    invalidateConflictingBorrows_eq_self mem.borrows 0 0 .none (fun entry hMem =>
      (hDisj entry hMem).imp id (fun hGe hEq => absurd (hEq ▸ hGe) (by decide)))
  have hDisFrame : disableFrameBorrows mem.borrows 0 4 = mem.borrows :=
    disableFrameBorrows_eq_self mem.borrows 0 4 hDisj
  cases mem with
  | mk nextAllocId globals borrows nextTag callees traitImpls callStack activeCallee
      activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
    simp only at hDisLocal hDisInv3 hDisInv0 hDisFrame
    let memOrig : Memory :=
      { nextAllocId := nextAllocId, globals := globals, borrows := borrows, nextTag := nextTag,
        callees := callees, traitImpls := traitImpls, callStack := callStack,
        activeCallee := activeCallee, activeProtectors := activeProtectors,
        nextProtector := nextProtector, callerLocals := callerLocals, fnPtrs := fnPtrs,
        exposedAllocIds := exposedAllocIds }
    let memCallee : Memory :=
      { nextAllocId := nextAllocId, globals := globals, borrows := borrows, nextTag := nextTag,
        callees := [], traitImpls := traitImpls, callStack := [], activeCallee := .none,
        activeProtectors := [], nextProtector := nextProtector, callerLocals := callerLocals,
        fnPtrs := fnPtrs, exposedAllocIds := exposedAllocIds }
    let l1 : List LocalSlot :=
      [ .uninit, .init (.scalar { bits := a, sizeBytes := 1 })
      , .init (.scalar { bits := b, sizeBytes := 1 }), .uninit ]
    change wpMirExecNoCallSym 7 checkedAddU8Mir
      (.running { frame := { blockIdx := 0, stmtIdx := 1, locals := l1 },
                  memory := { memCallee with borrows := disableLocalBorrows borrows 3 0 } }) _
    rw [hDisLocal]
    rcases borrows with _ | ⟨b1, _ | ⟨b2, rest⟩⟩ <;>
      ((repeat' ((conv => whnf); split)); all_goals (conv => whnf))
    all_goals first
      | (rename_i heq
         exact ⟨(nat_ble_eq_true_iff _ _).1 heq, rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩)
      | (rename_i heq
         have hLt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
         refine ⟨⟨congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
             (wrapScalarBits_of_lt hLt), Nat.not_le.2 hLt, ?_⟩,
           ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
         show { memOrig with
           borrows := disableFrameBorrows
             (invalidateConflictingBorrows
               (invalidateConflictingBorrows _ 3 .none 0) 0 .none 0) 0 4 } = memOrig
         dsimp only [memOrig]
         rw [hDisInv3, hDisInv0, hDisFrame])

/-- `linkCalleeWithCalleesHandler` implements `checkedAddU8DisjointBorrowsMirContract` totally. -/
theorem checkedAddU8_disjointBorrows_holdsTotallyOn (fallback : ExternalCallHandler) :
    checkedAddU8DisjointBorrowsMirContract.holdsTotallyOn
      (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) :=
  holdsTotallyOn_linkCalleeWithCalleesHandler_of_wpMirNoCallSym
    checkedAddU8DisjointBorrowsMirContract checkedAddU8Mir [] fallback 8 (fun _ h => h.1) (by
      rintro ⟨_, typeArgs, _, mem⟩ ⟨rfl, ⟨a, b, -, -, rfl⟩, hDisj⟩
      exact checkedAddU8_disjointBorrows_callee_wp typeArgs a b mem hDisj)

/-- Concrete non-empty borrow table (entries at depth 1 and local 5) accepted by the contract. -/
def nonEmptyDisjointBorrows : List BorrowEntry :=
  [ { tag := 1, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 1 }
  , { tag := 2, targetLocal := 5, targetProjection := [], perm := .active, targetFrameDepth := 0 } ]

theorem checkedAddU8_disjointBorrows_nonEmpty_witness (fallback : ExternalCallHandler) :
    let mem : Memory := { emptyMemory with borrows := nonEmptyDisjointBorrows, nextTag := 3 }
    checkedAddU8DisjointBorrowsMirContract.pre
      { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 1 2, memory := mem } ∧
      DWP mirClosedWP
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback
          { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 1 2, memory := mem })
        (fun ans _ =>
          checkedAddU8DisjointBorrowsMirContract.post
            { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 1 2, memory := mem }
            ans)
        PUnit.unit := by
  intro mem
  have hPre : checkedAddU8DisjointBorrowsMirContract.pre
      { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 1 2, memory := mem } := by
    refine ⟨rfl, ⟨1, 2, by decide, by decide, rfl⟩, ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl (by decide)
    · rcases List.mem_cons.1 hb' with rfl | hb''
      · exact Or.inr (by decide)
      · nomatch hb''
  exact ⟨hPre, checkedAddU8_disjointBorrows_holdsTotallyOn fallback _ hPre⟩

/--
Lowering Boundary Gap #8 (depth-0 frame-borrow collision in `linkCalleeHandler`
and `linkCalleeWithCalleesHandler`):
`fn borrow_caller(x: u8) -> u8 { let r = &x; let _ = checked_add_u8(x, 1); *r }`:
- `bb0`: `storageLive 2; _2 = &_1; storageLive 3; _3 = checked_add_u8(copy _1, const 1) -> bb1`
- `bb1`: `_0 = copy (*_2); return`
-/
def u8SharedRefTy : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 0 }

def borrowCallerMir : CapturedMir :=
  mkBody "panic_tests::borrow_caller" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut u8SharedRefTy, mkDecl .mut u8Ty ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign (local_ 2) (.ref .shared (local_ 1)))
          , mkStmt (.storageLive 3) ]
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), u8Const 1]
            (local_ 3) (.some 1) .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.copy { local_ := 2, projection := [.deref] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Under inlined execution (`callees := [checkedAddU8Mir]`), `checked_add_u8` runs
in a pushed frame at `targetFrameDepth = 1`, so its `return_` teardown does not
touch the caller's depth-0 borrow `&_1`, and `borrow_caller(5)` returns `5`.
-/
theorem borrowCaller_inlined_returns_ok :
    NeverPanics (mirStatefulTrees borrowCallerMir [checkedAddU8Mir])
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 }) ∧
      ∃ tr mem,
        ReachesRet
          (mirStatefulTrees borrowCallerMir [checkedAddU8Mir]
            ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
          tr (.normal (.scalar { bits := 5, sizeBytes := 1 }, mem)) := by
  have hDwp :
      DWP mirDefaultWP
        (mirStatefulTrees borrowCallerMir [checkedAddU8Mir]
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun out _ => ExactPanicOutcome
          (fun r : MirReturn => r.1 = .scalar { bits := 5, sizeBytes := 1 }) False out)
        PUnit.unit := by
    refine dwp_cofix_of_wpCoalBounded 16 ?_
    change wpMirBounded 16 borrowCallerMir _ _
    rw [← wpMirSym_eq_wpMirBounded]
    conv => whnf
    exact ⟨fun h => h, rfl⟩
  have hNever :
      NeverPanics (mirStatefulTrees borrowCallerMir [checkedAddU8Mir])
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 }) := by
    rintro _ rfl
    exact dwlp_pure_adequacy (ewp := mirDefaultWP)
      (DWLP.mono (fun out _ h => h.toPanicOutcomeOk) hDwp.toDWLP)
  obtain ⟨tr, out, hRet, hEx⟩ :=
    exists_reachesRet_of_dwp mirEffect_nonFault_nonempty hDwp
  cases out with
  | normal r =>
    obtain ⟨v, m⟩ := r
    cases (show v = .scalar { bits := 5, sizeBytes := 1 } from hEx.2)
    exact ⟨hNever, tr, m, hRet⟩
  | panic => exact False.elim hEx
  | abort => exact False.elim hEx

/--
Under modular linking through `linkCalleeHandler`, `checked_add_u8` executes at
`callStack = []` (`depth = 0`), colliding with the caller's own frame depth:
`disableFrameBorrows` disables the caller's depth-0 borrow `&_1`, so `*_2`
faults `.ub` and refutes every panic contract.
-/
theorem borrowCaller_linked_handler_ub (fallback : ExternalCallHandler)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    ¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees borrowCallerMir (linkCalleeHandler checkedAddU8Mir fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      post panicCond policy := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let req : MirCallReq :=
    { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 5 1, memory := memCall }
  let memAfter : Memory :=
    { emptyMemory with borrows := [{ b0 with perm := .disabled, allocDead := true }], nextTag := 2 }
  have hAns :
      ∃ tr, ReachesRet (linkCalleeHandler checkedAddU8Mir fallback req) tr
        (.returned (.scalar { bits := 6, sizeBytes := 1 }) memAfter) := by
    rw [linkCalleeHandler_of_defPath_eq checkedAddU8Mir fallback rfl]
    have hDwp :
        DWP mirClosedWP
          (closeMirTreeAsCallAns memCall (mirStatefulTree checkedAddU8Mir (scalarArgs2 1 5 1) memCall))
          (fun ans _ => ans = .returned (.scalar { bits := 6, sizeBytes := 1 }) memAfter)
          PUnit.unit := by
      unfold closeMirTreeAsCallAns
      apply DWP.bind
      refine DWP.mono (fun _ _ hEq => DWP.ret hEq)
        (dwp_interp (ewp₁ := mirNoCallWP) failUnlinkedCalls
          (fun i Q u hwp => by
            cases i with
            | inl _ => exact False.elim hwp
            | inr i' =>
              cases i' with
              | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
              | inr _ => exact False.elim hwp)
          (dwp_cofix_of_wpCoalBounded 8 ?_))
      change wpMirNoCallBounded 8 checkedAddU8Mir _ _
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      conv => whnf
      rfl
    obtain ⟨tr, ans, hRet, hEq⟩ :=
      exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hDwp
    subst hEq
    exact ⟨tr, hRet⟩
  obtain ⟨tr, hAnsRet⟩ := hAns
  exact not_panicsWithPolicyOnlyIf_of_reachesLinkedFault rfl
    (.tau rfl (.tau rfl (.tau rfl (.call rfl hAnsRet (.of_reachesFaultExecBounded _ 4 rfl)))))

/--
The exact same depth-0 borrow collision occurs under `linkCalleeWithCalleesHandler`,
because `enterExternalCalleeState` resets `callStack := []` while retaining
`callerMem.borrows` and `restoreCallerMemoryFrame` does not restore `borrows`.
-/
theorem borrowCaller_linked_withCallees_ub (fallback : ExternalCallHandler)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    ¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees borrowCallerMir (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      post panicCond policy := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let req : MirCallReq :=
    { defPath := checkedAddU8Path, typeArgs := [], args := scalarArgs2 1 5 1, memory := memCall }
  let memAfter : Memory :=
    { emptyMemory with borrows := [{ b0 with perm := .disabled, allocDead := true }], nextTag := 2 }
  have hAns :
      ∃ tr, ReachesRet (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback req) tr
        (.returned (.scalar { bits := 6, sizeBytes := 1 }) memAfter) := by
    rw [linkCalleeWithCalleesHandler_of_defPath_eq checkedAddU8Mir [] fallback rfl]
    have hDwp :
        DWP mirClosedWP
          (closeMirTreeRestoringFrame memCall
            (mirExternalCalleeTree checkedAddU8Mir (scalarArgs2 1 5 1) memCall []))
          (fun ans _ => ans = .returned (.scalar { bits := 6, sizeBytes := 1 }) memAfter)
          PUnit.unit := by
      unfold closeMirTreeRestoringFrame
      apply DWP.bind
      refine DWP.mono (fun _ _ hEq => DWP.ret hEq)
        (dwp_interp (ewp₁ := mirNoCallWP) failUnlinkedCalls
          (fun i Q u hwp => by
            cases i with
            | inl _ => exact False.elim hwp
            | inr i' =>
              cases i' with
              | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
              | inr _ => exact False.elim hwp)
          (dwp_cofix_of_wpCoalBounded 8 ?_))
      change wpMirNoCallBounded 8 checkedAddU8Mir _ _
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      conv => whnf
      rfl
    obtain ⟨tr, ans, hRet, hEq⟩ :=
      exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hDwp
    subst hEq
    exact ⟨tr, hRet⟩
  obtain ⟨tr, hAnsRet⟩ := hAns
  exact not_panicsWithPolicyOnlyIf_of_reachesLinkedFault rfl
    (.tau rfl (.tau rfl (.tau rfl (.call rfl hAnsRet (.of_reachesFaultExecBounded _ 4 rfl)))))

/-- Packaged divergence theorem documenting Lowering Boundary Gap #8. -/
theorem linkCallee_depth0_borrow_collision_divergence (fallback : ExternalCallHandler) :
    (∃ tr mem,
      ReachesRet
        (mirStatefulTrees borrowCallerMir [checkedAddU8Mir]
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 5, sizeBytes := 1 }, mem))) ∧
    (¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees borrowCallerMir (linkCalleeHandler checkedAddU8Mir fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      (fun _ _ => True) (fun _ => True) .waiveAbortUnchecked) ∧
    (¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees borrowCallerMir (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      (fun _ _ => True) (fun _ => True) .waiveAbortUnchecked) :=
  ⟨borrowCaller_inlined_returns_ok.2,
   borrowCaller_linked_handler_ub fallback _ _ _,
   borrowCaller_linked_withCallees_ub fallback _ _ _⟩

/-! ### `linkCalleeBorrowIsolatedHandler` (avoiding Gaps #8 & #9) & Gap #10 (caller-stack reference aliasing) -/

/--
Unrestricted panic call contract for `checked_add_u8` under borrow-isolated
linking: no `borrows = .nil` or borrow-disjointness precondition is needed at all.
-/
def checkedAddU8BorrowIsolatedContract : PanicMirCallContract where
  pre req := req.defPath = checkedAddU8Path ∧ scalarPre2 1 req.args
  post req retVal memAfter :=
    retVal = .scalar { bits := argSum req.args, sizeBytes := 1 } ∧
      ¬ overflows 1 req.args ∧ memAfter = req.memory
  panicCond req := overflows 1 req.args
  panicMemInv req memAfter := memAfter = req.memory

def checkedAddU8BorrowIsolatedMirContract : MirCallContract :=
  checkedAddU8BorrowIsolatedContract.withTraitsPreserved.toMirCallContract

/--
Under `enterBorrowIsolatedCalleeState`, `checked_add_u8` meets its full
frame-and-borrow-preserving contract symbolically for **completely arbitrary**
caller `mem : Memory` (arbitrary `borrows`, `callees`, `traitImpls`, `callStack`,
`activeCallee`, `activeProtectors`).
-/
theorem checkedAddU8_borrowIsolated_callee_wp (typeArgs : List RigidTy) (a b : Nat) (mem : Memory) :
    wpMirNoCallSym 8 checkedAddU8Mir
      (enterBorrowIsolatedCalleeState checkedAddU8Mir (scalarArgs2 1 a b) mem [])
      (fun out =>
        checkedAddU8BorrowIsolatedMirContract.post
          { defPath := checkedAddU8Path, typeArgs := typeArgs, args := scalarArgs2 1 a b,
            memory := mem }
          (outcomeToBorrowIsolatedCallAns mem out)) := by
  cases mem with
  | mk nextAllocId globals borrows nextTag callees traitImpls callStack activeCallee
      activeProtectors nextProtector callerLocals fnPtrs exposedAllocIds =>
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · rename_i heq
      exact ⟨(nat_ble_eq_true_iff _ _).1 heq, rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
    · rename_i heq
      have hlt : a + b < 256 := (nat_ble_eq_false_iff _ _).1 heq
      exact ⟨⟨congrArg (fun n => Value.scalar { bits := n, sizeBytes := 1 })
          (wrapScalarBits_of_lt hlt), Nat.not_le.2 hlt, rfl⟩,
        ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩

/-- `linkCalleeBorrowIsolatedHandler` implements `checkedAddU8BorrowIsolatedMirContract` totally. -/
theorem checkedAddU8_borrowIsolated_holdsTotallyOn (fallback : ExternalCallHandler) :
    checkedAddU8BorrowIsolatedMirContract.holdsTotallyOn
      (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback) :=
  holdsTotallyOn_linkCalleeBorrowIsolatedHandler_of_wpMirNoCallSym
    checkedAddU8BorrowIsolatedMirContract checkedAddU8Mir [] fallback 8 (fun _ h => h.1) (by
      rintro ⟨_, typeArgs, _, mem⟩ ⟨rfl, a, b, -, -, rfl⟩
      exact checkedAddU8_borrowIsolated_callee_wp typeArgs a b mem)

/--
Gap #8 avoided for value-passing callees: `borrowCallerMir` (which faults `.ub`
under both `linkCalleeHandler` and `linkCalleeWithCalleesHandler`) satisfies
`TotalExactPanicContract` and `NeverPanics` and returns `5` under
`linkCalleeBorrowIsolatedHandler`.
-/
theorem borrowCaller_borrowIsolated_neverPanics_and_totalExact (fallback : ExternalCallHandler) :
    TotalExactPanicContract
        (mirHandledTrees borrowCallerMir
          (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback))
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 })
        (fun _ => False) ∧
      NeverPanics
        (mirHandledTrees borrowCallerMir
          (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback))
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 }) := by
  have hTot :
      TotalExactPanicContract
        (mirHandledTrees borrowCallerMir
          (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback))
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 })
        (fun _ => False) :=
    mirHandled_totalExactPanicContract_of_wpMirModularSym checkedAddU8BorrowIsolatedMirContract
      (checkedAddU8_borrowIsolated_holdsTotallyOn fallback) 8 (by
        rintro _ rfl
        let b0 : BorrowEntry :=
          { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen,
            targetFrameDepth := 0 }
        let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
        let lCall : List LocalSlot :=
          [ .uninit, .init (.scalar { bits := 5, sizeBytes := 1 })
          , .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit ]
        let sCall : MachineState :=
          { frame := { blockIdx := 0, stmtIdx := 3, locals := lCall }, memory := memCall }
        change wpMirModularSym checkedAddU8BorrowIsolatedMirContract 5 borrowCallerMir sCall _
        conv => whnf
        refine ⟨⟨rfl, ⟨5, 1, by decide, by decide, rfl⟩⟩, fun ans hPost => ?_⟩
        cases ans with
        | returned retVal memAfter =>
          obtain ⟨⟨hVal, -, hMem⟩, _⟩ := hPost
          subst hVal hMem
          conv => whnf
          exact ⟨fun h => h, rfl⟩
        | panicked memAfter => exact absurd (show 256 ≤ 5 + 1 from hPost.1) (by decide)
        | aborted => exact False.elim hPost)
  exact ⟨hTot, hTot.exact.1⟩

private def borrowCallerAllU8Pre : MirInput → Prop :=
  fun inp => (∃ x, x < 256 ∧ inp.1 = [.scalar { bits := x, sizeBytes := 1 }]) ∧
    inp.2 = emptyMemory

private def borrowCallerAllU8Post : MirInput → MirReturn → Prop :=
  fun inp r => r.1 = .scalar { bits := argBits inp.1 0, sizeBytes := 1 }

private def borrowCallerAllU8Overflows : MirInput → Prop :=
  fun inp => 256 ≤ argBits inp.1 0 + 1

private theorem borrowCaller_inlined_dwp_u8 (x : Nat) :
    DWP mirDefaultWP
      (mirStatefulTrees borrowCallerMir [checkedAddU8Mir]
        ([.scalar { bits := x, sizeBytes := 1 }], emptyMemory))
      (fun out _ => ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := x, sizeBytes := 1 })
        (256 ≤ x + 1) out)
      PUnit.unit := by
  refine dwp_cofix_of_wpCoalBounded 16 ?_
  change wpMirBounded 16 borrowCallerMir _ _
  rw [← wpMirSym_eq_wpMirBounded]
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen,
      targetFrameDepth := 0 }
  let memCallInl : Memory :=
    { emptyMemory with borrows := [b0], nextTag := 2, callees := [checkedAddU8Mir] }
  let lCall : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := x, sizeBytes := 1 })
    , .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit ]
  let sCallInl : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3, locals := lCall }, memory := memCallInl }
  change wpMirSym 13 borrowCallerMir sCallInl _
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rename_i heq
    exact (nat_ble_eq_true_iff _ _).1 heq
  · rename_i heq
    exact ⟨Nat.not_le.2 ((nat_ble_eq_false_iff _ _).1 heq), rfl⟩

private theorem borrowCaller_borrowIsolated_modular_wp_u8 (x : Nat) (hx : x < 256) :
    wpMirModularSym checkedAddU8BorrowIsolatedMirContract 8 borrowCallerMir
      (initMachineStateWithMemoryAndCallees borrowCallerMir
        [.scalar { bits := x, sizeBytes := 1 }] emptyMemory [])
      (ExactPanicOutcome
        (fun r : MirReturn => r.1 = .scalar { bits := x, sizeBytes := 1 })
        (256 ≤ x + 1)) := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen,
      targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let lCall : List LocalSlot :=
    [ .uninit, .init (.scalar { bits := x, sizeBytes := 1 })
    , .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit ]
  let sCall : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3, locals := lCall }, memory := memCall }
  change wpMirModularSym checkedAddU8BorrowIsolatedMirContract 5 borrowCallerMir sCall _
  conv => whnf
  refine ⟨⟨rfl, ⟨x, 1, hx, by decide, rfl⟩⟩, fun ans hPost => ?_⟩
  cases ans with
  | returned retVal memAfter =>
    obtain ⟨⟨hVal, hFit, hMem⟩, _⟩ := hPost
    subst hVal hMem
    conv => whnf
    exact ⟨hFit, rfl⟩
  | panicked memAfter =>
    obtain ⟨hOver, hMem, _⟩ := hPost
    subst hMem
    conv => whnf
    exact hOver
  | aborted => exact False.elim hPost

/--
Universal 256-input exact panic contract for inlined `borrowCallerMir`: for
every `x < 256`, `borrow_caller(x)` returns `x` when `x < 255` and panics on
overflow when `x = 255`.
-/
theorem borrowCaller_inlined_totalExact_all_u8 :
    TotalExactPanicContract (mirStatefulTrees borrowCallerMir [checkedAddU8Mir])
      borrowCallerAllU8Pre borrowCallerAllU8Post borrowCallerAllU8Overflows :=
  totalExactPanicContract_of_dwp mirEffect_nonFault_nonempty (by
    rintro ⟨_, _⟩ ⟨⟨x, _, rfl⟩, rfl⟩
    exact borrowCaller_inlined_dwp_u8 x)

/--
Universal 256-input exact panic contract for `borrowCallerMir` linked through
`linkCalleeBorrowIsolatedHandler`, matching `borrowCaller_inlined_totalExact_all_u8`
on every normal and panicking input (`x < 256`).
-/
theorem borrowCaller_borrowIsolated_totalExact_all_u8 (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees borrowCallerMir
        (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback))
      borrowCallerAllU8Pre borrowCallerAllU8Post borrowCallerAllU8Overflows :=
  mirHandled_totalExactPanicContract_of_wpMirModularSym checkedAddU8BorrowIsolatedMirContract
    (checkedAddU8_borrowIsolated_holdsTotallyOn fallback) 8 (by
      rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, rfl⟩
      exact borrowCaller_borrowIsolated_modular_wp_u8 x hx)

/--
Cross-effect `ExactPass` behavioral adequacy on `borrowCallerMir` across all 256
valid `u8` inputs (`x : Fin 256`, covering both normal returns `x < 255` and
overflow panics `x = 255`): value-projected `linkCalleeBorrowIsolatedHandler`
execution (`MirClosedEffect`) is `ExactPass`-equivalent to inlined execution
(`MirEffect`). Note that this adequacy is established for this value-passing
caller/callee pair, not for callees dereferencing caller stack references
(Gap #10) or mutating `&mut` memory before panicking (Gap #1).
-/
theorem borrowCaller_borrowIsolated_vs_inlined_exactPass_all_u8
    (fallback : ExternalCallHandler) :
    ExactPass
      (panicSemantics (EffectObs.erase MirEffect PUnit)
        (fun body (x : Fin 256) =>
          projectMirOutcomeValue
            (mirStatefulTrees body [checkedAddU8Mir]
              ([.scalar { bits := x.val, sizeBytes := 1 }], emptyMemory))))
      (panicSemantics (EffectObs.erase MirClosedEffect PUnit)
        (fun body (x : Fin 256) =>
          projectMirOutcomeValue
            (mirHandledTrees body
              (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback) []
              ([.scalar { bits := x.val, sizeBytes := 1 }], emptyMemory))))
      id id borrowCallerMir borrowCallerMir := by
  refine exactPass_erase_of_same_unique_outcome (fun x => ?_)
  let targetOut : Outcome Value :=
    if 256 ≤ x.val + 1 then .panic else .normal (.scalar { bits := x.val, sizeBytes := 1 })
  have hExactToTarget : ∀ out : MirOutcome,
      ExactPanicOutcome (fun r : MirReturn => r.1 = .scalar { bits := x.val, sizeBytes := 1 })
        (256 ≤ x.val + 1) out →
      mirOutcomeValue out = targetOut := by
    intro out hEx
    cases out with
    | normal r =>
      obtain ⟨hNotOver, hVal⟩ := hEx
      simp only [targetOut, mirOutcomeValue, hNotOver, ↓reduceIte, hVal]
    | panic =>
      have hP : 256 ≤ x.val + 1 := hEx
      simp only [targetOut, mirOutcomeValue, hP, ↓reduceIte]
    | abort => exact False.elim hEx
  have hDwpInl :
      DWP mirDefaultWP
        (mirStatefulTrees borrowCallerMir [checkedAddU8Mir]
          ([.scalar { bits := x.val, sizeBytes := 1 }], emptyMemory))
        (fun out _ => mirOutcomeValue out = targetOut) PUnit.unit :=
    DWP.mono (fun out _ hEx => hExactToTarget out hEx)
      (borrowCaller_inlined_dwp_u8 x.val)
  have hDwpIso :
      DWP mirClosedWP
        (mirHandledTrees borrowCallerMir
          (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback) []
          ([.scalar { bits := x.val, sizeBytes := 1 }], emptyMemory))
        (fun out _ => mirOutcomeValue out = targetOut) PUnit.unit :=
    DWP.mono (fun out _ hEx => hExactToTarget out hEx)
      (dwp_interp (ewp₁ := mirModularWP checkedAddU8BorrowIsolatedMirContract.toCallContract)
        (handleMirExternalCalls
          (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback))
        (fun i Q u hwp => by
          cases i with
          | inl _ => exact False.elim hwp
          | inr i' =>
            cases i' with
            | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
            | inr req =>
              cases req with
              | call r =>
                exact DWP.mono (fun ans _ hPost => hwp.2 ans hPost)
                  (checkedAddU8_borrowIsolated_holdsTotallyOn fallback r hwp.1))
        (dwp_of_wpMirModularSym (borrowCaller_borrowIsolated_modular_wp_u8 x.val x.isLt)))
  obtain ⟨hs₁, hr₁, hu₁⟩ :=
    projectMirOutcomeValue_unique_of_dwp mirEffect_nonFault_nonempty hDwpInl
  obtain ⟨hs₂, hr₂, hu₂⟩ :=
    projectMirOutcomeValue_unique_of_dwp mirClosedEffect_nonFault_nonempty hDwpIso
  exact ⟨targetOut, hs₁, hr₁, hu₁, hs₂, hr₂, hu₂⟩

/--
Gap #9 also avoided: `outerCallerMir` with linked helper `[midHelperMir]`
satisfies `TotalExactPanicContract` under `linkCalleeBorrowIsolatedHandler`.
-/
theorem outerCaller_borrowIsolated_totalExact (fallback : ExternalCallHandler) :
    TotalExactPanicContract
      (mirHandledTrees outerCallerMir
        (linkCalleeBorrowIsolatedHandler checkedAddU8Mir [] fallback) [midHelperMir])
      addCallerPre addCallerPost addCallerOverflows :=
  mirHandled_totalExactPanicContract_of_wpMirModularSym checkedAddU8BorrowIsolatedMirContract
    (checkedAddU8_borrowIsolated_holdsTotallyOn fallback) 16 (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩⟩, fun ans hPost => ?_⟩
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
      | aborted => exact False.elim hPost)

/--
Lowering Boundary Gap #10 (caller-stack reference local-index aliasing due to
`MirCallReq` omitting caller `StackFrame.locals`):
- `fn read_ref(y: u8, r: &u8) -> u8 { *r }` (`_1: u8`, `_2: &u8`)
- `fn ref_caller(x: u8) -> u8 { let r = &x; read_ref(99, r) }` (`_1: u8`, `_2: &u8`)
-/
def readRefPath : DefPath := "panic_tests::read_ref"

def readRefMir : CapturedMir :=
  mkBody readRefPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8SharedRefTy ]
    [ { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.copy { local_ := 2, projection := [.deref] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def refCallerMir : CapturedMir :=
  mkBody "panic_tests::ref_caller" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut u8SharedRefTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))) ]
        terminator :=
          mkTerm (.call (fnItemOp readRefPath) [u8Const 99, .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/--
Under inlined execution (`callees := [readRefMir]`), `callStack` saves the
caller's depth-0 frame, so `*_2` resolves via `foreignFrameSlot?` to the
caller's `_1 = 5`, and `ref_caller(5)` returns `.scalar 5`.
-/
theorem refCaller_inlined_returns_5 :
    NeverPanics (mirStatefulTrees refCallerMir [readRefMir])
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 }) ∧
      ∃ tr mem,
        ReachesRet
          (mirStatefulTrees refCallerMir [readRefMir]
            ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
          tr (.normal (.scalar { bits := 5, sizeBytes := 1 }, mem)) := by
  have hDwp :
      DWP mirDefaultWP
        (mirStatefulTrees refCallerMir [readRefMir]
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun out _ => ExactPanicOutcome
          (fun r : MirReturn => r.1 = .scalar { bits := 5, sizeBytes := 1 }) False out)
        PUnit.unit := by
    refine dwp_cofix_of_wpCoalBounded 12 ?_
    change wpMirBounded 12 refCallerMir _ _
    rw [← wpMirSym_eq_wpMirBounded]
    conv => whnf
    exact ⟨fun h => h, rfl⟩
  have hNever :
      NeverPanics (mirStatefulTrees refCallerMir [readRefMir])
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 }) := by
    rintro _ rfl
    exact dwlp_pure_adequacy (ewp := mirDefaultWP)
      (DWLP.mono (fun out _ h => h.toPanicOutcomeOk) hDwp.toDWLP)
  obtain ⟨tr, out, hRet, hEx⟩ :=
    exists_reachesRet_of_dwp mirEffect_nonFault_nonempty hDwp
  cases out with
  | normal r =>
    obtain ⟨v, m⟩ := r
    cases (show v = .scalar { bits := 5, sizeBytes := 1 } from hEx.2)
    exact ⟨hNever, tr, m, hRet⟩
  | panic => exact False.elim hEx
  | abort => exact False.elim hEx

/--
Gap #10 under `linkCalleeHandler`: because `MirCallReq` omits the caller's
`StackFrame.locals`, `read_ref` runs at `callStack = []` (`depth = 0`) with
`callerMem.borrows`. When `read_ref` executes `*_2`, `activeFrameSlot?` matches
`entry.targetLocal = 1` against the *callee's* own `u8` parameter `_1 = 99`
(passing every typed dereference check in `evalStackThinPtrTypedDerefRead`), so
`ref_caller(5)` **silently returns `99` instead of `5`** without faulting and
refutes `PanicsOnlyIf` for `r.1 = .scalar 5`.
-/
theorem refCaller_linkCallee_silent_local_aliasing (fallback : ExternalCallHandler) :
    (∃ tr mem,
      ReachesRet
        (mirHandledTrees refCallerMir (linkCalleeHandler readRefMir fallback) []
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 99, sizeBytes := 1 }, mem))) ∧
      ¬ PanicsOnlyIf (mirHandledTrees refCallerMir (linkCalleeHandler readRefMir fallback))
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 })
        (fun _ => False) := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let ptrVal : Value := .ptr { allocId := 1, offsetBytes := 0 } 8
  let callArgs : List Value := [.scalar { bits := 99, sizeBytes := 1 }, ptrVal]
  let req : MirCallReq :=
    { defPath := readRefPath, typeArgs := [], args := callArgs, memory := memCall }
  let memAfter : Memory :=
    { emptyMemory with borrows := [{ b0 with perm := .disabled, allocDead := true }], nextTag := 2 }
  have hAns :
      ∃ tr, ReachesRet (linkCalleeHandler readRefMir fallback req) tr
        (.returned (.scalar { bits := 99, sizeBytes := 1 }) memAfter) := by
    rw [linkCalleeHandler_of_defPath_eq readRefMir fallback rfl]
    have hDwp :
        DWP mirClosedWP
          (closeMirTreeAsCallAns memCall (mirStatefulTree readRefMir callArgs memCall))
          (fun ans _ => ans = .returned (.scalar { bits := 99, sizeBytes := 1 }) memAfter)
          PUnit.unit := by
      unfold closeMirTreeAsCallAns
      apply DWP.bind
      refine DWP.mono (fun _ _ hEq => DWP.ret hEq)
        (dwp_interp (ewp₁ := mirNoCallWP) failUnlinkedCalls
          (fun i Q u hwp => by
            cases i with
            | inl _ => exact False.elim hwp
            | inr i' =>
              cases i' with
              | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
              | inr _ => exact False.elim hwp)
          (dwp_cofix_of_wpCoalBounded 4 ?_))
      change wpMirNoCallBounded 4 readRefMir _ _
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      conv => whnf
      rfl
    obtain ⟨tr, ans, hRet, hEq⟩ :=
      exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hDwp
    subst hEq
    exact ⟨tr, hRet⟩
  obtain ⟨tr, hAnsRet⟩ := hAns
  have hOut :
      ReachesLinkedOutcome refCallerMir (linkCalleeHandler readRefMir fallback)
        (.running (initMachineStateWithMemoryAndCallees refCallerMir
          [.scalar { bits := 5, sizeBytes := 1 }] emptyMemory []))
        (.normal (.scalar { bits := 99, sizeBytes := 1 }, memAfter)) :=
    .tau rfl (.tau rfl (.call rfl hAnsRet (.ret rfl)))
  refine ⟨?_, ?_⟩
  · obtain ⟨tr', hRet'⟩ := hOut.exists_reachesRet
    exact ⟨tr', memAfter, hRet'⟩
  · exact not_panicsOnlyIf_of_reachesLinkedOutcome rfl hOut (fun hEq => by
      have hBits := congrArg (fun v => match v with | Value.scalar s => s.bits | _ => 0) hEq
      exact absurd hBits (by decide))

/--
Gap #10 under `linkCalleeWithCalleesHandler`: the identical silent wrong-value
return (`99` instead of `5`) occurs, because `enterExternalCalleeState` retains
`callerMem.borrows` at `callStack = []`.
-/
theorem refCaller_linkCalleeWithCallees_silent_local_aliasing (fallback : ExternalCallHandler) :
    (∃ tr mem,
      ReachesRet
        (mirHandledTrees refCallerMir (linkCalleeWithCalleesHandler readRefMir [] fallback) []
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 99, sizeBytes := 1 }, mem))) ∧
      ¬ PanicsOnlyIf
        (mirHandledTrees refCallerMir (linkCalleeWithCalleesHandler readRefMir [] fallback))
        (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        (fun _ r => r.1 = .scalar { bits := 5, sizeBytes := 1 })
        (fun _ => False) := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let ptrVal : Value := .ptr { allocId := 1, offsetBytes := 0 } 8
  let callArgs : List Value := [.scalar { bits := 99, sizeBytes := 1 }, ptrVal]
  let req : MirCallReq :=
    { defPath := readRefPath, typeArgs := [], args := callArgs, memory := memCall }
  let memAfter : Memory :=
    { emptyMemory with borrows := [{ b0 with perm := .disabled, allocDead := true }], nextTag := 2 }
  have hAns :
      ∃ tr, ReachesRet (linkCalleeWithCalleesHandler readRefMir [] fallback req) tr
        (.returned (.scalar { bits := 99, sizeBytes := 1 }) memAfter) := by
    rw [linkCalleeWithCalleesHandler_of_defPath_eq readRefMir [] fallback rfl]
    have hDwp :
        DWP mirClosedWP
          (closeMirTreeRestoringFrame memCall
            (mirExternalCalleeTree readRefMir callArgs memCall []))
          (fun ans _ => ans = .returned (.scalar { bits := 99, sizeBytes := 1 }) memAfter)
          PUnit.unit := by
      unfold closeMirTreeRestoringFrame
      apply DWP.bind
      refine DWP.mono (fun _ _ hEq => DWP.ret hEq)
        (dwp_interp (ewp₁ := mirNoCallWP) failUnlinkedCalls
          (fun i Q u hwp => by
            cases i with
            | inl _ => exact False.elim hwp
            | inr i' =>
              cases i' with
              | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
              | inr _ => exact False.elim hwp)
          (dwp_cofix_of_wpCoalBounded 4 ?_))
      change wpMirNoCallBounded 4 readRefMir _ _
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      conv => whnf
      rfl
    obtain ⟨tr, ans, hRet, hEq⟩ :=
      exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty hDwp
    subst hEq
    exact ⟨tr, hRet⟩
  obtain ⟨tr, hAnsRet⟩ := hAns
  have hOut :
      ReachesLinkedOutcome refCallerMir (linkCalleeWithCalleesHandler readRefMir [] fallback)
        (.running (initMachineStateWithMemoryAndCallees refCallerMir
          [.scalar { bits := 5, sizeBytes := 1 }] emptyMemory []))
        (.normal (.scalar { bits := 99, sizeBytes := 1 }, memAfter)) :=
    .tau rfl (.tau rfl (.call rfl hAnsRet (.ret rfl)))
  refine ⟨?_, ?_⟩
  · obtain ⟨tr', hRet'⟩ := hOut.exists_reachesRet
    exact ⟨tr', memAfter, hRet'⟩
  · exact not_panicsOnlyIf_of_reachesLinkedOutcome rfl hOut (fun hEq => by
      have hBits := congrArg (fun v => match v with | Value.scalar s => s.bits | _ => 0) hEq
      exact absurd hBits (by decide))

/--
Under `linkCalleeBorrowIsolatedHandler`, dereferencing a caller stack reference
**fails closed** (`.ub`) rather than silently reading the callee's own local
frame, refuting every `PanicsWithPolicyOnlyIf` contract (even under
`.waiveAbortUnchecked`).
-/
theorem refCaller_borrowIsolated_fails_closed_ub (fallback : ExternalCallHandler)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    ¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees refCallerMir (linkCalleeBorrowIsolatedHandler readRefMir [] fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      post panicCond policy := by
  let b0 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }
  let memCall : Memory := { emptyMemory with borrows := [b0], nextTag := 2 }
  let ptrVal : Value := .ptr { allocId := 1, offsetBytes := 0 } 8
  let callArgs : List Value := [.scalar { bits := 99, sizeBytes := 1 }, ptrVal]
  let req : MirCallReq :=
    { defPath := readRefPath, typeArgs := [], args := callArgs, memory := memCall }
  have hNotSafe : ¬ TreeSafe (linkCalleeBorrowIsolatedHandler readRefMir [] fallback req) := by
    rw [linkCalleeBorrowIsolatedHandler_of_defPath_eq readRefMir [] fallback rfl]
    unfold closeMirTreeBorrowIsolated
    refine not_treeSafe_bind _ ?_
    have hF :
        ReachesLinkedFault readRefMir failAllCalls
          (.running (enterBorrowIsolatedCalleeState readRefMir callArgs memCall [])) :=
      .of_reachesFaultExecBounded _ 4 rfl
    have hT := hF.not_treeSafe
    unfold mirHandledFrom at hT
    rw [← failUnlinkedCalls_eq_handleMirExternalCalls] at hT
    exact hT
  exact not_panicsWithPolicyOnlyIf_of_reachesLinkedFault rfl
    (.tau rfl (.tau rfl (.handler rfl hNotSafe)))

/--
Packaged three-way divergence theorem characterizing Lowering Boundary Gap #10
(`MirCallReq` omitting caller `StackFrame.locals`):
1. Inlined execution returns `.scalar 5`.
2. `linkCalleeHandler` and `linkCalleeWithCalleesHandler` silently read the
   callee's own `_1 = 99` and return `.scalar 99`.
3. `linkCalleeBorrowIsolatedHandler` fails closed (`.ub`).
-/
theorem refCaller_threeWay_lowering_divergence (fallback : ExternalCallHandler) :
    (∃ tr mem,
      ReachesRet
        (mirStatefulTrees refCallerMir [readRefMir]
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 5, sizeBytes := 1 }, mem))) ∧
    (∃ tr mem,
      ReachesRet
        (mirHandledTrees refCallerMir (linkCalleeHandler readRefMir fallback) []
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 99, sizeBytes := 1 }, mem))) ∧
    (∃ tr mem,
      ReachesRet
        (mirHandledTrees refCallerMir (linkCalleeWithCalleesHandler readRefMir [] fallback) []
          ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
        tr (.normal (.scalar { bits := 99, sizeBytes := 1 }, mem))) ∧
    (¬ PanicsWithPolicyOnlyIf
      (mirHandledTrees refCallerMir (linkCalleeBorrowIsolatedHandler readRefMir [] fallback))
      (fun x => x = ([.scalar { bits := 5, sizeBytes := 1 }], emptyMemory))
      (fun _ _ => True) (fun _ => True) .waiveAbortUnchecked) :=
  ⟨refCaller_inlined_returns_5.2,
   (refCaller_linkCallee_silent_local_aliasing fallback).1,
   (refCaller_linkCalleeWithCallees_silent_local_aliasing fallback).1,
   refCaller_borrowIsolated_fails_closed_ub fallback _ _ _⟩

/-! ### CFG-reachable & counted transitive call-boundary guards + path-feasibility limit -/

/--
`CallSitesPreserved` accepts the dead-block decoy `addCallerInlinedDeadCallMir`,
whereas both `ReachableCallBoundaryPreserved` and `ReachableCallSitesPreserved`
reject it because the decoy block `bb2` is not CFG-reachable from `bb0`.
-/
theorem addCallerInlinedDeadCall_rejected_by_reachableGuards :
    CallSitesPreserved addCallerInlinedDeadCallMir [] checkedAddU8Path 1 ∧
      ¬ ReachableCallBoundaryPreserved addCallerInlinedDeadCallMir [] checkedAddU8Path ∧
      ¬ ReachableCallSitesPreserved addCallerInlinedDeadCallMir [] checkedAddU8Path 1 :=
  ⟨(callSitesPreserved_iff _ _ _ _).1 rfl,
   not_reachableCallBoundaryPreserved_of_zero_reachable_sites rfl,
   not_reachableCallSitesPreserved_of_count_ne (by decide)⟩

/--
Path-infeasible decoy: `bb0: switchInt(const 0u8) -> [1: bb3 (decoy call), otherwise: bb1 (inlined)]`.
Static CFG reachability includes `bb3`, yet `bb3` is dynamically unreachable.
-/
def addCallerInlinedFalseBranchDecoyMir : CapturedMir :=
  mkBody "panic_tests::add_caller_false_decoy" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut u8CheckedTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (u8Const 0) { branches := [(1, 3)], otherwise := 1 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign (local_ 3)
              (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolTy] }) false 2 .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign (local_ 0)
              (.use (.move { local_ := 3, projection := [.field 0 u8Ty] }))) ]
        terminator := mkTerm .return_
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 2) .continue_)
        isCleanup := false } ]

/--
Exact semantic boundary between static CFG reachability and dynamic path
feasibility: `ReachableCallBoundaryPreserved` and `ReachableCallSitesPreserved`
accept `addCallerInlinedFalseBranchDecoyMir` (`bb3` is CFG-reachable), yet
under `wpMirNoCallSym` the body never invokes `checked_add_u8` on any input.
-/
theorem addCallerInlinedFalseBranchDecoy_reachable_yet_never_calls :
    ReachableCallBoundaryPreserved addCallerInlinedFalseBranchDecoyMir [] checkedAddU8Path ∧
      ReachableCallSitesPreserved addCallerInlinedFalseBranchDecoyMir [] checkedAddU8Path 1 ∧
      ∀ a b,
        wpMirNoCallSym 8 addCallerInlinedFalseBranchDecoyMir
          (initMachineStateWithCallees addCallerInlinedFalseBranchDecoyMir (scalarArgs2 1 a b) [])
          (fun _ => True) := by
  refine ⟨(reachableCallBoundaryPreserved_iff _ _ _).1 rfl,
    (reachableCallSitesPreserved_iff _ _ _ _).1 rfl, fun a b => ?_⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals trivial

def twoSiteMidHelperPath : DefPath := "panic_tests::two_site_mid_helper"

def twoSiteMidHelperMir : CapturedMir :=
  { twoSiteCallerMir with defPath := twoSiteMidHelperPath }

def twoSiteMidHelperHalfInlinedMir : CapturedMir :=
  { twoSiteHalfInlinedMir with defPath := twoSiteMidHelperPath }

def outerTwoSiteCallerMir : CapturedMir :=
  mkBody "panic_tests::outer_two_site" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp twoSiteMidHelperPath) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- Counted transitive guard accepts the intact two-site helper and yields `CalleeTableExcludes`. -/
theorem outerTwoSiteCaller_calleesCallSitesPreserved (args : List Value) (mem : Memory) :
    CalleesCallSitesPreserved outerTwoSiteCallerMir [twoSiteMidHelperMir]
        [(twoSiteMidHelperPath, 2)] checkedAddU8Path ∧
      CalleeTableExcludes
        (initMachineStateWithMemoryAndCallees outerTwoSiteCallerMir args mem
          [twoSiteMidHelperMir]).memory
        checkedAddU8Path :=
  let h : CalleesCallSitesPreserved outerTwoSiteCallerMir [twoSiteMidHelperMir]
      [(twoSiteMidHelperPath, 2)] checkedAddU8Path :=
    (calleesCallSitesPreserved_iff _ _ _ _).1 rfl
  ⟨h, h.calleeTableExcludes_initStateful_of_ne_nil (by simp) args mem⟩

/--
Partial inlining inside a transitive helper: `CalleesCallBoundaryPreserved`
accepts `twoSiteMidHelperHalfInlinedMir`, while `CalleesCallSitesPreserved`
rejects it because its call-site count dropped from `2` to `1`.
-/
theorem outerTwoSiteHalfInlined_calleesCallBoundary_not_callSites :
    CalleesCallBoundaryPreserved outerTwoSiteCallerMir [twoSiteMidHelperHalfInlinedMir]
        [twoSiteMidHelperPath] checkedAddU8Path ∧
      ¬ CalleesCallSitesPreserved outerTwoSiteCallerMir [twoSiteMidHelperHalfInlinedMir]
        [(twoSiteMidHelperPath, 2)] checkedAddU8Path :=
  ⟨(calleesCallBoundaryPreserved_iff _ _ _ _).1 rfl,
   not_calleesCallSitesPreserved_of_count_ne
     (body := twoSiteMidHelperHalfInlinedMir) (p := (twoSiteMidHelperPath, 2))
     List.mem_cons_self List.mem_cons_self rfl (by decide)⟩

/--
Transitive helper with an unreachable dead-block call decoy: `bb0`/`bb1` inline
`checked_add_u8` directly, while unreachable `bb2` carries a decoy call to
`checked_add_u8`.
-/
def midHelperInlinedDeadCallMir : CapturedMir :=
  mkBody midHelperPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty, mkDecl .mut u8CheckedTy ]
    (checkedAddBlocks u8Ty .continue_ ++
      [ { statements := []
          terminator :=
            mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
              (local_ 0) (.some 1) .continue_)
          isCleanup := false } ])

/--
Dead-block decoy inside a transitive helper: both syntactic transitive guards
(`CalleesCallBoundaryPreserved` and `CalleesCallSitesPreserved`) are fooled by
`midHelperInlinedDeadCallMir`, whereas both CFG-reachable transitive guards
(`ReachableCalleesCallBoundaryPreserved` and `ReachableCalleesCallSitesPreserved`)
reject it.
-/
theorem outerCaller_deadDecoyHelper_passes_syntactic_rejected_by_reachable :
    CalleesCallBoundaryPreserved outerCallerMir [midHelperInlinedDeadCallMir]
        [midHelperPath] checkedAddU8Path ∧
      CalleesCallSitesPreserved outerCallerMir [midHelperInlinedDeadCallMir]
        [(midHelperPath, 1)] checkedAddU8Path ∧
      ¬ ReachableCalleesCallBoundaryPreserved outerCallerMir [midHelperInlinedDeadCallMir]
        [midHelperPath] checkedAddU8Path ∧
      ¬ ReachableCalleesCallSitesPreserved outerCallerMir [midHelperInlinedDeadCallMir]
        [(midHelperPath, 1)] checkedAddU8Path :=
  ⟨(calleesCallBoundaryPreserved_iff _ _ _ _).1 rfl,
   (calleesCallSitesPreserved_iff _ _ _ _).1 rfl,
   not_reachableCalleesCallBoundaryPreserved_of_zero_reachable_sites
     (body := midHelperInlinedDeadCallMir) List.mem_cons_self List.mem_cons_self rfl,
   not_reachableCalleesCallSitesPreserved_of_count_ne
     (body := midHelperInlinedDeadCallMir) (p := (midHelperPath, 1))
     List.mem_cons_self List.mem_cons_self rfl (by decide)⟩

/-- Positive counted CFG-reachable transitive guard on `outerTwoSiteCallerMir`. -/
theorem outerTwoSiteCaller_reachableCalleesCallSitesPreserved
    (args : List Value) (mem : Memory) :
    ReachableCalleesCallSitesPreserved outerTwoSiteCallerMir [twoSiteMidHelperMir]
        [(twoSiteMidHelperPath, 2)] checkedAddU8Path ∧
      CalleeTableExcludes
        (initMachineStateWithMemoryAndCallees outerTwoSiteCallerMir args mem
          [twoSiteMidHelperMir]).memory
        checkedAddU8Path :=
  let h : ReachableCalleesCallSitesPreserved outerTwoSiteCallerMir [twoSiteMidHelperMir]
      [(twoSiteMidHelperPath, 2)] checkedAddU8Path :=
    (reachableCalleesCallSitesPreserved_iff _ _ _ _).1 rfl
  ⟨h, h.calleeTableExcludes_initStateful_of_ne_nil (by simp) args mem⟩

/-! ### Helper chains: the caller must still call the helper -/

/--
`outer_caller` after pre-capture inlining of both its call to `mid_helper` and
`mid_helper`'s call to `checked_add_u8`: the checked addition sits directly in
the caller, and no call to either path remains.
-/
def outerCallerFullyInlinedMir : CapturedMir :=
  checkedAddMir "panic_tests::outer_caller" u8Ty u8CheckedTy .continue_

/--
The four guards over `callees` accept the fully inlined caller, because the
linked helper still contains its call to `checked_add_u8`. The helper-chain guard
rejects it: the caller no longer calls the helper, and it has no call to the
target either.
-/
theorem outerCallerFullyInlined_fools_callees_guards :
    CalleesCallBoundaryPreserved outerCallerFullyInlinedMir [midHelperMir] [midHelperPath]
        checkedAddU8Path ∧
      CalleesCallSitesPreserved outerCallerFullyInlinedMir [midHelperMir] [(midHelperPath, 1)]
        checkedAddU8Path ∧
      ReachableCalleesCallBoundaryPreserved outerCallerFullyInlinedMir [midHelperMir]
        [midHelperPath] checkedAddU8Path ∧
      ReachableCalleesCallSitesPreserved outerCallerFullyInlinedMir [midHelperMir]
        [(midHelperPath, 1)] checkedAddU8Path ∧
      ¬ HelperChainCallBoundaryPreserved outerCallerFullyInlinedMir [midHelperMir]
        midHelperPath checkedAddU8Path ∧
      ¬ BodyCallsDefPath checkedAddU8Path outerCallerFullyInlinedMir := by
  refine ⟨(calleesCallBoundaryPreserved_iff _ _ _ _).1 rfl,
    (calleesCallSitesPreserved_iff _ _ _ _).1 rfl,
    (reachableCalleesCallBoundaryPreserved_iff _ _ _ _).1 rfl,
    (reachableCalleesCallSitesPreserved_iff _ _ _ _).1 rfl,
    not_helperChainCallBoundaryPreserved_of_not_callsHelper rfl, fun h => ?_⟩
  have hT := (bodyCallsDefPath_iff _ _).2 h
  rw [show bodyCallsDefPath checkedAddU8Path outerCallerFullyInlinedMir = false from rfl] at hT
  nomatch hT

/-- The helper-chain guard accepts the caller that keeps both calls, and yields the runtime guard. -/
theorem outerCaller_helperChainCallBoundaryPreserved :
    HelperChainCallBoundaryPreserved outerCallerMir [midHelperMir] midHelperPath
        checkedAddU8Path ∧
      ∀ args, CalleeTableExcludes
        (initMachineStateWithCallees outerCallerMir args [midHelperMir]).memory
        checkedAddU8Path :=
  have h : HelperChainCallBoundaryPreserved outerCallerMir [midHelperMir] midHelperPath
      checkedAddU8Path := (helperChainCallBoundaryPreserved_iff _ _ _ _).1 rfl
  ⟨h, h.calleeTableExcludes_init⟩

/--
The guard rejects a chain whose helper was inlined: with `midHelperInlinedMir`
linked, the helper has no call to the target.
-/
theorem outerCaller_inlinedHelper_not_helperChain :
    ¬ HelperChainCallBoundaryPreserved outerCallerMir [midHelperInlinedMir] midHelperPath
      checkedAddU8Path := fun h => by
  have hT := (helperChainCallBoundaryPreserved_iff _ _ _ _).2 h
  rw [show helperChainCallBoundaryPreserved outerCallerMir [midHelperInlinedMir] midHelperPath
    checkedAddU8Path = false from rfl] at hT
  nomatch hT

/-- Multi-hop chain fixtures: `grand_caller -> outer_mid -> mid_helper -> checked_add_u8`. -/
def outerMidPath : DefPath := "panic_tests::outer_mid"

def outerMidMir : CapturedMir :=
  mkBody outerMidPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp midHelperPath) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

def outerMidInlinedMir : CapturedMir :=
  mkBody outerMidPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

def grandCallerMir : CapturedMir :=
  mkBody "panic_tests::grand_caller" 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp outerMidPath) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/--
Single-hop `HelperChainCallBoundaryPreserved` cannot verify intermediate linked
hops of a multi-hop chain because `notLinked` forbids its target (`midHelperPath`)
from appearing in `callees`.
-/
theorem grandCaller_twoHop_helperChain_fails_on_linked_hop :
    ¬ HelperChainCallBoundaryPreserved grandCallerMir [outerMidMir, midHelperMir]
      outerMidPath midHelperPath := fun h => by
  have hF := h.notLinked
  rw [show findCallee? [outerMidMir, midHelperMir] midHelperPath = .some midHelperMir from rfl] at hF
  nomatch hF

/--
Arbitrary-length `CallChainCallBoundaryPreserved` verifies the full 2-hop chain
`grand_caller -> outer_mid -> mid_helper -> checked_add_u8` and establishes
`CalleeTableExcludes` for both stateless and stateful initial states.
-/
theorem grandCaller_twoHop_callChainCallBoundaryPreserved
    (args : List Value) (mem : Memory) :
    CallChainCallBoundaryPreserved grandCallerMir [outerMidMir, midHelperMir]
        [outerMidPath, midHelperPath] checkedAddU8Path ∧
      CalleeTableExcludes
        (initMachineStateWithCallees grandCallerMir args [outerMidMir, midHelperMir]).memory
        checkedAddU8Path ∧
      CalleeTableExcludes
        (initMachineStateWithMemoryAndCallees grandCallerMir args mem
          [outerMidMir, midHelperMir]).memory
        checkedAddU8Path :=
  let h : CallChainCallBoundaryPreserved grandCallerMir [outerMidMir, midHelperMir]
      [outerMidPath, midHelperPath] checkedAddU8Path :=
    (callChainCallBoundaryPreserved_iff _ _ _ _).1 rfl
  ⟨h, h.calleeTableExcludes_init args,
   h.calleeTableExcludes_initStateful_of_ne_nil (by simp) args mem⟩

/--
Breaking any link in the 2-hop chain — hop 0 (caller omits `outerMidPath`),
missing intermediate body, hop 1 (`outerMidInlinedMir` inlines `midHelperPath`),
or hop 2 (`midHelperInlinedMir` inlines `checkedAddU8Path`) — is rejected by
`CallChainCallBoundaryPreserved`.
-/
theorem grandCaller_twoHop_broken_links_rejected :
    ¬ CallChainCallBoundaryPreserved outerCallerMir [outerMidMir, midHelperMir]
        [outerMidPath, midHelperPath] checkedAddU8Path ∧
      ¬ CallChainCallBoundaryPreserved grandCallerMir [midHelperMir]
        [outerMidPath, midHelperPath] checkedAddU8Path ∧
      ¬ CallChainCallBoundaryPreserved grandCallerMir [outerMidInlinedMir, midHelperMir]
        [outerMidPath, midHelperPath] checkedAddU8Path ∧
      ¬ CallChainCallBoundaryPreserved grandCallerMir [outerMidMir, midHelperInlinedMir]
        [outerMidPath, midHelperPath] checkedAddU8Path := by
  refine ⟨not_callChainCallBoundaryPreserved_of_not_callsHead rfl,
    not_callChainCallBoundaryPreserved_of_missing_hop rfl, ?_, ?_⟩
  · intro h
    have hT := (callChainCallBoundaryPreserved_iff _ _ _ _).2 h
    rw [show callChainCallBoundaryPreserved grandCallerMir [outerMidInlinedMir, midHelperMir]
      [outerMidPath, midHelperPath] checkedAddU8Path = false from rfl] at hT
    nomatch hT
  · intro h
    have hT := (callChainCallBoundaryPreserved_iff _ _ _ _).2 h
    rw [show callChainCallBoundaryPreserved grandCallerMir [outerMidMir, midHelperInlinedMir]
      [outerMidPath, midHelperPath] checkedAddU8Path = false from rfl] at hT
    nomatch hT

/-! ### `ReachesLinkedOutcome` fault-free refutations & `withCallees` contract-level exact compose -/

/-- Fault-free handler that always returns `99`, violating `addCallerPost` on `(1, 2)`. -/
def wrongAnswerHandler : ExternalCallHandler := fun req =>
  pure (.returned (.scalar { bits := 99, sizeBytes := 1 }) req.memory)

/-- Fault-free handler that always returns `.aborted`, violating `.forbidAbort`. -/
def unexpectedAbortHandler : ExternalCallHandler := fun _ => pure .aborted

/--
Fault-free outcome violation via `ReachesLinkedOutcome`: `addCallerMir .continue_`
linked with `wrongAnswerHandler` is `TreeSafe` on `(1, 2)`, yet returns `99 ≠ 3`,
refuting `PanicsOnlyIf` without any `.ub` fault.
-/
theorem addCaller_wrongAnswer_treeSafe_not_panicsOnlyIf :
    TreeSafe
      (mirHandledTrees (addCallerMir .continue_) wrongAnswerHandler []
        (scalarArgs2 1 1 2, emptyMemory)) ∧
      ¬ PanicsOnlyIf (mirHandledTrees (addCallerMir .continue_) wrongAnswerHandler)
        addCallerPre addCallerPost addCallerOverflows := by
  have hSafe : TreeSafe
      (mirHandledTrees (addCallerMir .continue_) wrongAnswerHandler []
        (scalarArgs2 1 1 2, emptyMemory)) := by
    let hC : MirCallContract :=
      { pre := fun req => req.memory = emptyMemory
        post := fun req ans => ans = .returned (.scalar { bits := 99, sizeBytes := 1 }) req.memory }
    have hH : hC.holdsOn wrongAnswerHandler := holdsOn_pure_handler _ _ (fun _ _ => rfl)
    have hMod : MirModularPanicsOnlyIf (addCallerMir .continue_) hC.holdsOn
        (fun x => x = (scalarArgs2 1 1 2, emptyMemory)) (fun _ _ => True) (fun _ => False) :=
      mirModularPanicsOnlyIf_of_wpMirModularSym hC 8 (by
        rintro _ rfl
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        refine ⟨rfl, fun ans hAns => ?_⟩
        subst hAns
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        trivial)
    exact (hMod wrongAnswerHandler hH _ rfl).1
  have hPre : addCallerPre (scalarArgs2 1 1 2, emptyMemory) :=
    ⟨⟨1, 2, by decide, by decide, rfl⟩, rfl⟩
  have hNot : ¬ PanicsOnlyIf (mirHandledTrees (addCallerMir .continue_) wrongAnswerHandler)
      addCallerPre addCallerPost addCallerOverflows :=
    not_panicsOnlyIf_of_reachesLinkedOutcome hPre
      (.call rfl (reachesRet_pure_handler _) (.ret rfl))
      (fun hPost => by
        have hBits := congrArg (fun v => match v with | Value.scalar s => s.bits | _ => 0) hPost
        exact absurd hBits (by decide))
  exact ⟨hSafe, hNot⟩

/--
Fault-free abort-policy violation via `ReachesLinkedOutcome`: linking with
`unexpectedAbortHandler` is `TreeSafe` on `(1, 2)` yet reaches `.abort`, refuting
`PanicsOnlyIf` (`.forbidAbort`).
-/
theorem addCaller_unexpectedAbort_treeSafe_not_panicsOnlyIf :
    TreeSafe
      (mirHandledTrees (addCallerMir .continue_) unexpectedAbortHandler []
        (scalarArgs2 1 1 2, emptyMemory)) ∧
      ¬ PanicsOnlyIf (mirHandledTrees (addCallerMir .continue_) unexpectedAbortHandler)
        addCallerPre addCallerPost addCallerOverflows := by
  have hSafe : TreeSafe
      (mirHandledTrees (addCallerMir .continue_) unexpectedAbortHandler []
        (scalarArgs2 1 1 2, emptyMemory)) := by
    let hC : MirCallContract := { pre := fun _ => True, post := fun _ ans => ans = .aborted }
    have hH : hC.holdsOn unexpectedAbortHandler := holdsOn_pure_handler _ _ (fun _ _ => rfl)
    have hMod : MirModularPanicsWithPolicyOnlyIf (addCallerMir .continue_) hC.holdsOn
        (fun x => x = (scalarArgs2 1 1 2, emptyMemory)) (fun _ _ => True) (fun _ => False)
        .waiveAbortUnchecked :=
      mirModularPanicsWithPolicyOnlyIf_of_wpMirModularSym hC 8 (by
        rintro _ rfl
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        refine ⟨trivial, fun ans hAns => ?_⟩
        subst hAns
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        trivial)
    exact (hMod unexpectedAbortHandler hH _ rfl).1
  have hPre : addCallerPre (scalarArgs2 1 1 2, emptyMemory) :=
    ⟨⟨1, 2, by decide, by decide, rfl⟩, rfl⟩
  have hNot : ¬ PanicsOnlyIf (mirHandledTrees (addCallerMir .continue_) unexpectedAbortHandler)
      addCallerPre addCallerPost addCallerOverflows :=
    not_panicsOnlyIf_of_reachesLinkedOutcome hPre
      (.call rfl (reachesRet_pure_handler _) (.ret rfl))
      (fun hF => hF)
  exact ⟨hSafe, hNot⟩

/--
Contract-level exact composition via `linkCalleeWithCalleesHandler`: establishes
`TotalExactPolicyPanicContract` on `mirExternalClosedCalleeTrees checkedAddU8Mir []`
and composes `outerCallerMir` (`[midHelperMir]`) through
`totalExactPolicyPanicContract_call_compose_withCallees_of_callee_contract`.
-/
theorem checkedAddU8_externalClosedCallee_totalExactPolicy :
    TotalExactPolicyPanicContract (mirExternalClosedCalleeTrees checkedAddU8Mir [])
      (fun req =>
        checkedAddU8FrameGeneralContract.withTraitsPreserved.pre req ∧
          req.defPath = checkedAddU8Mir.defPath)
      (fun req r =>
        checkedAddU8FrameGeneralContract.withTraitsPreserved.post req r.1
          (restoreCallerMemoryFrame req.memory r.2))
      checkedAddU8FrameGeneralContract.withTraitsPreserved.panicCond .forbidAbort :=
  totalExactPolicyPanicContract_of_dwp (ewp := mirClosedWP)
    mirClosedEffect_nonFault_nonempty (by
      rintro ⟨_, typeArgs, _, mem⟩ ⟨⟨rfl, ⟨a, b, -, -, rfl⟩, hB⟩, -⟩
      refine dwp_interp failUnlinkedCalls
        (fun i Q u hwp => by
          cases i with
          | inl _ => exact False.elim hwp
          | inr i' =>
            cases i' with
            | inl obs => cases obs; exact DWP.vis (DWP.ret hwp)
            | inr _ => exact False.elim hwp)
        (DWP.mono (fun out _ h => ?_)
          (dwp_of_wpMirNoCallSym (checkedAddU8_frameGeneral_callee_wp typeArgs a b mem hB)))
      cases out with
      | normal r => exact ⟨h.1.2.1, fun ha => ha, h⟩
      | panic => exact ⟨h.1, fun ha => ha⟩
      | abort => exact False.elim h)

theorem outerCaller_linked_totalExact_via_callee_contract (fallback : ExternalCallHandler) :
    TotalExactPolicyPanicContract
      (mirHandledTrees outerCallerMir
        (linkCalleeWithCalleesHandler checkedAddU8Mir [] fallback) [midHelperMir])
      addCallerPre addCallerPost addCallerOverflows .forbidAbort :=
  totalExactPolicyPanicContract_call_compose_withCallees_of_callee_contract
    checkedAddU8FrameGeneralContract.withTraitsPreserved .forbidAbort []
    (by
      rintro ⟨_, _⟩ ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩
      refine dwp_of_wpMirModularSym (fuel := 16) ?_
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      refine ⟨⟨rfl, ⟨a, b, ha, hb, rfl⟩, rfl⟩, fun ans hPost => ?_⟩
      cases ans with
      | returned retVal memAfter =>
        obtain ⟨-, -, ⟨hVal, hFit, hMem⟩, _⟩ := hPost
        subst hVal hMem
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        exact ⟨hFit, fun ha => ha, rfl⟩
      | panicked memAfter =>
        obtain ⟨⟨hOver, -⟩, hMem, _⟩ := hPost
        subst hMem
        (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
        exact ⟨hOver, fun ha => ha⟩
      | aborted => exact False.elim hPost.1)
    (fun _ _ _ _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩)
    checkedAddU8_externalClosedCallee_totalExactPolicy
    (fun _ hPre hNe => False.elim (hNe hPre.1))

/-! ### Concrete non-exact `CompilerPass` & `VerifierPass` variance instantiations -/

/--
Source body with UB on `2`: `bb0: switchInt(copy _1) -> [0: bb1 (panic), 2: bb2 (unreachable), otherwise: bb3 (return _1)]`.
-/
def ubOnTwoMir : CapturedMir :=
  mkBody "panic_tests::ub_on_two" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut neverTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1), (2, 2)], otherwise := 3 })
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic") [] (local_ 2) .none .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .unreachable, isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Target body eliminating UB on `2`: `bb0: switchInt(copy _1) -> [0: bb1 (panic), otherwise: bb2 (return _1)]`.
-/
def definedOnTwoMir : CapturedMir :=
  mkBody "panic_tests::defined_on_two" 1
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .mut neverTy ]
    [ { statements := []
        terminator :=
          mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1)], otherwise := 2 })
        isCleanup := false }
    , { statements := [ mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic") [] (local_ 2) .none .continue_)
        isCleanup := false }
    , { statements := [ mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

private theorem cofix_eq_of_step_obs {step : MirExecState → MirStepNode} {st : MirExecState}
    {tag : Nat} {st' : MachineState}
    (h : step st = MirStepNode.emitStep (.event tag) st') :
    ITree.cofix step st =
      ITree.vis (E := MirEffect) (.inr (.inl (.emit (.event tag))))
        (fun _ => ITree.cofix step (.running st')) := by
  apply ITree.eq_of_observe_eq
  rw [ITree.observe_cofix, h]
  dsimp only [MirStepNode.emitStep, ITreeF.map]
  exact (ITree.observe_vis (E := MirEffect) (.inr (.inl (.emit (.event tag)))) _).symm

private theorem eutt_vis_vis {E : Effect.{u}} {R : Type u} (i : E.I)
    (k₁ k₂ : E.O i → ITree E R) (h : ∀ o, Eutt (k₁ o) (k₂ o)) :
    Eutt (ITree.vis i k₁) (ITree.vis i k₂) := by
  rw [Eutt.eq_def]
  exact Or.inr (Or.inl ⟨_, _, i, k₁, k₂, .refl _, .refl _,
    ITree.observe_vis i k₁, ITree.observe_vis i k₂, h⟩)

private theorem evalRvalue_use_copy_local_mem {locals : List LocalSlot}
    {loc : Local} {mem mem' : Memory} {decls : List LocalDecl}
    {layouts : LayoutTable} {val : Value} {locals' : List LocalSlot}
    (h : evalRvalue locals (.use (.copy (local_ loc))) mem decls layouts =
      .ok val locals' mem') :
    mem' = mem := by
  unfold evalRvalue at h
  simp only [local_] at h
  cases hEval : evalOperand locals (.copy { local_ := loc, projection := [] })
      mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack with
  | ub => simp only [hEval] at h; nomatch h
  | unsupported => simp only [hEval] at h; nomatch h
  | ok v l' =>
    simp only [hEval] at h
    cases hVal : validateLoadedValue layouts decls
        (.copy { local_ := loc, projection := [] }) v with
    | false => simp only [hVal] at h; nomatch h
    | true =>
      simp only [hVal] at h
      injection h with _ _ hMem
      exact hMem.symm

private theorem ubOnTwo_definedOnTwo_refines (args : List Value) :
    UBClosedObsPrefixes (EffectObs.erase MirEffect PUnit) (mirTrees definedOnTwoMir [] args) ≤
      UBClosedObsPrefixes (EffectObs.erase MirEffect PUnit) (mirTrees ubOnTwoMir [] args) := by
  let s0 := initMachineStateWithCallees ubOnTwoMir args []
  have hStepU : stepMirState ubOnTwoMir (.running s0) =
      evalTerminator s0
        (mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1), (2, 2)], otherwise := 3 }))
        (.some ubOnTwoMir) := rfl
  have hStepD : stepMirState definedOnTwoMir (.running s0) =
      evalTerminator s0
        (mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 1)], otherwise := 2 }))
        (.some definedOnTwoMir) := rfl
  have hLay : definedOnTwoMir.layouts = ubOnTwoMir.layouts := rfl
  cases hOp : evalOperand s0.frame.locals (.copy (local_ 1))
      s0.memory.borrows s0.memory.globals ubOnTwoMir.layouts
      s0.memory.callerLocals [] s0.memory.callStack with
  | ub =>
    have hU := cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (st := .running s0)
      (fk := .ub) (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp])
    have hD := cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (st := .running s0)
      (fk := .ub) (by rw [hStepD]; simp only [evalTerminator, mkTerm, hLay, hOp])
    change UBClosedObsPrefixes _ (ITree.cofix (stepMirState definedOnTwoMir) (.running s0)) ≤
      UBClosedObsPrefixes _ (ITree.cofix (stepMirState ubOnTwoMir) (.running s0))
    rw [hU, hD]
    exact fun _ hp => hp
  | unsupported =>
    have hU := cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (st := .running s0)
      (fk := .unsupported) (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp]; rfl)
    have hD := cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (st := .running s0)
      (fk := .unsupported) (by rw [hStepD]; simp only [evalTerminator, mkTerm, hLay, hOp]; rfl)
    change UBClosedObsPrefixes _ (ITree.cofix (stepMirState definedOnTwoMir) (.running s0)) ≤
      UBClosedObsPrefixes _ (ITree.cofix (stepMirState ubOnTwoMir) (.running s0))
    rw [hU, hD]
    exact fun _ hp => hp
  | ok v locals' =>
    cases v with
    | scalar sc =>
      cases h0 : Nat.beq sc.bits 0 with
      | true =>
        -- Both emit `.event sc.bits` and step to block 1 (`storageLive 2; panic`).
        have hEq : Eutt (mirTrees definedOnTwoMir [] args) (mirTrees ubOnTwoMir [] args) := by
          let s1 : MachineState :=
            { frame := { blockIdx := 1, stmtIdx := 0, locals := locals' }, memory := emptyMemory }
          have hU1 := cofix_eq_of_step_obs (step := stepMirState ubOnTwoMir) (st := .running s0)
            (tag := sc.bits) (st' := s1)
            (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp, lookupSwitchTarget, h0]; rfl)
          have hD1 := cofix_eq_of_step_obs (step := stepMirState definedOnTwoMir) (st := .running s0)
            (tag := sc.bits) (st' := s1)
            (by rw [hStepD]; simp only [evalTerminator, mkTerm, hLay, hOp, lookupSwitchTarget, h0]; rfl)
          change Eutt (ITree.cofix (stepMirState definedOnTwoMir) (.running s0))
            (ITree.cofix (stepMirState ubOnTwoMir) (.running s0))
          rw [hU1, hD1]
          refine eutt_vis_vis _ _ _ (fun _ => ?_)
          cases hG : Trusted.Sequence.get? locals' 2 with
          | none =>
            rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                  (by change evalStmt s1 (mkStmt (.storageLive 2)) definedOnTwoMir.localDecls definedOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG]),
                cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                  (by change evalStmt s1 (mkStmt (.storageLive 2)) ubOnTwoMir.localDecls ubOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG])]
            exact Eutt.refl _
          | some _ =>
            cases hS : Trusted.Sequence.set? locals' 2 .uninit with
            | none =>
              rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                    (by change evalStmt s1 (mkStmt (.storageLive 2)) definedOnTwoMir.localDecls definedOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG, hS]),
                  cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                    (by change evalStmt s1 (mkStmt (.storageLive 2)) ubOnTwoMir.localDecls ubOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG, hS])]
              exact Eutt.refl _
            | some locals₂ =>
              let s1' : MachineState :=
                { frame := { blockIdx := 1, stmtIdx := 1, locals := locals₂ }, memory := emptyMemory }
              rw [cofix_eq_of_step_tau (step := stepMirState definedOnTwoMir) (st' := .running s1')
                    (by change evalStmt s1 (mkStmt (.storageLive 2)) definedOnTwoMir.localDecls definedOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG, hS]; rfl),
                  cofix_eq_of_step_tau (step := stepMirState ubOnTwoMir) (st' := .running s1')
                    (by change evalStmt s1 (mkStmt (.storageLive 2)) ubOnTwoMir.localDecls ubOnTwoMir.layouts = _; simp only [evalStmt, mkStmt, s1, hG, hS]; rfl)]
              apply eutt_tau_tau
              rw [cofix_eq_of_step_ret (step := stepMirState definedOnTwoMir) (out := .panic) rfl,
                  cofix_eq_of_step_ret (step := stepMirState ubOnTwoMir) (out := .panic) rfl]
              exact Eutt.refl _
        exact (exactPass_of_eutt (mirArgsMachine args) (mirArgsMachine args)
          (EffectObs.erase MirEffect PUnit) hEq).up_refines trivial
      | false =>
        cases h2 : Nat.beq sc.bits 2 with
        | true =>
          -- `EffectObs.erase` erases the `switchInt` observation, so `ubOnTwoMir` faults at trace `[]`.
          let s2 : MachineState :=
            { frame := { blockIdx := 2, stmtIdx := 0, locals := locals' }, memory := emptyMemory }
          have hU1 := cofix_eq_of_step_obs (step := stepMirState ubOnTwoMir) (st := .running s0)
            (tag := sc.bits) (st' := s2)
            (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp, lookupSwitchTarget, h0, h2]; rfl)
          have hU2 := cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (st := .running s2)
            (fk := .ub) rfl
          have hFaultAt0 :
              HasObsPrefix (EffectObs.erase MirEffect PUnit) (mirTrees ubOnTwoMir [] args)
                ⟨[], .fault⟩ := by
            refine ⟨[⟨(.inr (.inl (.emit (.event sc.bits))) : MirEffect.I), PUnit.unit⟩],
              ITree.fail FailureKind.ub, ?_, faultNow_fail FailureKind.ub, rfl⟩
            change Reaches (ITree.cofix (stepMirState ubOnTwoMir) (.running s0)) _ _
            rw [hU1]
            refine Reaches.vis (E := MirEffect)
              (i := (.inr (.inl (.emit (.event sc.bits))) : MirEffect.I))
              (ITree.observe_vis _ _) (fun hF => hF) PUnit.unit ?_
            rw [hU2]
            exact Reaches.refl _
          intro p _
          exact Or.inr ⟨[], List.nil_prefix, hFaultAt0⟩
        | false =>
          -- Both emit `.event sc.bits` and execute `_0 = copy _1; return`.
          have hEq : Eutt (mirTrees definedOnTwoMir [] args) (mirTrees ubOnTwoMir [] args) := by
            let sU : MachineState :=
              { frame := { blockIdx := 3, stmtIdx := 0, locals := locals' }, memory := emptyMemory }
            let sD : MachineState :=
              { frame := { blockIdx := 2, stmtIdx := 0, locals := locals' }, memory := emptyMemory }
            have hU1 := cofix_eq_of_step_obs (step := stepMirState ubOnTwoMir) (st := .running s0)
              (tag := sc.bits) (st' := sU)
              (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp, lookupSwitchTarget, h0, h2]; rfl)
            have hD1 := cofix_eq_of_step_obs (step := stepMirState definedOnTwoMir) (st := .running s0)
              (tag := sc.bits) (st' := sD)
              (by rw [hStepD]; simp only [evalTerminator, mkTerm, hLay, hOp, lookupSwitchTarget, h0]; rfl)
            change Eutt (ITree.cofix (stepMirState definedOnTwoMir) (.running s0))
              (ITree.cofix (stepMirState ubOnTwoMir) (.running s0))
            rw [hU1, hD1]
            refine eutt_vis_vis _ _ _ (fun _ => ?_)
            have hAsgnD : stepMirState definedOnTwoMir (.running sD) =
                evalStmt sD (mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))))
                  ubOnTwoMir.localDecls ubOnTwoMir.layouts := rfl
            have hAsgnU : stepMirState ubOnTwoMir (.running sU) =
                evalStmt sU (mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))))
                  ubOnTwoMir.localDecls ubOnTwoMir.layouts := rfl
            cases hRv : evalRvalue locals' (.use (.copy (local_ 1))) emptyMemory
                ubOnTwoMir.localDecls ubOnTwoMir.layouts with
            | ub =>
              rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                    (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]),
                  cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                    (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv])]
              exact Eutt.refl _
            | unsupported =>
              rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .unsupported)
                    (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]; rfl),
                  cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .unsupported)
                    (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv]; rfl)]
              exact Eutt.refl _
            | ok val locals₁ mem₁ =>
              have hMemEq : mem₁ = emptyMemory := evalRvalue_use_copy_local_mem hRv
              subst hMemEq
              cases hGet : Trusted.Sequence.get? locals₁ 0 with
              | none =>
                rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                      (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]; simp only [local_, hGet]),
                    cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                      (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv]; simp only [local_, hGet])]
                exact Eutt.refl _
              | some slot =>
                cases slot with
                | dead =>
                  rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                        (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]; simp only [local_, hGet]),
                      cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                        (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv]; simp only [local_, hGet])]
                  exact Eutt.refl _
                | uninit | init _ =>
                  cases hSet : Trusted.Sequence.set? locals₁ 0 (.init val) with
                  | none =>
                    rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (fk := .ub)
                          (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]; simp only [local_, hGet, hSet]),
                        cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (fk := .ub)
                          (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv]; simp only [local_, hGet, hSet])]
                    exact Eutt.refl _
                  | some locals₂ =>
                    let sD' : MachineState :=
                      { frame := { blockIdx := 2, stmtIdx := 1, locals := locals₂ }, memory := emptyMemory }
                    let sU' : MachineState :=
                      { frame := { blockIdx := 3, stmtIdx := 1, locals := locals₂ }, memory := emptyMemory }
                    rw [cofix_eq_of_step_tau (step := stepMirState definedOnTwoMir) (st' := .running sD')
                          (by rw [hAsgnD]; simp only [evalStmt, mkStmt, sD, hRv]; simp only [local_, hGet, hSet]; rfl),
                        cofix_eq_of_step_tau (step := stepMirState ubOnTwoMir) (st' := .running sU')
                          (by rw [hAsgnU]; simp only [evalStmt, mkStmt, sU, hRv]; simp only [local_, hGet, hSet]; rfl)]
                    apply eutt_tau_tau
                    have hRetD : stepMirState definedOnTwoMir (.running sD') =
                        evalTerminator sD' (mkTerm .return_) (.some ubOnTwoMir) := rfl
                    have hRetU : stepMirState ubOnTwoMir (.running sU') =
                        evalTerminator sU' (mkTerm .return_) (.some ubOnTwoMir) := rfl
                    cases hNode : evalTerminator sD' (mkTerm .return_) (.some ubOnTwoMir) with
                    | ret out =>
                      rw [cofix_eq_of_step_ret (step := stepMirState definedOnTwoMir) (hRetD.trans hNode),
                          cofix_eq_of_step_ret (step := stepMirState ubOnTwoMir) (hRetU.trans hNode)]
                      exact Eutt.refl _
                    | tau _ =>
                      simp only [evalTerminator, mkTerm, sD'] at hNode
                      repeat (split at hNode <;> try contradiction)
                    | vis _ _ =>
                      have hFk : ∃ fk, evalTerminator sD' (mkTerm .return_) (.some ubOnTwoMir) =
                          MirStepNode.fail fk := by
                        simp only [evalTerminator, mkTerm, sD'] at hNode ⊢
                        repeat (split at hNode <;> try contradiction)
                        all_goals (try exact ⟨.ub, rfl⟩)
                      obtain ⟨fk, hF⟩ := hFk
                      rw [cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (hRetD.trans hF),
                          cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (hRetU.trans hF)]
                      exact Eutt.refl _
          exact (exactPass_of_eutt (mirArgsMachine args) (mirArgsMachine args)
            (EffectObs.erase MirEffect PUnit) hEq).up_refines trivial
    | _ =>
      have hU := cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (st := .running s0)
        (fk := .ub) (by rw [hStepU]; simp only [evalTerminator, mkTerm, hOp])
      have hD := cofix_eq_of_step_fail (step := stepMirState definedOnTwoMir) (st := .running s0)
        (fk := .ub) (by rw [hStepD]; simp only [evalTerminator, mkTerm, hLay, hOp])
      change UBClosedObsPrefixes _ (ITree.cofix (stepMirState definedOnTwoMir) (.running s0)) ≤
        UBClosedObsPrefixes _ (ITree.cofix (stepMirState ubOnTwoMir) (.running s0))
      rw [hU, hD]
      exact fun _ hp => hp

/-- Concrete non-exact `CompilerPass`: eliminating UB on `x = 2` refines `ubOnTwoMir`. -/
theorem ubOnTwo_to_definedOnTwo_compilerPass :
    CompilerPass
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      Spec.top id ubOnTwoMir definedOnTwoMir :=
  fun _ args => ubOnTwo_definedOnTwo_refines args

/-- Concrete non-exact `VerifierPass` in the reverse direction. -/
theorem definedOnTwo_to_ubOnTwo_verifierPass :
    VerifierPass
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      Spec.top id definedOnTwoMir ubOnTwoMir :=
  fun _ args => ubOnTwo_definedOnTwo_refines args

/-- The pass is strictly non-exact (`¬ ExactPass`), separated at input `x = 2`. -/
theorem ubOnTwo_to_definedOnTwo_not_exactPass :
    ¬ ExactPass
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      id id ubOnTwoMir definedOnTwoMir := by
  intro hEx
  have hOnlyDef : PanicsOnlyIf (mirTrees definedOnTwoMir)
      (fun args => args = [.scalar { bits := 2, sizeBytes := 1 }])
      (fun _ r => r.1 = .scalar { bits := 2, sizeBytes := 1 }) (fun _ => False) :=
    panicsOnlyIf_of_wpMirSym 8 (by
      rintro _ rfl
      exact rfl)
  have hOnlyUb : PanicsOnlyIf (mirTrees ubOnTwoMir)
      (fun args => args = [.scalar { bits := 2, sizeBytes := 1 }])
      (fun _ r => r.1 = .scalar { bits := 2, sizeBytes := 1 }) (fun _ => False) :=
    (panicsOnlyIf_exactPass_iff
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b []) hEx).2 hOnlyDef
  have hSafe : TreeSafe (mirTrees ubOnTwoMir [] [.scalar { bits := 2, sizeBytes := 1 }]) :=
    (hOnlyUb _ rfl).1
  let s0 := initMachineStateWithCallees ubOnTwoMir [.scalar { bits := 2, sizeBytes := 1 }] []
  let s2 : MachineState :=
    { frame := { blockIdx := 2, stmtIdx := 0, locals := s0.frame.locals }, memory := emptyMemory }
  have hReaches :
      Reaches (mirTrees ubOnTwoMir [] [.scalar { bits := 2, sizeBytes := 1 }])
        [⟨(.inr (.inl (.emit (.event 2))) : MirEffect.I), PUnit.unit⟩]
        (ITree.fail FailureKind.ub) := by
    change Reaches (ITree.cofix (stepMirState ubOnTwoMir) (.running s0)) _ _
    rw [cofix_eq_of_step_obs (step := stepMirState ubOnTwoMir) (st := .running s0)
      (tag := 2) (st' := s2) rfl]
    refine Reaches.vis (E := MirEffect)
      (i := (.inr (.inl (.emit (.event 2))) : MirEffect.I))
      (ITree.observe_vis _ _) (fun hF => hF) PUnit.unit ?_
    rw [cofix_eq_of_step_fail (step := stepMirState ubOnTwoMir) (st := .running s2)
      (fk := .ub) rfl]
    exact Reaches.refl _
  exact hSafe _ _ hReaches (faultNow_fail FailureKind.ub)

/--
All four non-exact `Anneal.Pass` variance transfers exercised on the strictly
non-exact UB-eliminating pass (`ubOnTwoMir` ↔ `definedOnTwoMir`) for `x ≠ 2`.
-/
theorem ubOnTwo_nonExact_pass_variance_transfers :
    let preNe2 : List Value → Prop := fun args => scalarPre1 args ∧ argBits args 0 ≠ 2
    let postId : List Value → MirReturn → Prop :=
      fun args r => r.1 = .scalar { bits := argBits args 0, sizeBytes := 1 }
    let pCond : List Value → Prop := fun args => argBits args 0 = 0
    PanicsOnlyIf (mirTrees definedOnTwoMir) preNe2 postId pCond ∧
      PanicsIf (mirTrees ubOnTwoMir) preNe2 pCond ∧
      PanicsOnlyIf (mirTrees ubOnTwoMir) preNe2 postId pCond ∧
      PanicsIf (mirTrees definedOnTwoMir) preNe2 pCond := by
  intro preNe2 postId pCond
  have hUbOnly : PanicsOnlyIf (mirTrees ubOnTwoMir) preNe2 postId pCond :=
    panicsOnlyIf_of_wpMirSym 8 (by
      rintro _ ⟨⟨x, -, rfl⟩, hNe2⟩
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      · rename_i heq; exact (nat_beq_eq_true_iff _ _).1 heq
      · rename_i _ _ heq2; exact False.elim (hNe2 ((nat_beq_eq_true_iff _ _).1 heq2))
      · rfl)
  have hDefOnly : PanicsOnlyIf (mirTrees definedOnTwoMir) preNe2 postId pCond :=
    PanicsOnlyIf.compilerPass_forward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      ubOnTwo_to_definedOnTwo_compilerPass trivial hUbOnly
  have hDefIf : PanicsIf (mirTrees definedOnTwoMir) preNe2 pCond :=
    (totalExactPanicContract_of_wpMirSym 8 (post := postId) (by
      rintro _ ⟨⟨x, -, rfl⟩, -⟩
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      · rename_i heq; exact (nat_beq_eq_true_iff _ _).1 heq
      · rename_i heq; exact ⟨(nat_beq_eq_false_iff _ _).1 heq, rfl⟩)).exact.2
  have hUbIf : PanicsIf (mirTrees ubOnTwoMir) preNe2 pCond :=
    PanicsIf.compilerPass_backward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      ubOnTwo_to_definedOnTwo_compilerPass trivial
      (fun x hx => (hUbOnly x hx).1) hDefIf
  have hDefOnlyBack : PanicsOnlyIf (mirTrees definedOnTwoMir) preNe2 postId pCond :=
    PanicsOnlyIf.verifierPass_backward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      definedOnTwo_to_ubOnTwo_verifierPass trivial hUbOnly
  have hUbIfFwd : PanicsIf (mirTrees ubOnTwoMir) preNe2 pCond :=
    PanicsIf.verifierPass_forward
      (sem₁ := fun b => mirTrees b []) (sem₂ := fun b => mirTrees b [])
      definedOnTwo_to_ubOnTwo_verifierPass trivial
      (fun x hx => (hUbOnly x hx).1) hDefIf
  exact ⟨hDefOnlyBack, hUbIfFwd, hUbOnly, hDefIf⟩

/-- Concrete MIR body that always panics: `bb0: storageLive 1; core::panicking::panic()`. -/
def alwaysPanicMir : CapturedMir :=
  mkBody "panic_tests::always_panic" 0
    [ mkDecl .mut unitTy, mkDecl .mut neverTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call (fnItemOp "core::panicking::panic") [] (local_ 1) .none .continue_)
        isCleanup := false } ]

/-- Concrete MIR body that diverges silently: `bb0: goto -> bb0`. -/
def infiniteLoopMir : CapturedMir :=
  mkBody "panic_tests::infinite_loop" 0
    [ mkDecl .mut unitTy ]
    [ { statements := [], terminator := mkTerm (.goto 0), isCleanup := false } ]

private theorem infiniteLoopMir_eq_spin (args : List Value) :
    mirTrees infiniteLoopMir [] args = ITree.spin := by
  let s0 := initMachineStateWithCallees infiniteLoopMir args []
  refine ITree.bisim_eq
    (fun a b => a = ITree.cofix (stepMirState infiniteLoopMir) (.running s0) ∧ b = ITree.spin)
    ?_ ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  rw [ITree.observe_cofix, observe_spin]
  exact ⟨rfl, rfl⟩

/-- Concrete MIR `CompilerPass`: silent divergence refines panicking (`alwaysPanicMir` → `infiniteLoopMir`). -/
theorem alwaysPanic_to_infiniteLoop_compilerPass :
    CompilerPass
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      (panicSemantics (EffectObs.erase MirEffect PUnit) (fun b => mirTrees b []))
      Spec.top id alwaysPanicMir infiniteLoopMir := by
  intro _ args
  dsimp only [panicSemantics, panicBehavior, id]
  rw [infiniteLoopMir_eq_spin args]
  have hPanicEq : mirTrees alwaysPanicMir [] args = .tau (.ret .panic) := by
    let s0 := initMachineStateWithCallees alwaysPanicMir args []
    let s1 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .uninit] },
        memory := emptyMemory }
    have h1 : mirTrees alwaysPanicMir [] args =
        .tau (ITree.cofix (stepMirState alwaysPanicMir) (.running s1)) :=
      cofix_eq_of_step_tau (step := stepMirState alwaysPanicMir) (st := .running s0)
        (st' := .running s1) (by
          cases args with
          | nil => exact rfl
          | cons _ _ => exact rfl)
    have h2 : ITree.cofix (stepMirState alwaysPanicMir) (.running s1) = .ret .panic :=
      cofix_eq_of_step_ret (step := stepMirState alwaysPanicMir) (st := .running s1)
        (out := .panic) rfl
    rw [h1, h2]
  rw [hPanicEq]
  intro p hp
  have hSub := (panic_trigger_not_downward_closed (E := MirEffect) (Val := MirReturn)
    (EffectObs.erase MirEffect PUnit)).1 p hp
  rcases hSub with hPre | ⟨tr, hPref, hF⟩
  · refine Or.inl ?_
    cases ho : p.outcome with
    | running =>
      simp only [HasObsPrefix, ho] at hPre ⊢
      obtain ⟨tr, u, hr, hTr⟩ := hPre
      exact ⟨tr, u, .tau (ITree.observe_tau _) hr, hTr⟩
    | ret r =>
      simp only [HasObsPrefix, ho] at hPre ⊢
      obtain ⟨tr, ⟨u, hr, hu⟩, hTr⟩ := hPre
      exact ⟨tr, ⟨u, .tau (ITree.observe_tau _) hr, hu⟩, hTr⟩
    | fault =>
      simp only [HasObsPrefix, ho] at hPre ⊢
      obtain ⟨tr, u, hr, hf, hTr⟩ := hPre
      exact ⟨tr, u, .tau (ITree.observe_tau _) hr, hf, hTr⟩
  · obtain ⟨tr', u, hr, hf, hTr⟩ := hF
    exact Or.inr ⟨tr, hPref, tr', u, .tau (ITree.observe_tau _) hr, hf, hTr⟩

/--
Concrete MIR counterexample to forward `PanicsIf` across `CompilerPass`:
`alwaysPanicMir` satisfies `PanicsIf`, `infiniteLoopMir` refines it via
`alwaysPanic_to_infiniteLoop_compilerPass`, yet `infiniteLoopMir` refutes `PanicsIf`.
-/
theorem alwaysPanic_panicsIf_infiniteLoop_not_panicsIf :
    PanicsIf (mirTrees alwaysPanicMir) (fun args => args = []) (fun _ => True) ∧
      ¬ PanicsIf (mirTrees infiniteLoopMir) (fun args => args = []) (fun _ => True) := by
  refine ⟨?_, ?_⟩
  · rintro _ rfl _
    exact (totalExactPanicContract_of_wpMirSym 4 (by
      rintro _ rfl
      conv => whnf
      trivial) : TotalExactPanicContract (mirTrees alwaysPanicMir)
        (fun args => args = []) (fun _ _ => True) (fun _ => True)).exact.2 [] rfl trivial
  · intro hIf
    obtain ⟨tr, hr⟩ := hIf [] rfl trivial
    rw [infiniteLoopMir_eq_spin []] at hr
    exact not_reachesRet_spin tr (.panic : MirOutcome) hr

/-! ### Trait-dispatched hops in a call chain -/

def dispatchHelperPath : DefPath := "panic_tests::Dispatch::helper"
def dispatchEvilPath : DefPath := "panic_tests::dispatch_evil_impl"

/-- The helper the chain guard checks: it calls `checked_add_u8`. -/
def dispatchHelperMir : CapturedMir :=
  mkBody dispatchHelperPath 2
    [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
    [ { statements := []
        terminator :=
          mkTerm (.call (fnItemOp checkedAddU8Path) [.copy (local_ 1), .copy (local_ 2)]
            (local_ 0) (.some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]

/-- The body the trait implementation dispatches to: `checked_add_u8` inlined. -/
def dispatchEvilMir : CapturedMir :=
  checkedAddMir dispatchEvilPath u8Ty u8CheckedTy .continue_

/-- A trait implementation that dispatches the helper path to `dispatchEvilMir`. -/
def dispatchImpl : TraitImplEntry :=
  { traitRef := { defPath := dispatchHelperPath, args := [.uint .u8] },
    implPath := dispatchEvilPath }

/-- A caller that calls the helper with a type argument and carries `dispatchImpl`. -/
def dispatchCallerMir : CapturedMir :=
  { mkBody "panic_tests::dispatch_caller" 2
      [ mkDecl .mut u8Ty, mkDecl .not u8Ty, mkDecl .not u8Ty ]
      [ { statements := []
          terminator :=
            mkTerm (.call (fnItemOp dispatchHelperPath [.uint .u8])
              [.copy (local_ 1), .copy (local_ 2)] (local_ 0) (.some 1) .continue_)
          isCleanup := false }
      , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]
    with traitImpls := [dispatchImpl] }

def dispatchCallees : List CapturedMir := [dispatchHelperMir, dispatchEvilMir]

/--
`CallChainCallBoundaryPreserved` follows the helper path through `findCallee?`
to `dispatchHelperMir`, which calls `checked_add_u8`, and accepts the chain. At
run time `lookupCallee` dispatches the same path through `dispatchImpl` to
`dispatchEvilMir`, where `checked_add_u8` is inlined, so the boundary is gone.
`ChainHopsNotTraitDispatched` rejects the chain.
-/
theorem dispatchCaller_chain_guard_vs_runtime (args : List Value) :
    CallChainCallBoundaryPreserved dispatchCallerMir dispatchCallees [dispatchHelperPath]
        checkedAddU8Path ∧
      findCallee? dispatchCallees dispatchHelperPath = .some dispatchHelperMir ∧
      lookupCallee (initMachineStateWithCallees dispatchCallerMir args dispatchCallees).memory.callees
          emptyLayoutTable dispatchHelperPath [.uint .u8]
          (initMachineStateWithCallees dispatchCallerMir args dispatchCallees).memory.traitImpls =
        .some dispatchEvilMir ∧
      bodyCallsDefPath checkedAddU8Path dispatchEvilMir = false ∧
      ¬ ChainHopsNotTraitDispatched dispatchCallerMir dispatchCallees [dispatchHelperPath] := by
  refine ⟨(callChainCallBoundaryPreserved_iff _ _ _ _).1 rfl, rfl, rfl, rfl, fun h => ?_⟩
  have hT := (chainHopsNotTraitDispatched_iff _ _ _).2 h
  rw [show chainHopsNotTraitDispatched dispatchCallerMir dispatchCallees [dispatchHelperPath] =
    false from rfl] at hT
  nomatch hT

/-- On a chain without trait dispatch both guards hold. -/
theorem outerCaller_chain_not_traitDispatched :
    ChainHopsNotTraitDispatched outerCallerMir [midHelperMir] [midHelperPath] :=
  (chainHopsNotTraitDispatched_iff _ _ _).1 rfl


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
    (type_of% @checkedAddU8_ground_witnesses) ∧
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
    (type_of% @twoSiteCaller_callSitesPreserved) ∧
    (type_of% @twoSiteHalfInlined_callBoundaryPreserved) ∧
    (type_of% @twoSiteHalfInlined_not_callSitesPreserved) ∧
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
    (type_of% @injectingHandler_holdsOn_withFramePreserved) ∧
    (type_of% @twoCall_frameOnly_not_modular) ∧
    (type_of% @twoCall_traitsPreserved_modular_neverPanics) ∧
    (type_of% @twoCallContract_pre_not_universal) ∧
    (type_of% @twoCall_reachableOn_guard) ∧
    (type_of% @twoCall_reachable_guard_of_modular_proof) ∧
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
    (type_of% @tailCall_step_probes) ∧
    (type_of% @tailCall_no_inline_intercept_panic_and_exactDiv) ∧
    (type_of% @tailCall_resume_outcomes) ∧
    (type_of% @checkedAddU8_generalMem_callee_wp) ∧
    (type_of% @checkedAddU8_generalMem_holdsTotallyOn) ∧
    (type_of% @addCaller_generalMem_unwinding_wp) ∧
    (type_of% @addCaller_generalMem_linked_totalExact) ∧
    (type_of% @checkedAddU8_frameGeneral_callee_wp) ∧
    (type_of% @checkedAddU8_frameGeneral_holdsTotallyOn) ∧
    (type_of% @checkedAddU8_closedCallee_totalExactPolicy) ∧
    (type_of% @addCaller_linked_totalExact_via_callee_contract) ∧
    (type_of% @addCallerUnreachable_linked_not_panicsWithPolicyOnlyIf) ∧
    (type_of% @explicitPanic_continue_totalExact) ∧
    (type_of% @explicitPanic_terminate_totalExact) ∧
    (type_of% @explicitPanic_unreachable_not_panicsWithPolicyOnlyIf) ∧
    (type_of% @reactiveSwitchLoopMir_totalVerificationResult_not_totalExact) ∧
    (type_of% @outerCaller_calleesCallBoundaryPreserved) ∧
    (type_of% @outerCaller_calleesCallBoundaryPreserved_refutations) ∧
    (type_of% @callBoundaryPreserved_emptyCallees_does_not_guard_prepopulated_mem) ∧
    (type_of% @twoCall_resumed_state_guard_preserved) ∧
    (type_of% @indirect_and_fnItem_local_boundary_probes) ∧
    (type_of% @outerCaller_wp) ∧
    (type_of% @outerCaller_linked_totalExact) ∧
    (type_of% @outerCaller_linked_panicsOnlyIf) ∧
    (type_of% @outerCaller_linkCalleeHandler_not_panicsWithPolicyOnlyIf) ∧
    (type_of% @outerCaller_linkCalleeHandler_vs_withCallees) ∧
    (type_of% @checkedAddU8_not_holdsOn_toExactPolicy_waiveAbortUnchecked) ∧
    (type_of% @panicOrAbort_wp) ∧
    (type_of% @panicOrAbort_totalExact) ∧
    (type_of% @panicOrAbort_exactPanicAbort) ∧
    (type_of% @panicOrAbort_deterministicRet) ∧
    (type_of% @panicOrAbort_not_exactPanicAbort_overlapping) ∧
    (type_of% @panicOrAbort_conds_disjoint) ∧
    (type_of% @checkedAddU8_nop_eutt) ∧
    (type_of% @checkedAddU8_nop_exactPass) ∧
    (type_of% @checkedAddU8Nop_pass_variance_transfers) ∧
    (type_of% @kani5202_misaligned_u32_scalar_ptr_alignment_blindness) ∧
    (type_of% @kani5202_arith_offset_intrinsic_dangling_ptr_succeeds) ∧
    (type_of% @kani5219_borrow_backed_reborrow_and_write_contagion) ∧
    (type_of% @kani5219_global_alloc_slice_asymmetry) ∧
    (type_of% @multiStepCaller_reachable_preserves_calleeTableExcludes) ∧
    (type_of% @multiStepCaller_concrete_handler_guard) ∧
    (type_of% @multiStepCaller_concrete_chained_handler_guard_reaches_bb3) ∧
    (type_of% @checkedAddU8_disjointBorrows_callee_wp) ∧
    (type_of% @checkedAddU8_disjointBorrows_holdsTotallyOn) ∧
    (type_of% @checkedAddU8_disjointBorrows_nonEmpty_witness) ∧
    (type_of% @borrowCaller_inlined_returns_ok) ∧
    (type_of% @borrowCaller_linked_handler_ub) ∧
    (type_of% @borrowCaller_linked_withCallees_ub) ∧
    (type_of% @linkCallee_depth0_borrow_collision_divergence) ∧
    (type_of% @checkedAddU8_borrowIsolated_callee_wp) ∧
    (type_of% @checkedAddU8_borrowIsolated_holdsTotallyOn) ∧
    (type_of% @borrowCaller_borrowIsolated_neverPanics_and_totalExact) ∧
    (type_of% @borrowCaller_inlined_totalExact_all_u8) ∧
    (type_of% @borrowCaller_borrowIsolated_totalExact_all_u8) ∧
    (type_of% @borrowCaller_borrowIsolated_vs_inlined_exactPass_all_u8) ∧
    (type_of% @outerCaller_borrowIsolated_totalExact) ∧
    (type_of% @refCaller_inlined_returns_5) ∧
    (type_of% @refCaller_linkCallee_silent_local_aliasing) ∧
    (type_of% @refCaller_linkCalleeWithCallees_silent_local_aliasing) ∧
    (type_of% @refCaller_borrowIsolated_fails_closed_ub) ∧
    (type_of% @refCaller_threeWay_lowering_divergence) ∧
    (type_of% @addCallerInlinedDeadCall_rejected_by_reachableGuards) ∧
    (type_of% @addCallerInlinedFalseBranchDecoy_reachable_yet_never_calls) ∧
    (type_of% @outerTwoSiteCaller_calleesCallSitesPreserved) ∧
    (type_of% @outerTwoSiteHalfInlined_calleesCallBoundary_not_callSites) ∧
    (type_of% @outerCaller_deadDecoyHelper_passes_syntactic_rejected_by_reachable) ∧
    (type_of% @outerTwoSiteCaller_reachableCalleesCallSitesPreserved) ∧
    (type_of% @outerCallerFullyInlined_fools_callees_guards) ∧
    (type_of% @outerCaller_helperChainCallBoundaryPreserved) ∧
    (type_of% @outerCaller_inlinedHelper_not_helperChain) ∧
    (type_of% @grandCaller_twoHop_helperChain_fails_on_linked_hop) ∧
    (type_of% @grandCaller_twoHop_callChainCallBoundaryPreserved) ∧
    (type_of% @grandCaller_twoHop_broken_links_rejected) ∧
    (type_of% @addCaller_wrongAnswer_treeSafe_not_panicsOnlyIf) ∧
    (type_of% @addCaller_unexpectedAbort_treeSafe_not_panicsOnlyIf) ∧
    (type_of% @checkedAddU8_externalClosedCallee_totalExactPolicy) ∧
    (type_of% @outerCaller_linked_totalExact_via_callee_contract) ∧
    (type_of% @ubOnTwo_to_definedOnTwo_compilerPass) ∧
    (type_of% @definedOnTwo_to_ubOnTwo_verifierPass) ∧
    (type_of% @ubOnTwo_to_definedOnTwo_not_exactPass) ∧
    (type_of% @ubOnTwo_nonExact_pass_variance_transfers) ∧
    (type_of% @alwaysPanic_to_infiniteLoop_compilerPass) ∧
    (type_of% @alwaysPanic_panicsIf_infiniteLoop_not_panicsIf) ∧
    (type_of% @dispatchCaller_chain_guard_vs_runtime) ∧
    (type_of% @outerCaller_chain_not_traitDispatched) :=
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
    @checkedAddU8_ground_witnesses,
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
    @twoSiteCaller_callSitesPreserved,
    @twoSiteHalfInlined_callBoundaryPreserved,
    @twoSiteHalfInlined_not_callSitesPreserved,
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
    @injectingHandler_holdsOn_withFramePreserved,
    @twoCall_frameOnly_not_modular,
    @twoCall_traitsPreserved_modular_neverPanics,
    @twoCallContract_pre_not_universal,
    @twoCall_reachableOn_guard,
    @twoCall_reachable_guard_of_modular_proof,
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
    @tailCall_step_probes,
    @tailCall_no_inline_intercept_panic_and_exactDiv,
    @tailCall_resume_outcomes,
    @checkedAddU8_generalMem_callee_wp,
    @checkedAddU8_generalMem_holdsTotallyOn,
    @addCaller_generalMem_unwinding_wp,
    @addCaller_generalMem_linked_totalExact,
    @checkedAddU8_frameGeneral_callee_wp,
    @checkedAddU8_frameGeneral_holdsTotallyOn,
    @checkedAddU8_closedCallee_totalExactPolicy,
    @addCaller_linked_totalExact_via_callee_contract,
    @addCallerUnreachable_linked_not_panicsWithPolicyOnlyIf,
    @explicitPanic_continue_totalExact,
    @explicitPanic_terminate_totalExact,
    @explicitPanic_unreachable_not_panicsWithPolicyOnlyIf,
    @reactiveSwitchLoopMir_totalVerificationResult_not_totalExact,
    @outerCaller_calleesCallBoundaryPreserved,
    @outerCaller_calleesCallBoundaryPreserved_refutations,
    @callBoundaryPreserved_emptyCallees_does_not_guard_prepopulated_mem,
    @twoCall_resumed_state_guard_preserved,
    @indirect_and_fnItem_local_boundary_probes,
    @outerCaller_wp,
    @outerCaller_linked_totalExact,
    @outerCaller_linked_panicsOnlyIf,
    @outerCaller_linkCalleeHandler_not_panicsWithPolicyOnlyIf,
    @outerCaller_linkCalleeHandler_vs_withCallees,
    @checkedAddU8_not_holdsOn_toExactPolicy_waiveAbortUnchecked,
    @panicOrAbort_wp,
    @panicOrAbort_totalExact,
    @panicOrAbort_exactPanicAbort,
    @panicOrAbort_deterministicRet,
    @panicOrAbort_not_exactPanicAbort_overlapping,
    @panicOrAbort_conds_disjoint,
    @checkedAddU8_nop_eutt,
    @checkedAddU8_nop_exactPass,
    @checkedAddU8Nop_pass_variance_transfers,
    @kani5202_misaligned_u32_scalar_ptr_alignment_blindness,
    @kani5202_arith_offset_intrinsic_dangling_ptr_succeeds,
    @kani5219_borrow_backed_reborrow_and_write_contagion,
    @kani5219_global_alloc_slice_asymmetry,
    @multiStepCaller_reachable_preserves_calleeTableExcludes,
    @multiStepCaller_concrete_handler_guard,
    @multiStepCaller_concrete_chained_handler_guard_reaches_bb3,
    @checkedAddU8_disjointBorrows_callee_wp,
    @checkedAddU8_disjointBorrows_holdsTotallyOn,
    @checkedAddU8_disjointBorrows_nonEmpty_witness,
    @borrowCaller_inlined_returns_ok,
    @borrowCaller_linked_handler_ub,
    @borrowCaller_linked_withCallees_ub,
    @linkCallee_depth0_borrow_collision_divergence,
    @checkedAddU8_borrowIsolated_callee_wp,
    @checkedAddU8_borrowIsolated_holdsTotallyOn,
    @borrowCaller_borrowIsolated_neverPanics_and_totalExact,
    @borrowCaller_inlined_totalExact_all_u8,
    @borrowCaller_borrowIsolated_totalExact_all_u8,
    @borrowCaller_borrowIsolated_vs_inlined_exactPass_all_u8,
    @outerCaller_borrowIsolated_totalExact,
    @refCaller_inlined_returns_5,
    @refCaller_linkCallee_silent_local_aliasing,
    @refCaller_linkCalleeWithCallees_silent_local_aliasing,
    @refCaller_borrowIsolated_fails_closed_ub,
    @refCaller_threeWay_lowering_divergence,
    @addCallerInlinedDeadCall_rejected_by_reachableGuards,
    @addCallerInlinedFalseBranchDecoy_reachable_yet_never_calls,
    @outerTwoSiteCaller_calleesCallSitesPreserved,
    @outerTwoSiteHalfInlined_calleesCallBoundary_not_callSites,
    @outerCaller_deadDecoyHelper_passes_syntactic_rejected_by_reachable,
    @outerTwoSiteCaller_reachableCalleesCallSitesPreserved,
    @outerCallerFullyInlined_fools_callees_guards,
    @outerCaller_helperChainCallBoundaryPreserved,
    @outerCaller_inlinedHelper_not_helperChain,
    @grandCaller_twoHop_helperChain_fails_on_linked_hop,
    @grandCaller_twoHop_callChainCallBoundaryPreserved,
    @grandCaller_twoHop_broken_links_rejected,
    @addCaller_wrongAnswer_treeSafe_not_panicsOnlyIf,
    @addCaller_unexpectedAbort_treeSafe_not_panicsOnlyIf,
    @checkedAddU8_externalClosedCallee_totalExactPolicy,
    @outerCaller_linked_totalExact_via_callee_contract,
    @ubOnTwo_to_definedOnTwo_compilerPass,
    @definedOnTwo_to_ubOnTwo_verifierPass,
    @ubOnTwo_to_definedOnTwo_not_exactPass,
    @ubOnTwo_nonExact_pass_variance_transfers,
    @alwaysPanic_to_infiniteLoop_compilerPass,
    @alwaysPanic_panicsIf_infiniteLoop_not_panicsIf,
    @dispatchCaller_chain_guard_vs_runtime,
    @outerCaller_chain_not_traitDispatched⟩

/--
info: 'Anneal.PanicContractsTests.all_panic_contracts_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms all_panic_contracts_tests

end Anneal.PanicContractsTests
