import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.Rustc.V2026_06_01.SymReflect

namespace Anneal.Rustc.V2026_06_01.SymbolicEvalTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
Kernel-checked test suite for `Anneal.Rustc.V2026_06_01.SymbolicEval`:
1. Straight-line symbolic arithmetic verification (`Claim`, `TotalClaim`, and
   `MirContractHoldsWithSafety` across panicking and non-panicking inputs).
2. Branching (`SwitchInt`) symbolic verification paired with multi-block
   short-circuit `#[spec]` boolean companion predicates (`MirBoolPredicateHolds`),
   plus one-call pinned `#[spec]` combinators (`dischargeRustEqU32`,
   `dischargeRustEq2U8`).
3. Stateful Tree Borrows pointer read/write verification (`StatefulClaim`,
   `verifyStatefulMirNoPanicSym`, `dischargeStatefulEq`).
4. Negative UB refutation tests (`refuteClaimByBoundedUB`,
   `refuteTotalClaimByBoundedUB`, `refuteStatefulClaimByBoundedUB`).
5. Non-vacuity witness helpers (`proveNonVacuousPre`,
   `proveNonVacuousStatefulPre`, `proveNonVacuousBoolSpecPre`).
-/

/-! ## Helper Constructors for Self-Contained `CapturedMir` Test Bodies -/

private def u8MirTy : Ty := { kind := .uint .u8, layoutIdx := 0 }
private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
private def u8CheckedTupleTy : Ty :=
  { kind := .tuple [.uint .u8, .bool], layoutIdx := 0 }
private def u8MutRefMirTy : Ty :=
  { kind := .ref .mut (.uint .u8), layoutIdx := 0 }

private def u8ConstOperand (n : Nat) : Operand :=
  .constant { ty := u8MirTy, val := .scalar (.int { bits := n, sizeBytes := 1 }) }

private def u32ConstOperand (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

private def boolConstOperand (b : Bool) : Operand :=
  .constant
    { ty := boolMirTy
      val := .scalar (.int { bits := if b then 1 else 0, sizeBytes := 1 }) }

private def defaultU8TypeLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

private def defaultTestFnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU8TypeLayout, mode := .direct }
  conv := .rust
  canUnwind := true
}

private def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

private def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "SymbolicEvalTests.lean" }

private def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "SymbolicEvalTests.lean" }

private def mkMirBody
    (defPath : DefPath)
    (argCount : Nat)
    (localDecls : List LocalDecl)
    (basicBlocks : List BasicBlockData)
    (role : ContractRole := .subject) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks, role
  phase := .runtimePostCleanup
  fnAbi := defaultTestFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/-! ## 1. Straight-Line Symbolic Checked Arithmetic (`VerificationResult`, `TotalVerificationResult`, `MirContractHoldsWithSafety`) -/

/--
`pub fn add_bounded(a: u8, b: u8) -> u8 { a + b }` lowered with
`BinOp.addWithOverflow` (`_3 = AddWithOverflow(_1, _2)`), `Assert(!move (_3.1))`,
and `_0 = copy (_3.0)`.
-/
def addBoundedMir : CapturedMir :=
  mkMirBody "sym_test::add_bounded" 2
    [ mkDecl .mut u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut u8CheckedTupleTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.binaryOp .addWithOverflow
                (.copy { local_ := 1, projection := [] })
                (.copy { local_ := 2, projection := [] }))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolMirTy] })
            false
            1
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 3, projection := [.field 0 u8MirTy] })))
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def addBoundedClaim : Claim where
  body := addBoundedMir
  pre args :=
    ∃ a b : Nat,
      a < 100 ∧ b < 100 ∧
      args = [.scalar { bits := a, sizeBytes := 1 },
              .scalar { bits := b, sizeBytes := 1 }]
  post args ret :=
    ∀ a b : Nat,
      args = [.scalar { bits := a, sizeBytes := 1 },
              .scalar { bits := b, sizeBytes := 1 }] →
      ret = .scalar { bits := a + b, sizeBytes := 1 }

/-- Single-pass symbolic verification of `add_bounded` over all `10,000` `(a, b)` pairs. -/
theorem addBoundedClaim_verified : VerificationResult addBoundedClaim := by
  refine verifyWellTypedScalarArg2 addBoundedClaim 8 1 1 ?_ ?_
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, b, by dsimp [scalarModulus, scalarPow2]; omega,
                 by dsimp [scalarModulus, scalarPow2]; omega, rfl⟩
  · intro a b _ _ ⟨a', b', ha', hb', heq⟩
    simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl⟩
    (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
    · simp_all; omega
    · intro a'' b'' h_args
      simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at h_args
      rcases h_args with ⟨rfl, rfl⟩
      simp; omega

def addBoundedTotalClaim : TotalClaim where
  body := addBoundedMir
  pre args mem :=
    ∃ a b : Nat,
      a < 100 ∧ b < 100 ∧
      args = [.scalar { bits := a, sizeBytes := 1 },
              .scalar { bits := b, sizeBytes := 1 }] ∧
      mem = emptyMemory
  post _ _ ret mem' :=
    (∃ s : Nat, s < 200 ∧ ret = .scalar { bits := s, sizeBytes := 1 }) ∧
    mem' = emptyMemory

/-- Single-pass total-correctness (`DWP`) symbolic verification of `add_bounded`. -/
theorem addBoundedTotalClaim_verified :
    TotalVerificationResult addBoundedTotalClaim := by
  refine verifyTotalMirSym addBoundedTotalClaim 8 ?_
  rintro _ _ ⟨a, b, ha, hb, rfl, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · simp_all; omega
  · exact ⟨⟨a + b, by omega, by simp; omega⟩, rfl⟩

/--
`pub fn advance_offset(offset: u8) -> u8 { offset + 4 }` verified across ALL 256
`u8` inputs (`WellTypedScalarArg1 1`): inputs `< 252` return `offset + 4`, while
overflowing inputs `252 ≤ offset < 256` panic safely without UB.
-/
def advanceOffsetSymMir : CapturedMir :=
  mkMirBody "sym_test::advance_offset" 1
    [ mkDecl .mut u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut u8CheckedTupleTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign { local_ := 2, projection := [] }
              (.binaryOp .addWithOverflow
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 4))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 2, projection := [.field 1 boolMirTy] })
            false
            1
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 2, projection := [.field 0 u8MirTy] })))
          , mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def advanceOffsetSymPre (args : List Value) : Prop :=
  ∃ b : Nat, b < 252 ∧ args = [.scalar { bits := b, sizeBytes := 1 }]

def advanceOffsetSymPost (args : List Value) (ret : Value) : Prop :=
  ∀ b : Nat,
    args = [.scalar { bits := b, sizeBytes := 1 }] →
    ret = .scalar { bits := b + 4, sizeBytes := 1 }

def advanceOffsetSymClaim : Claim where
  body := advanceOffsetSymMir
  pre := WellTypedScalarArg1 1
  post args ret := advanceOffsetSymPre args → advanceOffsetSymPost args ret

theorem advanceOffsetSymClaim_verified :
    VerificationResult advanceOffsetSymClaim := by
  refine verifyWellTypedSafeScalarArg1 advanceOffsetSymClaim 8 1 (fun _ h => h) ?_
  intro b hb _
  dsimp [scalarModulus, scalarPow2] at hb
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · trivial
  · rintro ⟨b', hb', h_pre⟩ b'' h_args
    simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at h_pre h_args
    subst h_pre; subst h_args
    simp; omega

theorem advanceOffsetSym_holdsWithSafety :
    MirContractHoldsWithSafety
      advanceOffsetSymMir
      (WellTypedScalarArg1 1)
      advanceOffsetSymPre
      advanceOffsetSymPost :=
  (mirContractHoldsWithSafety_iff_mirContractHolds_imp
    advanceOffsetSymMir
    (WellTypedScalarArg1 1)
    advanceOffsetSymPre
    advanceOffsetSymPost).2
    advanceOffsetSymClaim_verified.proof

/-! ## 2. Branching (`SwitchInt`) Symbolic Verification & `#[spec]` Boolean Companions -/

/--
`pub fn clamp_or_step(x: u8) -> u8 { if x < 10 { x + 1 } else { 10 } }`:
- `bb0`: `_2 = Lt(_1, 10_u8); switchInt(_2) [0 -> bb2, otherwise -> bb1]`
- `bb1`: `_3 = AddWithOverflow(_1, 1_u8); assert(!_3.1) -> bb3`
- `bb2`: `_0 = 10_u8; goto -> bb4`
- `bb3`: `_0 = copy (_3.0); goto -> bb4`
- `bb4`: `return`
-/
def clampOrStepMir : CapturedMir :=
  mkMirBody "sym_test::clamp_or_step" 1
    [ mkDecl .mut u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut boolMirTy
    , mkDecl .mut u8CheckedTupleTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign { local_ := 2, projection := [] }
              (.binaryOp .lt
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 10))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 2, projection := [] })
            { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.binaryOp .addWithOverflow
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 1))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolMirTy] })
            false
            3
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (u8ConstOperand 10))) ]
        terminator := mkTerm (.goto 4)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 3, projection := [.field 0 u8MirTy] })))
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm (.goto 4)
        isCleanup := false }
    , { statements := [ mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

/--
Multi-block short-circuit `#[spec(requires: x < 20 && !(x == 15))]` companion:
- `bb0`: `_2 = Lt(_1, 20_u8); switchInt(_2) [0 -> bb2, otherwise -> bb1]`
- `bb1`: `_3 = Eq(_1, 15_u8); _0 = Not(_3); goto -> bb3`
- `bb2`: `_0 = false; goto -> bb3`
- `bb3`: `return`
-/
def clampReqMir : CapturedMir :=
  mkMirBody "sym_test::__anodized_fn_requires_clamp_or_step" 1
    [ mkDecl .mut boolMirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut boolMirTy
    , mkDecl .mut boolMirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign { local_ := 2, projection := [] }
              (.binaryOp .lt
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 20))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 2, projection := [] })
            { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 15)))
          , mkStmt (.assign { local_ := 0, projection := [] }
              (.unaryOp .not (.copy { local_ := 3, projection := [] })))
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (boolConstOperand false))) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements := [ mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.requires "sym_test::clamp_or_step")

/-- `#[spec(ensures: |ret| ret <= 10)]` companion taking `(x, ret)` -> `bool`. -/
def clampEnsMir : CapturedMir :=
  mkMirBody "sym_test::__anodized_fn_ensures_clamp_or_step" 2
    [ mkDecl .mut boolMirTy
    , mkDecl .not u8MirTy
    , mkDecl .not u8MirTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .le
                (.copy { local_ := 2, projection := [] })
                (u8ConstOperand 10))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.ensures "sym_test::clamp_or_step")

def clampOrStepClaim : Claim where
  body := clampOrStepMir
  pre args :=
    WellTypedScalarArg1 1 args ∧ MirBoolPredicateHolds clampReqMir args
  post args ret :=
    MirBoolPredicateHolds clampEnsMir (args ++ [ret]) ∧
    (∀ x : Nat,
      args = [.scalar { bits := x, sizeBytes := 1 }] →
      ret = .scalar { bits := if x < 10 then x + 1 else 10, sizeBytes := 1 })

/--
Symbolic equivalence test for `mirBoolPredicateHolds_iff_wpMirBoolSym` on the
multi-block short-circuit `clampReqMir` predicate over all canonical `u8` inputs.
-/
theorem clampReqMir_iff_arith (x : Nat) :
    MirBoolPredicateHolds clampReqMir [.scalar { bits := x, sizeBytes := 1 }] ↔
      (x < 20 ∧ x ≠ 15) := by
  have h_iff :=
    mirBoolPredicateHolds_iff_wpMirBoolSym 12 clampReqMir
      [.scalar { bits := x, sizeBytes := 1 }] (by
        ((repeat' ((conv => whnf); split)); all_goals (conv => whnf)) <;> trivial)
  rw [h_iff]
  constructor
  · intro h
    (repeat' ((conv at h => whnf); split at h))
    all_goals (conv at h => whnf)
    all_goals (try exact False.elim h)
    all_goals simp_all
    all_goals omega
  · rintro ⟨hx20, hx15⟩
    (repeat' ((conv => whnf); split))
    all_goals (conv => whnf)
    all_goals simp_all
    all_goals omega

/--
Single-pass symbolic verification of branching `clampOrStepMir` with `#[spec]`
boolean companion `requires` (`clampReqMir`) and `ensures` (`clampEnsMir`).
-/
theorem clampOrStepClaim_verified : VerificationResult clampOrStepClaim := by
  refine verifyWellTypedScalarArg1 clampOrStepClaim 12 1 (fun _ h => h.1) ?_
  intro x hx ⟨_, h_req⟩
  dsimp [scalarModulus, scalarPow2] at hx
  have h_req_sym :=
    holdBoolMirSym_of_mirBoolPredicateHolds 12 clampReqMir
      [.scalar { bits := x, sizeBytes := 1 }] h_req
  have hx20 : x < 20 := by
    (repeat' ((conv at h_req_sym => whnf); split at h_req_sym))
    all_goals (conv at h_req_sym => whnf)
    all_goals (try exact False.elim h_req_sym)
    all_goals simp_all
    all_goals omega
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · refine ⟨mirBoolPredicateHolds_of_wpMirSym 8 clampEnsMir _ (by
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)), ?_⟩
    intro x' h_args
    simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at h_args
    subst h_args
    have h_not_lt : ¬ (x < 10) := by simp_all
    simp [h_not_lt]
  · simp_all; omega
  · have h_wrap : (x + 1) % 256 = x + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨mirBoolPredicateHolds_of_wpMirSym 8 clampEnsMir _ (by
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      simp_all; omega), ?_⟩
    intro x' h_args
    simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at h_args
    subst h_args
    have h_lt10 : x < 10 := by simp_all
    simp [h_lt10, h_wrap]

/-- Pinned 1-argument `u32` `#[spec(requires: magic == 7, ensures: ret == 7)]` test. -/
def pinMagicMir : CapturedMir :=
  mkMirBody "sym_test::pin_magic" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 1, projection := [] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def pinMagicReqMir : CapturedMir :=
  mkMirBody "sym_test::req_pin_magic" 1
    [mkDecl .mut boolMirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 1, projection := [] })
                (u32ConstOperand 7))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.requires "sym_test::pin_magic")

def pinMagicEnsMir : CapturedMir :=
  mkMirBody "sym_test::ens_pin_magic" 2
    [mkDecl .mut boolMirTy, mkDecl .not u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 2, projection := [] })
                (u32ConstOperand 7))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.ensures "sym_test::pin_magic")

def pinMagicClaim : Claim where
  body := pinMagicMir
  pre args :=
    And (Trusted.Sequence.length args = 1) (MirBoolPredicateHolds pinMagicReqMir args)
  post args ret :=
    MirBoolPredicateHolds pinMagicEnsMir (args ++ [ret])

theorem pinMagicClaim_verified : VerificationResult pinMagicClaim :=
  dischargeRustEqU32 pinMagicClaim 8 16 pinMagicReqMir pinMagicEnsMir 7

/-- Pinned 2-argument `(u8, u8)` short-circuit `&&` `#[spec]` test for `dischargeRustEq2U8`. -/
def totalFrameLenReqMir : CapturedMir :=
  mkMirBody "sym_test::req_total_frame_len" 2
    [ mkDecl .mut boolMirTy
    , mkDecl .not u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut boolMirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 1))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 3, projection := [] })
            { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 2, projection := [] })
                (u8ConstOperand 2))) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (boolConstOperand false))) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements := [ mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.requires "sym_test::add_bounded")

def totalFrameLenEnsMir : CapturedMir :=
  mkMirBody "sym_test::ens_total_frame_len" 3
    [ mkDecl .mut boolMirTy
    , mkDecl .not u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .not u8MirTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 3, projection := [] })
                (u8ConstOperand 3))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.ensures "sym_test::add_bounded")

def totalFrameLenClaim : Claim where
  body := addBoundedMir
  pre args :=
    And (Trusted.Sequence.length args = 2)
        (MirBoolPredicateHolds totalFrameLenReqMir args)
  post args ret :=
    MirBoolPredicateHolds totalFrameLenEnsMir (args ++ [ret])

theorem totalFrameLenClaim_verified : VerificationResult totalFrameLenClaim :=
  dischargeRustEq2U8 totalFrameLenClaim 16 16
    totalFrameLenReqMir totalFrameLenEnsMir 1 2

/-! ## 3. Stateful Tree Borrows Pointer Read & Mutation (`StatefulVerificationResult`) -/

/--
`pub unsafe fn write_and_read_mut(hdr: &mut u8, ver: u8) -> u8 { *hdr = ver; *hdr }`
-/
def writeAndReadMutMir : CapturedMir :=
  mkMirBody "sym_test::write_and_read_mut" 2
    [ mkDecl .mut u8MirTy
    , mkDecl .not u8MutRefMirTy
    , mkDecl .not u8MirTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 1, projection := [.deref] }
              (.use (.copy { local_ := 2, projection := [] })))
          , mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 1, projection := [.deref] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def activeMutBorrowEntry : BorrowEntry where
  tag := 1
  perm := .active
  targetLocal := 2
  targetProjection := []
  protector := some 1
  rangeOffset := 0
  rangeLen := 1

def activeMutMem : Memory :=
  { emptyMemory with
    borrows := [activeMutBorrowEntry]
    nextTag := 2
    activeProtectors := [1]
    nextProtector := 2 }

def writeAndReadMutSymClaim : StatefulClaim where
  body := writeAndReadMutMir
  pre args mem :=
    ∃ v : Nat,
      v < 256 ∧
      args = [.ptr { allocId := 1, offsetBytes := 0 } 8,
              .scalar { bits := v, sizeBytes := 1 }] ∧
      mem = activeMutMem
  post args _ ret mem' :=
    (∀ v : Nat,
      args = [.ptr { allocId := 1, offsetBytes := 0 } 8,
              .scalar { bits := v, sizeBytes := 1 }] →
      ret = .scalar { bits := v, sizeBytes := 1 }) ∧
    mem' = activeMutMem

/-- Symbolic stateful verification for ALL `256` values of `ver: u8`. -/
theorem writeAndReadMutSymClaim_verified :
    StatefulVerificationResult writeAndReadMutSymClaim := by
  refine verifyStatefulMirNoPanicSym writeAndReadMutSymClaim 8 ?_
  rintro _ _ ⟨v, hv, rfl, rfl⟩
  exact ⟨fun v' h_eq => by simp at h_eq; subst h_eq; rfl, rfl⟩

def writeAndReadMutPinnedClaim : StatefulClaim where
  body := writeAndReadMutMir
  pre args mem :=
    args = [.ptr { allocId := 1, offsetBytes := 0 } 8,
            .scalar { bits := 42, sizeBytes := 1 }] ∧
    mem = activeMutMem
  post _ _ ret mem' :=
    ret = .scalar { bits := 42, sizeBytes := 1 } ∧ mem' = activeMutMem

/-- Concrete pinned stateful verification via `dischargeStatefulEq` + `⟨rfl, rfl⟩`. -/
theorem writeAndReadMutPinnedClaim_verified :
    StatefulVerificationResult writeAndReadMutPinnedClaim :=
  dischargeStatefulEq
    writeAndReadMutPinnedClaim
    8
    [.ptr { allocId := 1, offsetBytes := 0 } 8,
     .scalar { bits := 42, sizeBytes := 1 }]
    activeMutMem
    (fun _ _ h => h)
    ⟨rfl, rfl⟩

/-! ## 4. Negative Bounded UB Refutation Tests -/

/-- `unsafe { a.unchecked_add(b) }` on `u8` (`BinOp.addUnchecked`). -/
def uncheckedAddU8Mir : CapturedMir :=
  mkMirBody "sym_test::unchecked_add_u8" 2
    [mkDecl .mut u8MirTy, mkDecl .not u8MirTy, mkDecl .not u8MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .addUnchecked
                (.copy { local_ := 1, projection := [] })
                (.copy { local_ := 2, projection := [] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def uncheckedOverflowClaim : Claim where
  body := uncheckedAddU8Mir
  pre := WellTypedScalarArg2 1 1
  post _ _ := True

/-- Refutes `uncheckedOverflowClaim` in 1 line at `(200_u8, 100_u8)` (`300 ≥ 256` UB). -/
theorem not_uncheckedOverflowClaim_holds : ¬ uncheckedOverflowClaim.holds :=
  refuteClaimByBoundedUB
    uncheckedOverflowClaim
    8
    [.scalar { bits := 200, sizeBytes := 1 },
     .scalar { bits := 100, sizeBytes := 1 }]
    ⟨200, 100, by decide, by decide, rfl⟩

def uncheckedOverflowTotalClaim : TotalClaim where
  body := uncheckedAddU8Mir
  pre args mem := WellTypedScalarArg2 1 1 args ∧ mem = emptyMemory
  post _ _ _ _ := True

/-- Refutes `uncheckedOverflowTotalClaim` in 1 line at `(200_u8, 100_u8)`. -/
theorem not_uncheckedOverflowTotalClaim_holds :
    ¬ uncheckedOverflowTotalClaim.holds :=
  refuteTotalClaimByBoundedUB
    uncheckedOverflowTotalClaim
    8
    [.scalar { bits := 200, sizeBytes := 1 },
     .scalar { bits := 100, sizeBytes := 1 }]
    emptyMemory
    ⟨⟨200, 100, by decide, by decide, rfl⟩, rfl⟩

def frozenBorrowMem : Memory :=
  { emptyMemory with
    borrows := [{ activeMutBorrowEntry with perm := .frozen }]
    nextTag := 2
    activeProtectors := [1]
    nextProtector := 2 }

def frozenWriteStatefulClaim : StatefulClaim where
  body := writeAndReadMutMir
  pre args mem :=
    args = [.ptr { allocId := 1, offsetBytes := 0 } 8,
            .scalar { bits := 42, sizeBytes := 1 }] ∧
    mem = frozenBorrowMem
  post _ _ _ _ := True

/-- Refutes writing `*hdr = 42_u8` through a `.frozen` Tree Borrows tag (`¬ claim.holds`). -/
theorem not_frozenWriteStatefulClaim_holds :
    ¬ frozenWriteStatefulClaim.holds :=
  refuteStatefulClaimByBoundedUB
    frozenWriteStatefulClaim
    8
    [.ptr { allocId := 1, offsetBytes := 0 } 8,
     .scalar { bits := 42, sizeBytes := 1 }]
    frozenBorrowMem
    ⟨rfl, rfl⟩

/-! ## 5. Non-Vacuity Witness Tests -/

theorem addBoundedClaim_pre_nonVacuous : ∃ a, addBoundedClaim.pre a :=
  proveNonVacuousPre
    [.scalar { bits := 10, sizeBytes := 1 },
     .scalar { bits := 20, sizeBytes := 1 }]
    ⟨10, 20, by omega, by omega, rfl⟩

theorem writeAndReadMutSymClaim_pre_nonVacuous :
    ∃ a m, writeAndReadMutSymClaim.pre a m :=
  proveNonVacuousStatefulPre
    [.ptr { allocId := 1, offsetBytes := 0 } 8,
     .scalar { bits := 7, sizeBytes := 1 }]
    activeMutMem
    ⟨7, by omega, rfl, rfl⟩

theorem clampReqMir_pre_nonVacuous :
    ∃ a, Trusted.Sequence.length a = 1 ∧ MirBoolPredicateHolds clampReqMir a :=
  proveNonVacuousBoolSpecPre
    12
    1
    clampReqMir
    [.scalar { bits := 5, sizeBytes := 1 }]

/-! ## 6. Differential Testing Verdict & Strict UB / Safe Panic Combinator Tests -/

/--
Certifies Miri `pass` agreement on `addBoundedMir` at `(10_u8, 20_u8) -> 30_u8`
via `verifyTotalMirScalarPointBounded`.
-/
theorem addBounded_diff_pass_verified :
    TotalVerificationResult
      { body := addBoundedMir
        pre := fun a m =>
          a = [.scalar { bits := 10, sizeBytes := 1 },
               .scalar { bits := 20, sizeBytes := 1 }] ∧
          m = emptyMemory
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := 30, sizeBytes := 1 } } :=
  verifyTotalMirScalarPointBounded
    addBoundedMir
    8
    [.scalar { bits := 10, sizeBytes := 1 },
     .scalar { bits := 20, sizeBytes := 1 }]
    emptyMemory
    30
    1

/--
Certifies Miri `panic` agreement on `advanceOffsetSymMir` at `255_u8` (`255 + 4`
overflows `u8` and unwinds via `TerminatorKind.assert`): proves both UB-freedom
(`StatefulVerificationResult` with `post := False`) and `¬ TotalClaim.holds`.
-/
theorem advanceOffset_diff_panic_verified :
    StatefulVerificationResult
      { body := advanceOffsetSymMir
        pre := fun a m =>
          a = [.scalar { bits := 255, sizeBytes := 1 }] ∧ m = emptyMemory
        post := fun _ _ _ _ => False } ∧
    ¬ ({ body := advanceOffsetSymMir
         pre := fun a m =>
           a = [.scalar { bits := 255, sizeBytes := 1 }] ∧ m = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  verifySafePanicMirPointBounded
    advanceOffsetSymMir
    8
    [.scalar { bits := 255, sizeBytes := 1 }]
    emptyMemory

/--
Certifies Miri `fail` (Undefined Behavior) agreement on `uncheckedAddU8Mir` at
`(200_u8, 100_u8)` via `refuteMirPointByStrictUB`, proving that the fault is
specifically `FailureKind.ub` (not `.unsupported`) and refuting both
`StatefulClaim.holds` and `TotalClaim.holds`.
-/
theorem uncheckedAdd_diff_strict_ub_refuted :
    ¬ ({ body := uncheckedAddU8Mir
         pre := fun a m =>
           a = [.scalar { bits := 200, sizeBytes := 1 },
                .scalar { bits := 100, sizeBytes := 1 }] ∧
           m = emptyMemory
         post := fun _ _ _ _ => True } : StatefulClaim).holds ∧
    ¬ ({ body := uncheckedAddU8Mir
         pre := fun a m =>
           a = [.scalar { bits := 200, sizeBytes := 1 },
                .scalar { bits := 100, sizeBytes := 1 }] ∧
           m = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  refuteMirPointByStrictUB
    uncheckedAddU8Mir
    8
    [.scalar { bits := 200, sizeBytes := 1 },
     .scalar { bits := 100, sizeBytes := 1 }]
    emptyMemory

end Anneal.Rustc.V2026_06_01.SymbolicEvalTests
