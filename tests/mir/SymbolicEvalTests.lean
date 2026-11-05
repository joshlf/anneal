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

/-! ## 12. Bound-Independent Symbolic Range Reflection (`dischargeRustSymRange1Auto`) -/

private def u32CheckedTupleTy : Ty :=
  { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }

/-- `pub fn clamp_add_one(x: u32) -> u32 { x + 1 }` with `requires: x < 1000`
and `ensures: |ret: u32| ret <= 1000`. -/
def clampAddOneMir : CapturedMir :=
  mkMirBody "sym_test::clamp_add_one" 1
    [ mkDecl .mut u32MirTy
    , mkDecl .not u32MirTy
    , mkDecl .mut u32CheckedTupleTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.assign { local_ := 2, projection := [] }
              (.binaryOp .addWithOverflow
                (.copy { local_ := 1, projection := [] })
                (u32ConstOperand 1))) ]
        terminator :=
          mkTerm (.assert
            (.move { local_ := 2, projection := [.field 1 boolMirTy] })
            false
            1
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 2, projection := [.field 0 u32MirTy] })))
          , mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

def clampAddOneReq1000Mir : CapturedMir :=
  mkMirBody "sym_test::__anodized_fn_requires_clamp_add_one" 1
    [mkDecl .mut boolMirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .lt
                (.copy { local_ := 1, projection := [] })
                (u32ConstOperand 1000))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.requires "sym_test::clamp_add_one")

def clampAddOneEns1000Mir : CapturedMir :=
  mkMirBody "sym_test::__anodized_fn_ensures_clamp_add_one" 2
    [mkDecl .mut boolMirTy, mkDecl .not u32MirTy, mkDecl .not u32MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .le
                (.copy { local_ := 2, projection := [] })
                (u32ConstOperand 1000))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.ensures "sym_test::clamp_add_one")

def clampAddOne1000Claim : Claim where
  body := clampAddOneMir
  pre args :=
    Trusted.Sequence.length args = 1 ∧
      MirBoolPredicateHolds clampAddOneReq1000Mir args
  post args ret :=
    MirBoolPredicateHolds clampAddOneEns1000Mir (args ++ [ret])

theorem clampAddOne1000_verified : VerificationResult clampAddOne1000Claim := by
  exact dischargeRustSymRange1Auto
    clampAddOne1000Claim 16 16
    clampAddOneReq1000Mir
    (.some clampAddOneEns1000Mir)

/-! ## 8. Multi-Frame `callees` Symbolic Execution (`core::slice::*` & `RangeBounds::contains` via `traitImpls` and Polymorphic `CapturedMir.instantiate`) -/

private def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
private def paramTMirTy : Ty := { kind := .param 0 "T", layoutIdx := 0 }
private def sliceRefParamTMirTy : Ty :=
  { kind := .ref .not (.slice (.param 0 "T")), layoutIdx := 0 }
private def sliceMutRefParamTMirTy : Ty :=
  { kind := .ref .mut (.slice (.param 0 "T")), layoutIdx := 0 }
private def rawConstPtrParamTMirTy : Ty :=
  { kind := .rawPtr .not (.param 0 "T"), layoutIdx := 0 }
private def rawMutPtrParamTMirTy : Ty :=
  { kind := .rawPtr .mut (.param 0 "T"), layoutIdx := 0 }
private def rawMutSliceParamTMirTy : Ty :=
  { kind := .rawPtr .mut (.slice (.param 0 "T")), layoutIdx := 0 }
private def sliceRefU8MirTy : Ty :=
  { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
private def sliceMutRefU8MirTy : Ty :=
  { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 0 }
private def rawConstPtrU8MirTy : Ty :=
  { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private def rawMutPtrU8MirTy : Ty :=
  { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
private def splitTupleParamTMirTy : Ty :=
  { kind := .tuple [sliceMutRefParamTMirTy.kind, sliceMutRefParamTMirTy.kind], layoutIdx := 0 }
private def splitTupleU8MirTy : Ty :=
  { kind := .tuple [sliceMutRefU8MirTy.kind, sliceMutRefU8MirTy.kind], layoutIdx := 0 }
private def rangeUsizeMirTy : Ty :=
  { kind := .adt "core::ops::range::Range" [.uint .usize], layoutIdx := 0 }

private def fnConstOp (defPath : DefPath) (typeArgs : List RigidTy := []) : Operand :=
  .constant
    { ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
      val := .zeroSized }

private def sliceCallerLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [defaultU8TypeLayout]
}

/--
Polymorphic `core::slice::<impl [T]>::len`:
`_0 = PtrMetadata(move _1); return`.
-/
def coreSliceLenMir : CapturedMir := {
  mkMirBody "core::slice::<impl [T]>::len" 1
    [mkDecl .mut usizeMirTy, mkDecl .not sliceRefParamTMirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.unaryOp .ptrMetadata (.move { local_ := 1, projection := [] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts := sliceCallerLayouts
}

/--
Polymorphic `core::slice::<impl [T]>::as_ptr`:
`_0 = move _1 as *const T (PtrToPtr); return`.
-/
def coreSliceAsPtrMir : CapturedMir := {
  mkMirBody "core::slice::<impl [T]>::as_ptr" 1
    [ mkDecl .mut rawConstPtrParamTMirTy
    , mkDecl .not sliceRefParamTMirTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.cast .ptrToPtr
                (.move { local_ := 1, projection := [] })
                rawConstPtrParamTMirTy)) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts := sliceCallerLayouts
}

/--
Polymorphic `core::slice::from_raw_parts_mut`:
`_0 = *mut [T] from (copy _1, copy _2); return`.
-/
def coreSliceFromRawPartsMutMir : CapturedMir := {
  mkMirBody "core::slice::from_raw_parts_mut" 2
    [ mkDecl .mut sliceMutRefParamTMirTy
    , mkDecl .not rawMutPtrParamTMirTy
    , mkDecl .not usizeMirTy ]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.aggregate (.rawPtr { kind := .slice (.param 0 "T"), layoutIdx := 0 } .mut)
                [ .copy { local_ := 1, projection := [] }
                , .copy { local_ := 2, projection := [] } ])) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts := sliceCallerLayouts
}

/--
`core::slice::<impl [T]>::split_at_mut` (calling polymorphic
`core::slice::<impl [T]>::len::<u8>` and `core::slice::from_raw_parts_mut::<u8>`
across nested stack frames):
- `bb0`: `_3 = core::slice::<impl [T]>::len::<u8>(copy _1) -> bb1`
- `bb1`: `_4 = copy _1 as *mut u8 (PtrToPtr); _5 = Offset(copy _4, copy _2);
         _7 = core::slice::from_raw_parts_mut::<u8>(copy _4, copy _2) -> bb2`
- `bb2`: `_6 = Sub(copy _3, copy _2);
         _8 = core::slice::from_raw_parts_mut::<u8>(copy _5, copy _6) -> bb3`
- `bb3`: `_0 = (move _7, move _8); return`
-/
def coreSliceSplitAtMutMir : CapturedMir := {
  mkMirBody "core::slice::<impl [T]>::split_at_mut" 2
    [ mkDecl .mut splitTupleU8MirTy     -- _0: (&mut [u8], &mut [u8])
    , mkDecl .not sliceMutRefU8MirTy    -- _1: &mut [u8]
    , mkDecl .not usizeMirTy            -- _2: mid: usize
    , mkDecl .mut usizeMirTy            -- _3: len: usize
    , mkDecl .mut rawMutPtrU8MirTy      -- _4: ptr: *mut u8
    , mkDecl .mut rawMutPtrU8MirTy      -- _5: right_ptr: *mut u8
    , mkDecl .mut usizeMirTy            -- _6: right_len: usize
    , mkDecl .mut sliceMutRefU8MirTy    -- _7: left_slice: &mut [u8]
    , mkDecl .mut sliceMutRefU8MirTy ]  -- _8: right_slice: &mut [u8]
    [ { statements := [ mkStmt (.storageLive 3) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::len" [.uint .u8])
            [.copy { local_ := 1, projection := [] }]
            { local_ := 3, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 4)
          , mkStmt (.storageLive 5)
          , mkStmt (.storageLive 6)
          , mkStmt (.storageLive 7)
          , mkStmt (.assign { local_ := 4, projection := [] }
              (.cast .ptrToPtr
                (.copy { local_ := 1, projection := [] })
                rawMutPtrU8MirTy))
          , mkStmt (.assign { local_ := 5, projection := [] }
              (.binaryOp .offset
                (.copy { local_ := 4, projection := [] })
                (.copy { local_ := 2, projection := [] }))) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::from_raw_parts_mut" [.uint .u8])
            [ .copy { local_ := 4, projection := [] }
            , .copy { local_ := 2, projection := [] } ]
            { local_ := 7, projection := [] }
            (.some 2)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageLive 8)
          , mkStmt (.assign { local_ := 6, projection := [] }
              (.binaryOp .sub
                (.copy { local_ := 3, projection := [] })
                (.copy { local_ := 2, projection := [] }))) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::from_raw_parts_mut" [.uint .u8])
            [ .copy { local_ := 5, projection := [] }
            , .copy { local_ := 6, projection := [] } ]
            { local_ := 8, projection := [] }
            (.some 3)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [ .move { local_ := 7, projection := [] }
                , .move { local_ := 8, projection := [] } ])) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

/--
Caller `sliceLenAsPtrFromRawPartsMir` that invokes polymorphic
`core::slice::<impl [T]>::len::<u8>`, `core::slice::<impl [T]>::as_ptr::<u8>`,
and `core::slice::from_raw_parts_mut::<u8>` in sequence to reconstruct a mutable
slice from its raw pointer and length.
-/
def sliceLenAsPtrFromRawPartsMir : CapturedMir := {
  mkMirBody "sym_test::slice_len_as_ptr_from_raw_parts" 1
    [ mkDecl .mut sliceMutRefU8MirTy    -- _0: &mut [u8]
    , mkDecl .not sliceMutRefU8MirTy    -- _1: slice: &mut [u8]
    , mkDecl .mut usizeMirTy            -- _2: len: usize
    , mkDecl .mut rawConstPtrU8MirTy    -- _3: const_ptr: *const u8
    , mkDecl .mut rawMutPtrU8MirTy ]    -- _4: mut_ptr: *mut u8
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.storageLive 3)
          , mkStmt (.storageLive 4) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::len" [.uint .u8])
            [.copy { local_ := 1, projection := [] }]
            { local_ := 2, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::as_ptr" [.uint .u8])
            [.copy { local_ := 1, projection := [] }]
            { local_ := 3, projection := [] }
            (.some 2)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 4, projection := [] }
              (.cast .ptrToPtr
                (.move { local_ := 3, projection := [] })
                rawMutPtrU8MirTy)) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::from_raw_parts_mut" [.uint .u8])
            [ .move { local_ := 4, projection := [] }
            , .move { local_ := 2, projection := [] } ]
            { local_ := 0, projection := [] }
            (.some 3)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageDead 4)
          , mkStmt (.storageDead 3)
          , mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def sliceHelperCallees : List CapturedMir :=
  [ coreSliceFromRawPartsMutMir
  , coreSliceLenMir
  , coreSliceAsPtrMir
  , coreSliceSplitAtMutMir ]

def sliceLenAsPtrFromRawPartsClaim : Claim where
  body := sliceLenAsPtrFromRawPartsMir
  callees := [coreSliceLenMir, coreSliceAsPtrMir, coreSliceFromRawPartsMutMir]
  pre args :=
    ∃ (p : ProvenancePtr) (len : Nat),
      args = [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }] ]
  post args ret :=
    args = [ret]

set_option maxHeartbeats 800000 in
/--
Kernel-checked symbolic verification of `sliceLenAsPtrFromRawPartsMir` stepping
through polymorphic `core::slice::<impl [T]>::len::<u8>`,
`core::slice::<impl [T]>::as_ptr::<u8>`, and
`core::slice::from_raw_parts_mut::<u8>` in a single `verifyMirNoPanicSym` pass.
-/
theorem sliceLenAsPtrFromRawParts_verified :
    VerificationResult sliceLenAsPtrFromRawPartsClaim := by
  refine verifyMirNoPanicSym sliceLenAsPtrFromRawPartsClaim 24 ?_
  rintro _ ⟨p, len, rfl⟩
  rfl

/--
Caller `sliceSplitAtMutCallerMir` that invokes `core::slice::<impl [T]>::split_at_mut`
(which internally calls polymorphic `core::slice::<impl [T]>::len::<u8>` and
`core::slice::from_raw_parts_mut::<u8>` twice), exercising multi-frame
`callStack` depth 2 and polymorphic callee instantiation in `s.memory.callees`.
-/
def sliceSplitAtMutCallerMir : CapturedMir := {
  mkMirBody "sym_test::slice_split_at_mut_caller" 2
    [ mkDecl .mut splitTupleU8MirTy     -- _0: (&mut [u8], &mut [u8])
    , mkDecl .not sliceMutRefU8MirTy    -- _1: slice: &mut [u8]
    , mkDecl .not usizeMirTy ]          -- _2: mid: usize
    [ { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::split_at_mut")
            [ .move { local_ := 1, projection := [] }
            , .copy { local_ := 2, projection := [] } ]
            { local_ := 0, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def sliceHelperPipelineClaim : Claim where
  body := sliceSplitAtMutCallerMir
  callees := [coreSliceFromRawPartsMutMir, coreSliceLenMir, coreSliceSplitAtMutMir]
  pre args :=
    ∃ (p : ProvenancePtr) (len mid : Nat),
      mid ≤ len ∧ len < 18446744073709551616 ∧
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ]
  post args ret :=
    ∀ (p : ProvenancePtr) (len mid : Nat),
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ] →
      ret =
        .aggregate 0
          [ .aggregate 0 [.ptr p 8, .scalar { bits := mid, sizeBytes := 8 }]
          , .aggregate 0
              [ .ptr { p with offsetBytes := p.offsetBytes + mid } 8
              , .scalar { bits := len - mid, sizeBytes := 8 } ] ]

set_option maxHeartbeats 800000 in
/--
Kernel-checked symbolic verification of `sliceSplitAtMutCallerMir` stepping
through `split_at_mut`, `len`, and `from_raw_parts_mut` across nested
stack frames (`callStack` depth 2) in a single `verifyMirNoPanicSym` pass.
-/
theorem sliceHelperPipeline_verified :
    VerificationResult sliceHelperPipelineClaim := by
  refine verifyMirNoPanicSym sliceHelperPipelineClaim 28 ?_
  rintro _ ⟨p, len, mid, h_le, h_len, rfl⟩
  have h_ble : Nat.ble mid len = true := Nat.ble_eq_true_of_le h_le
  have h_sub : len - mid < 18446744073709551616 := by omega
  (conv => whnf)
  split
  · (conv => whnf)
    intro p' len' mid' h_args
    simp only [List.cons.injEq, Value.aggregate.injEq, Value.ptr.injEq,
      Value.scalar.injEq, ScalarInt.mk.injEq, and_true, true_and] at h_args
    rcases h_args with ⟨⟨rfl, rfl⟩, rfl⟩
    simp; exact h_sub
  · rename_i h_false
    rw [h_ble] at h_false
    cases h_false

/--
`core::ops::range::<impl RangeBounds<usize> for Range<usize>>::contains`:
takes `_1 : Range<usize>` (`.aggregate 0 [start, end_]`) and `_2 : usize`,
returns `start <= idx && idx < end_`.
-/
def coreRangeContainsImplMir : CapturedMir := {
  mkMirBody "core::ops::range::<impl RangeBounds<usize> for Range<usize>>::contains" 2
    [ mkDecl .mut boolMirTy
    , mkDecl .not rangeUsizeMirTy
    , mkDecl .not usizeMirTy
    , mkDecl .mut boolMirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.binaryOp .le
                (.copy { local_ := 1, projection := [.field 0 usizeMirTy] })
                (.copy { local_ := 2, projection := [] }))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 3, projection := [] })
            { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .lt
                (.copy { local_ := 2, projection := [] })
                (.copy { local_ := 1, projection := [.field 1 usizeMirTy] }))) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (boolConstOperand false))) ]
        terminator := mkTerm (.goto 3)
        isCleanup := false }
    , { statements := [ mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

/--
Caller `rangeBoundsCallerMir` invoking trait method
`"core::ops::range::RangeBounds::contains"` with
`typeArgs = [Range<usize>, usize]`, resolved via `traitImpls`.
-/
def rangeBoundsCallerMir : CapturedMir := {
  mkMirBody "sym_test::check_in_range" 2
    [ mkDecl .mut boolMirTy
    , mkDecl .not rangeUsizeMirTy
    , mkDecl .not usizeMirTy ]
    [ { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::ops::range::RangeBounds::contains"
              [rangeUsizeMirTy.kind, .uint .usize])
            [ .copy { local_ := 1, projection := [] }
            , .copy { local_ := 2, projection := [] } ]
            { local_ := 0, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ] with
  traitImpls :=
    [ { traitRef :=
          { defPath := "core::ops::range::RangeBounds::contains"
            args := [rangeUsizeMirTy.kind, .uint .usize] }
        implPath :=
          "core::ops::range::<impl RangeBounds<usize> for Range<usize>>::contains" } ]
  layouts := sliceCallerLayouts
}

def rangeBoundsCallerClaim : Claim where
  body := rangeBoundsCallerMir
  callees := [coreRangeContainsImplMir]
  pre args :=
    ∃ start end_ idx : Nat,
      start ≤ idx ∧ idx < end_ ∧
      args =
        [ .aggregate 0
            [ .scalar { bits := start, sizeBytes := 8 }
            , .scalar { bits := end_, sizeBytes := 8 } ]
        , .scalar { bits := idx, sizeBytes := 8 } ]
  post _ ret := ret = .scalar { bits := 1, sizeBytes := 1 }

/--
Kernel-checked symbolic verification of trait-method dispatch through
`traitImpls` and `c.callees` for `RangeBounds::contains` across all symbolic
`start ≤ idx < end_`.
-/
theorem rangeBoundsTraitDispatch_verified :
    VerificationResult rangeBoundsCallerClaim := by
  refine verifyMirNoPanicSym rangeBoundsCallerClaim 16 ?_
  rintro _ ⟨start, end_, idx, h_lo, h_hi, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals (try simp_all; try omega)

/-! ## 9. Indirect `FnPtr` Calls (`ReifyFnPointer`, `fnPtrToPtr`, `TerminatorKind.call`, `TerminatorKind.tailCall`, `s.memory.fnPtrs`, and UB Refutation) -/

private def u8FnPtrKind : RigidTy :=
  .fnPtr [.uint .u8] (.uint .u8) .safe .rust

private def u8FnPtrMirTy : Ty := { kind := u8FnPtrKind, layoutIdx := 0 }

/-- Callee `fn inc_u8_cb(x: u8) -> u8 { x & 1 }` invoked via function pointer. -/
def incU8CallbackMir : CapturedMir := {
  mkMirBody "sym_test::inc_u8_cb" 1
    [mkDecl .mut u8MirTy, mkDecl .not u8MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .bitAnd
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 1))) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

/--
Caller `reifyAndCallFnPtrMir` that:
1. Coerces `sym_test::inc_u8_cb` into a function pointer `_2 : fn(u8) -> u8`
   via `CastKind.pointerCoercion "ReifyFnPointer"` (allocating in `s.memory.fnPtrs`),
2. Casts `_2` to a thin raw pointer `_3 : *const u8` via `CastKind.fnPtrToPtr`, and
3. Invokes `move _2(move _1)` indirectly via `TerminatorKind.call`.
-/
def reifyAndCallFnPtrMir : CapturedMir := {
  mkMirBody "sym_test::reify_and_call_fn_ptr" 1
    [ mkDecl .mut u8MirTy
    , mkDecl .not u8MirTy
    , mkDecl .mut u8FnPtrMirTy
    , mkDecl .mut rawConstPtrU8MirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 2)
          , mkStmt (.storageLive 3)
          , mkStmt (.assign { local_ := 2, projection := [] }
              (.cast (.pointerCoercion "ReifyFnPointer")
                (fnConstOp "sym_test::inc_u8_cb")
                u8FnPtrMirTy))
          , mkStmt (.assign { local_ := 3, projection := [] }
              (.cast .fnPtrToPtr
                (.copy { local_ := 2, projection := [] })
                rawConstPtrU8MirTy)) ]
        terminator :=
          mkTerm (.call
            (.move { local_ := 2, projection := [] })
            [.move { local_ := 1, projection := [] }]
            { local_ := 0, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.storageDead 3)
          , mkStmt (.storageDead 2) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def reifyAndCallFnPtrClaim : Claim where
  body := reifyAndCallFnPtrMir
  callees := [incU8CallbackMir]
  pre args := ∃ x : Nat, x < 256 ∧ args = [.scalar { bits := x, sizeBytes := 1 }]
  post args ret :=
    ∀ x : Nat,
      args = [.scalar { bits := x, sizeBytes := 1 }] →
      ret = .scalar { bits := x % 2, sizeBytes := 1 }

/--
Kernel-checked symbolic verification of `ReifyFnPointer` + `fnPtrToPtr` +
indirect `TerminatorKind.call` across all 256 `u8` inputs.
-/
theorem reifyAndCallFnPtr_verified :
    VerificationResult reifyAndCallFnPtrClaim := by
  refine verifyMirNoPanicSym reifyAndCallFnPtrClaim 16 ?_
  rintro _ ⟨x, _, rfl⟩
  intro x' h_args
  simp only [List.cons.injEq, Value.scalar.injEq, ScalarInt.mk.injEq, and_true] at h_args
  subst h_args
  -- `simp` leaves the `u8` range side condition `x % 2 < 256`.
  simp <;> omega

/--
Caller `indirectFnPtrTailCallMir` taking an incoming function pointer parameter
`_1 : fn(u8) -> u8` (registered in `s.memory.fnPtrs`) and `_2 : u8` and invoking
`move _1(move _2)` via `TerminatorKind.tailCall`.
-/
def indirectFnPtrTailCallMir : CapturedMir := {
  mkMirBody "sym_test::indirect_tail_call" 2
    [mkDecl .mut u8MirTy, mkDecl .not u8FnPtrMirTy, mkDecl .not u8MirTy]
    [ { statements := []
        terminator :=
          mkTerm (.tailCall
            (.move { local_ := 1, projection := [] })
            [.move { local_ := 2, projection := [] }])
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def indirectFnPtrTailCallClaim : StatefulClaim where
  body := indirectFnPtrTailCallMir
  callees := [incU8CallbackMir]
  pre args mem :=
    ∃ x : Nat,
      x < 256 ∧
      args =
        [ .ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8
        , .scalar { bits := x, sizeBytes := 1 } ] ∧
      mem =
        { emptyMemory with
          fnPtrs :=
            [ { allocId := fnPtrAllocBase
                defPath := "sym_test::inc_u8_cb"
                fnSig := some u8FnPtrKind } ] }
  post _ _ ret _ :=
    ∃ y : Nat, ret = .scalar { bits := y, sizeBytes := 1 }

/--
Kernel-checked symbolic verification of indirect `TerminatorKind.tailCall`
through `s.memory.fnPtrs`.
-/
theorem indirectFnPtrTailCall_verified :
    StatefulVerificationResult indirectFnPtrTailCallClaim := by
  refine verifyStatefulMirNoPanicSym indirectFnPtrTailCallClaim 12 ?_
  rintro _ _ ⟨x, hx, rfl, rfl⟩
  exact ⟨_, rfl⟩

/--
Negative test: calling a function pointer whose `allocId` is not registered in
`s.memory.fnPtrs` triggers immediate UB (`CallTargetResult.ub`), refuting the
stateful claim via `refuteStatefulClaimByBoundedUB`.
-/
def indirectCallDanglingFnPtrClaim : StatefulClaim where
  body := indirectFnPtrTailCallMir
  callees := [incU8CallbackMir]
  pre args mem :=
    args =
      [ .ptr { allocId := 99999, offsetBytes := 0 } 8
      , .scalar { bits := 7, sizeBytes := 1 } ] ∧
    mem =
      { emptyMemory with
        fnPtrs :=
          [ { allocId := fnPtrAllocBase
              defPath := "sym_test::inc_u8_cb"
              fnSig := some u8FnPtrKind } ] }
  post _ _ _ _ := True

theorem indirectCallDanglingFnPtr_refuted :
    ¬ indirectCallDanglingFnPtrClaim.holds := by
  exact refuteStatefulClaimByBoundedUB
    indirectCallDanglingFnPtrClaim 8
    [ .ptr { allocId := 99999, offsetBytes := 0 } 8
    , .scalar { bits := 7, sizeBytes := 1 } ]
    { emptyMemory with
      fnPtrs :=
        [ { allocId := fnPtrAllocBase
            defPath := "sym_test::inc_u8_cb"
            fnSig := some u8FnPtrKind } ] }
    ⟨rfl, rfl⟩
    rfl

/-! ## 10. Diverging Panic & `UnreachableUnchecked` Branches (`target = .none`) -/

/--
`guardedSliceLenSubMir`: checks `_3 = Le(_2, PtrMetadata(_1))`; on `true` (`bb1`)
calls `core::slice::<impl [T]>::len::<u8>(_1)` and returns `len - mid`; on
`false` (`bb2`) calls `"core::hint::unreachable_unchecked"` with `target = .none`.
-/
def guardedSliceLenSubMir : CapturedMir := {
  mkMirBody "sym_test::guarded_slice_len_sub" 2
    [ mkDecl .mut usizeMirTy
    , mkDecl .not sliceRefU8MirTy
    , mkDecl .not usizeMirTy
    , mkDecl .mut usizeMirTy
    , mkDecl .mut boolMirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.storageLive 4) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::len" [.uint .u8])
            [.copy { local_ := 1, projection := [] }]
            { local_ := 3, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 4, projection := [] }
              (.binaryOp .le
                (.copy { local_ := 2, projection := [] })
                (.copy { local_ := 3, projection := [] }))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 4, projection := [] })
            { branches := [(0, 3)], otherwise := 2 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .sub
                (.copy { local_ := 3, projection := [] })
                (.copy { local_ := 2, projection := [] })))
          , mkStmt (.storageDead 4)
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::hint::unreachable_unchecked")
            []
            { local_ := 0, projection := [] }
            .none
            .unreachable)
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def guardedSliceLenSubClaim : Claim where
  body := guardedSliceLenSubMir
  callees := [coreSliceLenMir]
  pre args :=
    ∃ (p : ProvenancePtr) (len mid : Nat),
      mid ≤ len ∧ len < 1000 ∧
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ]
  post args ret :=
    ∀ (p : ProvenancePtr) (len mid : Nat),
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ] →
      ret = .scalar { bits := len - mid, sizeBytes := 8 }

/--
Kernel-checked symbolic verification of `guardedSliceLenSubMir`: when `mid ≤ len`,
the `unreachable_unchecked` branch (`target = .none`) is pruned symbolically and
the inlined `core::slice::<impl [T]>::len` call reduces cleanly.
-/
theorem guardedSliceLenSub_verified :
    VerificationResult guardedSliceLenSubClaim := by
  refine verifyMirNoPanicSym guardedSliceLenSubClaim 16 ?_
  rintro _ ⟨p, len, mid, h_le, h_len, rfl⟩
  have h_ble : Nat.ble mid len = true := Nat.ble_eq_true_of_le h_le
  have h_sub : len - mid < 18446744073709551616 := by omega
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · intro p' len' mid' h_args
    simp only [List.cons.injEq, Value.aggregate.injEq, Value.ptr.injEq,
      Value.scalar.injEq, ScalarInt.mk.injEq, and_true, true_and] at h_args
    rcases h_args with ⟨⟨rfl, rfl⟩, rfl⟩
    simp; exact h_sub
  · simp_all
  · simp_all

/--
`guardedPanicCallMir`: calls `core::slice::<impl [T]>::len::<u8>(_1)` and if
`mid > len`, invokes diverging `"core::panicking::panic"` (`target = .none`,
`unwind = .continue_`), which halts with `.panic` (safe under `MirNoUB`).
-/
def guardedPanicCallMir : CapturedMir := {
  mkMirBody "sym_test::guarded_panic_call" 2
    [ mkDecl .mut usizeMirTy
    , mkDecl .not sliceRefU8MirTy
    , mkDecl .not usizeMirTy
    , mkDecl .mut usizeMirTy
    , mkDecl .mut boolMirTy ]
    [ { statements :=
          [ mkStmt (.storageLive 3)
          , mkStmt (.storageLive 4) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::len" [.uint .u8])
            [.copy { local_ := 1, projection := [] }]
            { local_ := 3, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 4, projection := [] }
              (.binaryOp .le
                (.copy { local_ := 2, projection := [] })
                (.copy { local_ := 3, projection := [] }))) ]
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 4, projection := [] })
            { branches := [(0, 3)], otherwise := 2 })
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .sub
                (.copy { local_ := 3, projection := [] })
                (.copy { local_ := 2, projection := [] })))
          , mkStmt (.storageDead 4)
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::panicking::panic")
            []
            { local_ := 0, projection := [] }
            .none
            .continue_)
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def guardedPanicCallClaim : Claim where
  body := guardedPanicCallMir
  callees := [coreSliceLenMir]
  pre args :=
    ∃ (p : ProvenancePtr) (len mid : Nat),
      len < 1000 ∧ mid < 1000 ∧
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ]
  post args ret :=
    ∀ (p : ProvenancePtr) (len mid : Nat),
      mid ≤ len →
      args =
        [ .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }]
        , .scalar { bits := mid, sizeBytes := 8 } ] →
      ret = .scalar { bits := len - mid, sizeBytes := 8 }

/--
Kernel-checked symbolic verification of `guardedPanicCallMir` across BOTH
returning (`mid ≤ len`) and diverging-panic (`mid > len`) branches, plus its
`MirContractHoldsWithSafetyAndCallees` equivalence.
-/
theorem guardedPanicCall_verified :
    VerificationResult guardedPanicCallClaim := by
  refine verifyMirSym guardedPanicCallClaim 16 ?_
  rintro _ ⟨p, len, mid, h_len, h_mid, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · intro p' len' mid' h_le h_args
    simp only [List.cons.injEq, Value.aggregate.injEq, Value.ptr.injEq,
      Value.scalar.injEq, ScalarInt.mk.injEq, and_true, true_and] at h_args
    rcases h_args with ⟨⟨rfl, rfl⟩, rfl⟩
    have h_sub : len - mid < 18446744073709551616 := by omega
    simp; exact h_sub
  · simp_all
  · trivial

/-! ## 11. Polymorphic Claims (`verifyPolyMirNoPanicSym`) & Compositional Linking (`verifyExternalSpecWithCalleesMirSym`, `linkVerifiedPolyContractMirCalleeWithCalleesSym`, `dischargeRustPinnedContractWithSpecCalleesAuto`) -/

private def paramTPlaceholderLayout : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/--
Polymorphic identity function `fn poly_id<T>(x: T) -> T { x }` with
`typeParamCount = 1`.
-/
def polyIdMir : CapturedMir := {
  mkMirBody "sym_test::poly_id" 1
    [mkDecl .mut paramTMirTy, mkDecl .not paramTMirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.use (.move { local_ := 1, projection := [] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [paramTPlaceholderLayout]
  }
}

def polyIdClaimFor (typeArgs : TypeSubst) : Claim where
  body := polyIdMir.instantiate typeArgs
  pre args := ∃ v : Value, args = [v]
  post args ret := args = [ret]

/--
Universally quantified polymorphic verification of `polyIdMir` over ALL
`typeArgs : TypeSubst` with `typeArgs.length = 1` via `verifyPolyMirNoPanicSym`.
-/
theorem polyId_all_typeArgs_verified :
    ∀ typeArgs : TypeSubst,
      typeArgs.length = 1 →
      VerificationResult (polyIdClaimFor typeArgs) := by
  refine verifyPolyMirNoPanicSym polyIdMir polyIdClaimFor 8 ?_
  rintro typeArgs _ args s rfl ⟨v, rfl⟩ h_ctx
  rfl

/--
`#[external_spec]` sidecar for `core::slice::from_raw_parts_mut` and a modular
caller `externalSpecSliceCallerMir` that:
1. Calls `core::slice::from_raw_parts_mut::<u8>(_1, _2)` via its
   `externalSpecCallContract` (which returns a symbolic post-call `memAfter`
   preserving `callFramePreserved`), and
2. Calls inlined `core::slice::<impl [T]>::len::<u8>(_3)` from `c.callees`
   immediately after the external call!
-/
def extFromRawPartsMutSidecarMir : CapturedMir := {
  mkMirBody "sym_test::spec_from_raw_parts_mut" 2
    [ mkDecl .mut sliceMutRefU8MirTy
    , mkDecl .not rawMutPtrU8MirTy
    , mkDecl .not usizeMirTy ]
    [ { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ] with
  fnAbi := { defaultTestFnAbi with canUnwind := false }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := { bytes := 16 }
          align := { bytes := 8 }
          backendRepr := .scalarPair
            (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
            (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
          fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
          variants := .single 0
          isUninhabited := false } ]
  }
}

def extFromRawPartsMutContract : MirCallContract :=
  polyExternalSpecCallContract
    "core::slice::from_raw_parts_mut"
    [.uint .u8]
    extFromRawPartsMutSidecarMir
    (fun args =>
      ∃ p len,
        len < 18446744073709551616 ∧
        args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }])
    (fun args ret =>
      ∀ p len,
        args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }] →
        ret = .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }])

def externalSpecSliceCallerMir : CapturedMir := {
  mkMirBody "sym_test::ext_spec_slice_caller" 2
    [ mkDecl .mut usizeMirTy
    , mkDecl .not rawMutPtrU8MirTy
    , mkDecl .not usizeMirTy
    , mkDecl .mut sliceMutRefU8MirTy ]
    [ { statements := [ mkStmt (.storageLive 3) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::from_raw_parts_mut" [.uint .u8])
            [ .copy { local_ := 1, projection := [] }
            , .copy { local_ := 2, projection := [] } ]
            { local_ := 3, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::slice::<impl [T]>::len" [.uint .u8])
            [.move { local_ := 3, projection := [] }]
            { local_ := 0, projection := [] }
            (.some 2)
            .continue_)
        isCleanup := false }
    , { statements := [ mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def externalSpecSliceCallerClaim : ModularClaim where
  body := externalSpecSliceCallerMir
  callees := [coreSliceLenMir]
  envAssumed := extFromRawPartsMutContract.holdsOn
  pre args mem :=
    ∃ (p : ProvenancePtr) (len : Nat),
      p.allocId > 0 ∧ len < 18446744073709551616 ∧
      args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }] ∧
      mem = emptyMemory
  post args _ ret _ :=
    ∀ (p : ProvenancePtr) (len : Nat),
      args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }] →
      ret = .scalar { bits := len, sizeBytes := 8 }

/--
Kernel-checked modular verification via `verifyPolyExternalSpecWithCalleesMirSym`:
`wpMirFrameAndTraitsModularSym` restores `callees`, `traitImpls`, and `callStack`
across the polymorphic `#[external_spec]` call to
`core::slice::from_raw_parts_mut::<u8>`, allowing the subsequent inlined
polymorphic call to `core::slice::<impl [T]>::len::<u8>` in `c.callees` to
instantiate and reduce in a single pass!
-/
theorem externalSpecSliceCaller_verified :
    ModularVerificationResult externalSpecSliceCallerClaim := by
  refine verifyPolyExternalSpecWithCalleesMirSym
    "core::slice::from_raw_parts_mut"
    [.uint .u8]
    extFromRawPartsMutSidecarMir
    (fun args =>
      ∃ p len,
        len < 18446744073709551616 ∧
        args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }])
    (fun args ret =>
      ∀ p len,
        args = [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }] →
        ret = .aggregate 0 [.ptr p 8, .scalar { bits := len, sizeBytes := 8 }])
    externalSpecSliceCallerMir
    [coreSliceLenMir]
    externalSpecSliceCallerClaim.pre
    externalSpecSliceCallerClaim.post
    16
    ?_
  rintro _ _ ⟨p, len, hp, hlen, rfl, rfl⟩
  (conv => whnf)
  refine ⟨⟨rfl, rfl, rfl, ⟨Or.inl ⟨p, 8, rfl⟩, ⟨len, hlen, rfl⟩, trivial⟩, ⟨p, len, hlen, rfl⟩⟩, ?_⟩
  rintro ans h_post
  cases ans with
  | returned retVal memAfter =>
    rcases h_post with ⟨_, _, h_ens⟩
    have h_ret := h_ens p len rfl
    subst h_ret
    (conv => whnf)
    rintro retVal' mem' h_out p' len' h_args
    injection h_out with h_pair
    injection h_pair with h_rv _
    subst h_rv
    simp only [List.cons.injEq, Value.ptr.injEq, Value.scalar.injEq,
      ScalarInt.mk.injEq, and_true] at h_args
    rcases h_args with ⟨rfl, rfl⟩
    rfl
  | panicked memAfter =>
    exact False.elim h_post
  | aborted =>
    intro _ _ h_eq
    cases h_eq

/--
Kernel-checked compositional caller–callee linking via
`linkVerifiedPolyContractMirCalleeWithCalleesSym`: links
`externalSpecSliceCaller_verified` (which has `[coreSliceLenMir]` in
`callerCallees`) with the polymorphic implementation
`coreSliceFromRawPartsMutMir`, closing the modular assumption into a closed
`MirClosedStatefulContractSpec` refinement!
-/
theorem externalSpecSliceCaller_linked_verified :
    (fun args mem =>
      (mirHandledTreeWithCallees
        externalSpecSliceCallerMir args mem [coreSliceLenMir]
        (linkPolyCalleeWithCalleesHandler
          coreSliceFromRawPartsMutMir
          externalSpecSliceCallerMir.layouts
          []
          abortExternalCalls
          externalSpecSliceCallerMir.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec
        externalSpecSliceCallerClaim.pre
        externalSpecSliceCallerClaim.pre
        externalSpecSliceCallerClaim.post := by
  refine linkVerifiedPolyContractMirCalleeWithCalleesSym
    externalSpecSliceCaller_verified
    coreSliceFromRawPartsMutMir
    []
    8
    abortExternalCalls
    ?_
    ?_
  · rintro req h_path ⟨_, h_typeArgs, _, _, ⟨p, len, h_len_lt, h_args⟩⟩
    cases req with
    | mk defPath typeArgs args memory =>
      dsimp only at h_path h_typeArgs h_args ⊢
      subst h_path h_typeArgs h_args
      refine ⟨callFrameAndTraitsPreserved_restoreCallerMemoryFrame_same_fnPtrs memory _ rfl, ?_, ?_⟩
      · exact ⟨p, 8, len, h_len_lt, rfl⟩
      · intro p' len' h_eq
        simp only [List.cons.injEq, Value.ptr.injEq, Value.scalar.injEq,
          ScalarInt.mk.injEq, and_true] at h_eq
        rcases h_eq with ⟨rfl, rfl⟩
        rfl
  · rintro req h_ne ⟨h_eq, _⟩
    exact False.elim (h_ne h_eq)

/--
`O(1)` lookup context witness for `coreSliceLenMir` basic block `0` and
polymorphic callee lookup in `[coreSliceLenMir]`.
-/
theorem coreSliceLenMir_blockCtx_0 :
    BlockCtx coreSliceLenMir 0
      { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.unaryOp .ptrMetadata (.move { local_ := 1, projection := [] }))) ]
        terminator := mkTerm .return_
        isCleanup := false } :=
  rfl

theorem sliceHelperCallees_calleeCtx_len :
    CalleeCtx [coreSliceLenMir] sliceCallerLayouts
      "core::slice::<impl [T]>::len" [.uint .u8] []
      (instantiateCalleeForReq
        coreSliceLenMir
        sliceCallerLayouts
        { defPath := "core::slice::<impl [T]>::len"
          typeArgs := [.uint .u8]
          args := []
          memory := emptyMemory }
        []) :=
  rfl

/--
Boolean companion `requires` (pinning `x == 4`) and `ensures` (calling
`sym_test::inc_u8_cb` via `specCallees`), discharged via
`dischargeRustPinnedContractWithSpecCalleesAuto`.
-/
def companionPinnedReqMir : CapturedMir := {
  mkMirBody "sym_test::__anodized_fn_requires_pinned" 1
    [mkDecl .mut boolMirTy, mkDecl .not u8MirTy]
    [ { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 1, projection := [] })
                (u8ConstOperand 4))) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.requires "sym_test::pinned_with_spec_callees") with
  layouts := sliceCallerLayouts
}

def companionWithCallEnsMir : CapturedMir := {
  mkMirBody "sym_test::__anodized_fn_ensures_with_call" 2
    [mkDecl .mut boolMirTy, mkDecl .not u8MirTy, mkDecl .not u8MirTy, mkDecl .mut u8MirTy]
    [ { statements := [ mkStmt (.storageLive 3) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::inc_u8_cb")
            [.copy { local_ := 1, projection := [] }]
            { local_ := 3, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.binaryOp .eq
                (.copy { local_ := 2, projection := [] })
                (.copy { local_ := 3, projection := [] })))
          , mkStmt (.storageDead 3) ]
        terminator := mkTerm .return_
        isCleanup := false } ]
    (.ensures "sym_test::pinned_with_spec_callees") with
  layouts := sliceCallerLayouts
}

def pinnedWithSpecCalleesSubjectMir : CapturedMir := {
  mkMirBody "sym_test::pinned_with_spec_callees" 1
    [mkDecl .mut u8MirTy, mkDecl .not u8MirTy]
    [ { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::inc_u8_cb")
            [.copy { local_ := 1, projection := [] }]
            { local_ := 0, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ] with
  layouts := sliceCallerLayouts
}

def pinnedWithSpecCalleesClaim : Claim where
  body := pinnedWithSpecCalleesSubjectMir
  callees := [incU8CallbackMir]
  pre args :=
    Trusted.Sequence.length args = 1 ∧
      MirBoolPredicateHolds companionPinnedReqMir args
  post args ret :=
    MirBoolPredicateHoldsWithCallees companionWithCallEnsMir [incU8CallbackMir] (args ++ [ret])

/--
Kernel-checked verification of `pinnedWithSpecCalleesClaim` where both the
subject body and its `ensures` companion predicate invoke a linked callee in
`callees` / `specCallees`.
-/
theorem pinnedWithSpecCallees_verified :
    VerificationResult pinnedWithSpecCalleesClaim := by
  exact dischargeRustPinnedContractWithSpecCalleesAuto
    pinnedWithSpecCalleesClaim 16 16
    [incU8CallbackMir]
    (.some companionPinnedReqMir)
    (.some companionWithCallEnsMir)

def pinnedWithSpecCalleesTotalClaim : TotalClaim where
  body := pinnedWithSpecCalleesSubjectMir
  callees := [incU8CallbackMir]
  pre args mem :=
    (Trusted.Sequence.length args = 1 ∧
      MirBoolPredicateHolds companionPinnedReqMir args) ∧
      mem = (initMachineState pinnedWithSpecCalleesSubjectMir args).memory
  post args _ ret _ :=
    MirBoolPredicateHoldsWithCallees companionWithCallEnsMir [incU8CallbackMir] (args ++ [ret])

/--
Kernel-checked total verification of `pinnedWithSpecCalleesTotalClaim` via
`dischargeRustTotalPinnedContractWithSpecCalleesAuto`.
-/
theorem pinnedWithSpecCalleesTotal_verified :
    TotalVerificationResult pinnedWithSpecCalleesTotalClaim := by
  exact dischargeRustTotalPinnedContractWithSpecCalleesAuto
    pinnedWithSpecCalleesTotalClaim 16 16
    [incU8CallbackMir]
    (.some companionPinnedReqMir)
    (.some companionWithCallEnsMir)

end Anneal.Rustc.V2026_06_01.SymbolicEvalTests
