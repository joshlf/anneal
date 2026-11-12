import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.Rustc.V2026_06_01.SymReflect

namespace Anneal.Rustc.V2026_06_01.SymbolicEvalTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
Kernel-checked test suite for `Anneal.Rustc.V2026_06_01.SymbolicEval`:
1. Straight-line symbolic arithmetic verification (`Claim`, `TotalClaim`, and
   `MirContractHoldsWithSafety` across panicking and non-panicking inputs).
2. Branching (`SwitchInt`) symbolic verification paired with multi-block
   short-circuit `#[spec]` boolean companion predicates (`MirBoolPredicateHolds`),
   plus one-call pinned `#[spec]` combinators (`dischargeRustEqU32FuelFree`,
   `dischargeRustEq2U8FuelFree`).
3. Stateful Tree Borrows pointer read/write verification (`StatefulClaim`,
   `verifyStatefulMirFuelFree`, `dischargeStatefulEqFuelFree`).
4. Negative UB refutation tests (`refuteClaimByBoundedUB`,
   `refuteTotalClaimByBoundedUB`, `refuteStatefulClaimByBoundedUB`).
5. Non-vacuity witness helpers (`proveNonVacuousPre`,
   `proveNonVacuousStatefulPre`, `proveNonVacuousBoolSpecPre`).

`*VerificationResult` claims are discharged by fuel-free combinators (the
`SymReflect` `*FuelFree` wrappers and the suite-local `SymConv` stepper below);
explicit step bounds remain only where the API under test takes one (bounded
refutation, point-bounded differential verdicts, `wpMirBoolSym` equivalence,
and the polymorphic, modular, and linking combinators).
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

/-- Single-pass fuel-free symbolic verification of `add_bounded` over all `10,000` `(a, b)`. -/
theorem addBoundedClaim_verified : VerificationResult addBoundedClaim := by
  refine verifyByWPFuelFree addBoundedClaim ?_
  rintro _ ⟨a, b, ha, hb, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · simp_all; omega
  · rintro _ _ ⟨⟩
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

/-- Single-pass fuel-free total-correctness (`DWP`) symbolic verification of `add_bounded`. -/
theorem addBoundedTotalClaim_verified :
    TotalVerificationResult addBoundedTotalClaim := by
  refine verifyTotalMirFuelFree addBoundedTotalClaim ?_
  rintro _ _ ⟨a, b, ha, hb, rfl, rfl⟩
  rw [← wpMirSym_eq_wpMirBounded]
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · simp_all; omega
  · exact ⟨_, _, rfl, ⟨a + b, by omega, by simp; omega⟩, rfl⟩

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
  refine verifyByWPSafeFuelFree advanceOffsetSymClaim ?_
  rintro _ ⟨b, hb, rfl⟩
  dsimp [scalarModulus, scalarPow2] at hb
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · trivial
  · rintro ⟨_, hb', ⟨⟩⟩ _ ⟨⟩
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
  rw [mirBoolPredicateHolds_iff_wpMirBoolSym 12 clampReqMir _ (by
    ((repeat' ((conv => whnf); split)); all_goals (conv => whnf)) <;> trivial)]
  (repeat' ((conv => lhs; whnf); split)) <;>
    (conv => lhs; whnf) <;>
    simp_all <;> omega

/--
Single-pass symbolic verification of branching `clampOrStepMir` with `#[spec]`
boolean companion `requires` (`clampReqMir`) and `ensures` (`clampEnsMir`).
-/
theorem clampOrStepClaim_verified : VerificationResult clampOrStepClaim := by
  refine verifyByWPFuelFree clampOrStepClaim ?_
  rintro _ ⟨⟨x, hx, rfl⟩, h_req⟩
  dsimp [scalarModulus, scalarPow2] at hx
  have hx20 : x < 20 := ((clampReqMir_iff_arith x).1 h_req).1
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · refine ⟨mirBoolPredicateHolds_of_wp_fuelFree clampEnsMir _, ?_⟩
    rintro _ ⟨⟩; simp_all; omega
  · simp_all; omega
  · refine ⟨mirBoolPredicateHolds_of_fuelFree clampEnsMir _ (by
      rw [← wpMirSym_eq_wpMirBounded]
      (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
      all_goals first | (rintro _ _ ⟨⟩; rfl) | (simp_all; omega)), ?_⟩
    rintro _ ⟨⟩; simp_all

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
  dischargeRustEqU32FuelFree pinMagicClaim pinMagicReqMir pinMagicEnsMir 7

/-- Pinned `(u8, u8)` short-circuit `&&` `#[spec]` test (`dischargeRustEq2U8FuelFree`). -/
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
  dischargeRustEq2U8FuelFree totalFrameLenClaim totalFrameLenReqMir totalFrameLenEnsMir 1 2

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

/-- Fuel-free symbolic stateful verification for ALL `256` values of `ver: u8`. -/
theorem writeAndReadMutSymClaim_verified :
    StatefulVerificationResult writeAndReadMutSymClaim := by
  refine verifyStatefulMirFuelFree writeAndReadMutSymClaim ?_
  rintro _ _ ⟨v, hv, rfl, rfl⟩ _ _ ⟨⟩
  exact ⟨by rintro _ ⟨⟩; rfl, rfl⟩

def writeAndReadMutPinnedClaim : StatefulClaim where
  body := writeAndReadMutMir
  pre args mem :=
    args = [.ptr { allocId := 1, offsetBytes := 0 } 8,
            .scalar { bits := 42, sizeBytes := 1 }] ∧
    mem = activeMutMem
  post _ _ ret mem' :=
    ret = .scalar { bits := 42, sizeBytes := 1 } ∧ mem' = activeMutMem

/-- Concrete pinned stateful verification via `dischargeStatefulEqFuelFree` + `⟨rfl, rfl⟩`. -/
theorem writeAndReadMutPinnedClaim_verified :
    StatefulVerificationResult writeAndReadMutPinnedClaim :=
  dischargeStatefulEqFuelFree
    writeAndReadMutPinnedClaim
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

theorem clampAddOne1000_verified : VerificationResult clampAddOne1000Claim :=
  dischargeRustSymRange1Auto
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
private def sliceRefU8MirTy : Ty :=
  { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
private def sliceMutRefU8MirTy : Ty :=
  { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 0 }
private def rawConstPtrU8MirTy : Ty :=
  { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private def rawMutPtrU8MirTy : Ty :=
  { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
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

/-!
### Fuel-Free Symbolic Convergence (`SymConv`)

`Anneal.MirFuelFree` and `Anneal.MirLiftCore` sit above `SymbolicEval` in the
module DAG, and `trusted/audit/check_trusted.py` pins this suite's imports to
`SymbolicEval` + `SymReflect`, so the suite carries the minimal fuel-free layer
its multi-callee proofs need (their 18+ steps exceed the 16-step budget of the
`SymReflect` `*FuelFree` wrappers): `SymConv body post st` hides the step
budget of `wpMirExecSym` existentially, and `SymConv.step` discharges one
call-free symbolic step whose `SymTree` is evaluated by `whnf`. The proofs
`reduce` each intermediate state to a closed literal before stepping (so no
`advanceStmt`/`pushCalleeFrame` chain accumulates) and rewrite only symbolic
branch conditions; none of them states a step count.
-/

/-- Fuel-free convergence of `body` from `st` to `post` (`∃ fuel, wpMirExecSym ..`). -/
private inductive SymConv (body : CapturedMir) (post : MirOutcome → Prop) :
    MirExecState → Prop
  | intro {st : MirExecState} (fuel : Nat) :
      wpMirExecSym fuel body st post → SymConv body post st

/--
One call-free symbolic step: every leaf of the step's `SymTree` either returns
into `post` or continues as `SymConv`.
-/
private theorem SymConv.step {body : CapturedMir} {post : MirOutcome → Prop}
    {st : MirExecState}
    (h : evalSymNodeTreeNoCall (SymConv body post) post (stepMirExecSymTree body st)) :
    SymConv body post st := by
  have h_unfold : ∀ fuel, wpMirExecSym (fuel + 1) body st post =
      evalNodeWP (fun st' => wpMirExecSym fuel body st' post) post
        (stepMirState body st) := fun fuel => by
    rw [wpMirExecSym, evalSymNodeTree_eq, stepMirExecSymTree_eval]
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h
  cases h_st : stepMirState body st with
  | ret out => rw [h_st] at h; exact ⟨1, by rw [h_unfold, h_st]; exact h⟩
  | tau st' =>
    rw [h_st] at h
    obtain ⟨fuel, h_wp⟩ := h
    exact ⟨fuel + 1, by rw [h_unfold, h_st]; exact h_wp⟩
  | vis i k =>
    rw [h_st] at h
    rcases i with f | (e | c)
    · exact h.elim
    · obtain ⟨fuel, h_wp⟩ := h
      exact ⟨fuel + 1, by rw [h_unfold, h_st]; exact h_wp⟩
    · exact h.elim

/-- Discharge `VerificationResult c` from per-input fuel-free convergence. -/
private theorem verifyMirNoPanic_of_symConv (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      SymConv c.body (mirNormalPost fun retVal _ => c.post args retVal)
        (.running (initMachineStateWithCallees c.body args c.callees))) :
    VerificationResult c :=
  verifyByDWLP c fun args h_pre => by
    obtain ⟨_, h_wp⟩ := h args h_pre
    exact dwlp_of_wpMirSym (s := initMachineStateWithCallees c.body args c.callees)
      (wpMirSym_mono (fun out h_out =>
        (mirSafePost_iff_forall_normal _ out).1 (mirNormalPost_imp_mirSafePost h_out)) h_wp)

/--
Kernel-checked symbolic verification of `sliceLenAsPtrFromRawPartsMir` stepping
through polymorphic `core::slice::<impl [T]>::len::<u8>`,
`core::slice::<impl [T]>::as_ptr::<u8>`, and
`core::slice::from_raw_parts_mut::<u8>` by fuel-free `SymConv` stepping.
-/
theorem sliceLenAsPtrFromRawParts_verified :
    VerificationResult sliceLenAsPtrFromRawPartsClaim := by
  refine verifyMirNoPanic_of_symConv _ ?_
  rintro _ ⟨p, len, rfl⟩
  repeat ((conv => arg 3; reduce); apply SymConv.step; conv => whnf)

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
      p.allocId ≠ 0 ∧ mid ≤ len ∧ p.offsetBytes + len < 9223372036854775808 ∧
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

/--
Kernel-checked symbolic verification of `sliceSplitAtMutCallerMir` stepping
through `split_at_mut`, `len`, and `from_raw_parts_mut` across nested
stack frames (`callStack` depth 2) by fuel-free `SymConv` stepping.
-/
theorem sliceHelperPipeline_verified :
    VerificationResult sliceHelperPipelineClaim := by
  refine verifyMirNoPanic_of_symConv _ ?_
  rintro _ ⟨⟨_ | allocId, offsetBytes⟩, len, mid, h_alloc, h_le, h_len, rfl⟩
  · exact (h_alloc rfl).elim
  dsimp only at h_len
  have h_mod : scalarModulus 8 = 18446744073709551616 := rfl
  have h_half : signedHalfModulus 8 = 9223372036854775808 := rfl
  have h_wrap : wrapScalarBits mid 18446744073709551616 = mid :=
    wrapScalarBits_eq_of_lt (by omega)
  have h_d : Nat.ble 9223372036854775808 mid = false := (nat_ble_eq_false_iff _ _).2 (by omega)
  have h_neg : isSignedNegative mid 8 = false := by
    show Nat.ble (Nat.div (scalarModulus 8) 2) (wrapScalarBits mid (scalarModulus 8)) = false
    rw [h_mod, h_wrap]; exact h_d
  have h_mul : Nat.mul mid 1 = mid := Nat.mul_one mid
  have h_c : Nat.ble 9223372036854775808 (Nat.add offsetBytes mid) = false :=
    (nat_ble_eq_false_iff _ _).2 (by change offsetBytes + mid < _; omega)
  have h_o : Nat.ble 9223372036854775808 offsetBytes = false :=
    (nat_ble_eq_false_iff _ _).2 (by omega)
  have h_sub : Nat.ble mid len = true := Nat.ble_eq_true_of_le h_le
  repeat' (first
    | ((conv => arg 3; reduce); apply SymConv.step; conv => whnf)
    | (simp only [layoutPointerBytes, Option.getD, h_mod, h_half, h_wrap, h_neg, h_mul, h_d, h_c,
         h_o, h_sub, Bool.not_false];
       conv => whnf))
  rintro _ _ _ ⟨⟩
  have h_ble_sub : Nat.ble 18446744073709551616 (len - mid) = false :=
    (nat_ble_eq_false_iff _ _).2 (by omega)
  simp [h_ble_sub]

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
  refine verifyByWPFuelFree rangeBoundsCallerClaim ?_
  rintro _ ⟨start, end_, idx, h_lo, h_hi, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals simp_all <;> omega

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
  refine verifyByWPFuelFree reifyAndCallFnPtrClaim ?_
  rintro _ ⟨x, _, rfl⟩ _ ⟨⟩
  simp <;> omega -- `simp` leaves the `u8` range side condition `x % 2 < 256`.

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
  refine verifyStatefulMirFuelFree indirectFnPtrTailCallClaim ?_
  rintro _ _ ⟨x, hx, rfl, rfl⟩ _ _ ⟨⟩
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
    ¬ indirectCallDanglingFnPtrClaim.holds :=
  refuteStatefulClaimByBoundedUB
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
  refine verifyByWPFuelFree guardedSliceLenSubClaim ?_
  rintro _ ⟨p, len, mid, h_le, h_len, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rintro _ _ _ ⟨⟩
    simp; omega
  · simp_all
  · simp_all; omega

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
  refine verifyByWPSafeFuelFree guardedPanicCallClaim ?_
  rintro _ ⟨p, len, mid, h_len, h_mid, rfl⟩
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  · rintro _ _ _ h_le ⟨⟩
    simp; omega
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
  pre args :=
    ∃ v : Value, args = [v] ∧
      (match typeArgs with
      | [(.bool, _)] => v = .scalar { bits := 0, sizeBytes := 1 } ∨ v = .scalar { bits := 1, sizeBytes := 1 }
      | _ => True)
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
  intro typeArgs
  cases typeArgs with
  | nil => intro h_len; contradiction
  | cons head tail =>
    cases tail with
    | cons head2 tail2 => intro h_len; dsimp [TypeSubst.length] at h_len; have : polyIdMir.typeParamCount = 1 := rfl; omega
    | nil =>
      rcases head with ⟨t, l⟩
      intro h_len args s rfl ⟨v, h_args, hv⟩ h_ctx
      subst h_args
      cases t
      case bool =>
        rcases hv with rfl | rfl <;> rfl
      all_goals rfl

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
    _
    _
    externalSpecSliceCallerMir
    [coreSliceLenMir]
    externalSpecSliceCallerClaim.pre
    externalSpecSliceCallerClaim.post
    16
    ?_
  rintro _ _ ⟨p, len, hp, hlen, rfl, rfl⟩
  (conv => whnf)
  refine ⟨⟨rfl, rfl, rfl, ⟨Or.inl ⟨p, 8, rfl⟩, ⟨len, hlen, rfl⟩, trivial⟩, ⟨p, len, hlen, rfl⟩⟩, ?_⟩
  rintro (⟨retVal, memAfter⟩ | _ | _) h_post
  · rcases h_post with ⟨_, _, h_ens⟩
    obtain rfl := h_ens p len rfl
    (conv => whnf)
    rintro _ _ ⟨⟩ _ _ ⟨⟩
    rfl
  · exact h_post.elim
  · rintro _ _ ⟨⟩

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
  · rintro ⟨defPath, typeArgs, args, memory⟩ rfl ⟨_, rfl, _, _, ⟨p, len, h_len_lt, rfl⟩⟩
    refine ⟨callFrameAndTraitsPreserved_restoreCallerMemoryFrame_same_fnPtrs memory _ rfl,
      ⟨p, 8, len, h_len_lt, rfl⟩, ?_⟩
    rintro _ _ ⟨⟩
    rfl
  · exact fun _ h_ne ⟨h_eq, _⟩ => (h_ne h_eq).elim

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
    VerificationResult pinnedWithSpecCalleesClaim :=
  dischargeRustPinnedContractWithSpecCalleesAuto
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
    TotalVerificationResult pinnedWithSpecCalleesTotalClaim :=
  dischargeRustTotalPinnedContractWithSpecCalleesAuto
    pinnedWithSpecCalleesTotalClaim 16 16
    [incU8CallbackMir]
    (.some companionPinnedReqMir)
    (.some companionWithCallEnsMir)

/-!
## 7. Scalar-Represented Fieldless Enum Return Classification (`DIFF-E`)
-/

/--
Exact captured `LayoutTable` from `finding_0009`
(`miri_diff_corpus::ub_transmute_invalid_enum_tag__b7_c29`), where entry `0` is
`#[repr(u8)] enum ColorTag { Red = 0, Green = 1, Blue = 2 }` with
`BackendRepr.scalar` and `validRange` `0..=2`.
-/
def ubTransmuteInvalidEnumTagB7C29Layouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := { bytes := 1 }
          align := { bytes := 1 }
          backendRepr :=
            .scalar (.initialized (.int 8 false) { start := 0, end_ := 2 })
          fields := .arbitrary [{ bytes := 0 }] [0]
          variants :=
            .multiple
              (.initialized (.int 8 false) { start := 0, end_ := 2 })
              0
              [ .arbitrary [] []
              , .arbitrary [] []
              , .arbitrary [] [] ]
          isUninhabited := false }
      , { size := { bytes := 1 }
          align := { bytes := 1 }
          backendRepr :=
            .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
      , { size := { bytes := 4 }
          align := { bytes := 4 }
          backendRepr := .memory
          fields := .union 2
          variants := .single 0
          isUninhabited := false }
      , { size := { bytes := 0 }
          align := { bytes := 1 }
          backendRepr := .memory
          fields := .arbitrary [] []
          variants := .single 0
          isUninhabited := false }
      , { size := { bytes := 4 }
          align := { bytes := 4 }
          backendRepr :=
            .scalar
              (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
      , { size := { bytes := 1 }
          align := { bytes := 1 }
          backendRepr :=
            .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
          fields := .primitive
          variants := .single 0
          isUninhabited := false } ] }

/--
Exact captured `CapturedMir` body from `finding_0009`
(`miri_diff_corpus::ub_transmute_invalid_enum_tag__b7_c29`), transmuting `1_u8`
into `ColorTag::Green` and returning it in `_0`.
-/
def ubTransmuteInvalidEnumTagB7C29Body : CapturedMir :=
  let colorTy : Ty :=
    { kind := .adt "miri_diff_corpus::ColorTag" [], layoutIdx := 0 }
  let boolTy : Ty := { kind := .bool, layoutIdx := 1 }
  let uninitU32Ty : Ty :=
    { kind := .adt "miri_diff_corpus::Uninit" [.uint .u32], layoutIdx := 2 }
  let unitTy : Ty := { kind := .tuple [], layoutIdx := 3 }
  let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 4 }
  let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 5 }
  let colorRetLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 0, end_ := 2 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 0, end_ := 2 })
          0
          [ .arbitrary [] []
          , .arbitrary [] []
          , .arbitrary [] [] ]
      isUninhabited := false }
  { defPath := "miri_diff_corpus::ub_transmute_invalid_enum_tag__b7_c29"
    phase := .runtimeOptimized
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := colorTy, debugName := .none }
      , { mutability := .not, ty := colorTy, debugName := .some "c" }
      , { mutability := .not
          ty := colorTy
          debugName := .some "__tail___miri_valid_5053" }
      , { mutability := .not, ty := boolTy, debugName := .some "__valid_b" }
      , { mutability := .mut
          ty := uninitU32Ty
          debugName := .some "__valid_slot" }
      , { mutability := .mut, ty := unitTy, debugName := .none }
      , { mutability := .not
          ty := u32Ty
          debugName := .some "__miri_valid_5053" }
      , { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := boolTy, debugName := .none }
      , { mutability := .mut, ty := u32Ty, debugName := .some "__miri_sink" }
      , { mutability := .not
          ty := colorTy
          debugName := .some "__tail___miri_valid_19483" }
      , { mutability := .not, ty := boolTy, debugName := .some "__valid_b" }
      , { mutability := .mut
          ty := uninitU32Ty
          debugName := .some "__valid_slot" }
      , { mutability := .mut, ty := unitTy, debugName := .none }
      , { mutability := .not
          ty := u32Ty
          debugName := .some "__miri_valid_19483" }
      , { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := boolTy, debugName := .none }
      , { mutability := .mut, ty := u32Ty, debugName := .some "__miri_sink" } ]
    basicBlocks :=
      [ { statements :=
            [ { kind := .storageLive 1, span := "src/lib.rs:5006:9: 5006:10" }
            , { kind :=
                  .assign { local_ := 1, projection := [] }
                    (.cast .transmute
                      (.constant
                        { ty := u8Ty
                          val := .scalar (.int { bits := 1, sizeBytes := 1 }) })
                      colorTy)
                span := "src/lib.rs:5006:32: 5006:46" }
            , { kind := .storageLive 2, span := "src/lib.rs:5007:9: 5007:33" }
            , { kind :=
                  .assign { local_ := 2, projection := [] }
                    (.use (.move { local_ := 1, projection := [] }))
                span := "src/lib.rs:5007:46: 5007:47" }
            , { kind := .storageLive 3, span := "src/lib.rs:5008:9: 5008:18" }
            , { kind :=
                  .assign { local_ := 3, projection := [] }
                    (.cast .transmute
                      (.constant
                        { ty := u8Ty
                          val := .scalar (.int { bits := 1, sizeBytes := 1 }) })
                      boolTy)
                span := "src/lib.rs:5008:36: 5008:50" }
            , { kind := .storageLive 4, span := "src/lib.rs:5009:9: 5009:25" }
            , { kind := .storageLive 5, span := "src/lib.rs:5009:58: 5009:60" }
            , { kind :=
                  .assign { local_ := 5, projection := [] }
                    (.aggregate .tuple [])
                span := "src/lib.rs:5009:58: 5009:60" }
            , { kind :=
                  .assign { local_ := 4, projection := [] }
                    (.aggregate
                      (.adt "miri_diff_corpus::Uninit" 0 (.some 0))
                      [.move { local_ := 5, projection := [] }])
                span := "src/lib.rs:5009:41: 5009:62" }
            , { kind := .storageDead 5, span := "src/lib.rs:5009:61: 5009:62" }
            , { kind := .storageLive 6, span := "src/lib.rs:5010:9: 5010:26" }
            , { kind :=
                  .assign
                    { local_ := 4, projection := [.field 1 u32Ty] }
                    (.use
                      (.constant
                        { ty := u32Ty
                          val := .scalar (.int { bits := 42, sizeBytes := 4 }) }))
                span := "src/lib.rs:5011:9: 5011:35" }
            , { kind := .storageLive 7, span := "src/lib.rs:5012:9: 5012:27" }
            , { kind :=
                  .assign { local_ := 7, projection := [] }
                    (.use
                      (.copy { local_ := 4, projection := [.field 1 u32Ty] }))
                span := "src/lib.rs:5012:9: 5012:27" }
            , { kind := .storageLive 8, span := "src/lib.rs:5012:30: 5012:48" }
            , { kind := .storageLive 9, span := "src/lib.rs:5012:31: 5012:40" }
            , { kind :=
                  .assign { local_ := 9, projection := [] }
                    (.use (.copy { local_ := 3, projection := [] }))
                span := "src/lib.rs:5012:31: 5012:40" }
            , { kind :=
                  .assign { local_ := 8, projection := [] }
                    (.cast .intToInt
                      (.move { local_ := 9, projection := [] })
                      u32Ty)
                span := "src/lib.rs:5012:30: 5012:48" }
            , { kind := .storageDead 9, span := "src/lib.rs:5012:47: 5012:48" }
            , { kind :=
                  .assign { local_ := 6, projection := [] }
                    (.binaryOp .bitXor
                      (.move { local_ := 7, projection := [] })
                      (.move { local_ := 8, projection := [] }))
                span := "src/lib.rs:5012:9: 5012:48" }
            , { kind := .storageDead 8, span := "src/lib.rs:5012:47: 5012:48" }
            , { kind := .storageDead 7, span := "src/lib.rs:5012:47: 5012:48" }
            , { kind := .storageLive 10, span := "src/lib.rs:5014:9: 5014:24" }
            , { kind :=
                  .assign { local_ := 10, projection := [] }
                    (.use (.copy { local_ := 6, projection := [] }))
                span := "src/lib.rs:5014:32: 5014:49" }
            , { kind := .storageLive 11, span := "src/lib.rs:5015:9: 5015:34" }
            , { kind :=
                  .assign { local_ := 11, projection := [] }
                    (.use (.move { local_ := 2, projection := [] }))
                span := "src/lib.rs:5015:47: 5015:71" }
            , { kind := .storageLive 12, span := "src/lib.rs:5016:9: 5016:18" }
            , { kind :=
                  .assign { local_ := 12, projection := [] }
                    (.cast .transmute
                      (.constant
                        { ty := u8Ty
                          val := .scalar (.int { bits := 1, sizeBytes := 1 }) })
                      boolTy)
                span := "src/lib.rs:5016:36: 5016:50" }
            , { kind := .storageLive 13, span := "src/lib.rs:5017:9: 5017:25" }
            , { kind := .storageLive 14, span := "src/lib.rs:5017:58: 5017:60" }
            , { kind :=
                  .assign { local_ := 14, projection := [] }
                    (.aggregate .tuple [])
                span := "src/lib.rs:5017:58: 5017:60" }
            , { kind :=
                  .assign { local_ := 13, projection := [] }
                    (.aggregate
                      (.adt "miri_diff_corpus::Uninit" 0 (.some 0))
                      [.move { local_ := 14, projection := [] }])
                span := "src/lib.rs:5017:41: 5017:62" }
            , { kind := .storageDead 14, span := "src/lib.rs:5017:61: 5017:62" }
            , { kind := .storageLive 15, span := "src/lib.rs:5018:9: 5018:27" }
            , { kind :=
                  .assign
                    { local_ := 13, projection := [.field 1 u32Ty] }
                    (.use
                      (.constant
                        { ty := u32Ty
                          val := .scalar (.int { bits := 955, sizeBytes := 4 }) }))
                span := "src/lib.rs:5019:9: 5019:36" }
            , { kind := .storageLive 16, span := "src/lib.rs:5020:9: 5020:27" }
            , { kind :=
                  .assign { local_ := 16, projection := [] }
                    (.use
                      (.copy { local_ := 13, projection := [.field 1 u32Ty] }))
                span := "src/lib.rs:5020:9: 5020:27" }
            , { kind := .storageLive 17, span := "src/lib.rs:5020:30: 5020:48" }
            , { kind := .storageLive 18, span := "src/lib.rs:5020:31: 5020:40" }
            , { kind :=
                  .assign { local_ := 18, projection := [] }
                    (.use (.copy { local_ := 12, projection := [] }))
                span := "src/lib.rs:5020:31: 5020:40" }
            , { kind :=
                  .assign { local_ := 17, projection := [] }
                    (.cast .intToInt
                      (.move { local_ := 18, projection := [] })
                      u32Ty)
                span := "src/lib.rs:5020:30: 5020:48" }
            , { kind := .storageDead 18, span := "src/lib.rs:5020:47: 5020:48" }
            , { kind :=
                  .assign { local_ := 15, projection := [] }
                    (.binaryOp .bitXor
                      (.move { local_ := 16, projection := [] })
                      (.move { local_ := 17, projection := [] }))
                span := "src/lib.rs:5020:9: 5020:48" }
            , { kind := .storageDead 17, span := "src/lib.rs:5020:47: 5020:48" }
            , { kind := .storageDead 16, span := "src/lib.rs:5020:47: 5020:48" }
            , { kind := .storageLive 19, span := "src/lib.rs:5022:9: 5022:24" }
            , { kind :=
                  .assign { local_ := 19, projection := [] }
                    (.use (.copy { local_ := 15, projection := [] }))
                span := "src/lib.rs:5022:32: 5022:50" }
            , { kind :=
                  .assign { local_ := 0, projection := [] }
                    (.use (.move { local_ := 11, projection := [] }))
                span := "src/lib.rs:5023:5: 5023:30" }
            , { kind := .storageDead 19, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 15, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 13, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 12, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 11, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 10, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 6, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 4, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 3, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 2, span := "src/lib.rs:5024:1: 5024:2" }
            , { kind := .storageDead 1, span := "src/lib.rs:5024:1: 5024:2" } ]
          terminator := { kind := .return_, span := "src/lib.rs:5024:2: 5024:2" }
          isCleanup := false } ]
    fnAbi :=
      { args := []
        ret := { layout := colorRetLayout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := ubTransmuteInvalidEnumTagB7C29Layouts
    allocations := [] }

/--
Kernel-checked `by rfl` confirmation that `evalMirDiffTagBounded` classifies
`ub_transmute_invalid_enum_tag__b7_c29` (`ColorTag::Green`) as
`MirDiffTag.normalScalar 1 1`, matching `MIRI_PASS:scalar:1:1`.
-/
theorem confirm_tag_ub_transmute_invalid_enum_tag__b7_c29 :
    evalMirDiffTagBounded 64 ubTransmuteInvalidEnumTagB7C29Body
      (initMachineStateWithMemory
        ubTransmuteInvalidEnumTagB7C29Body [] emptyMemory) =
      MirDiffTag.normalScalar 1 1 :=
  rfl

/--
Kernel-checked `by rfl` confirmation that `probeMirDiffExecBounded` reports
`(MirDiffTag.normalScalar 1 1, "none")` on
`ub_transmute_invalid_enum_tag__b7_c29`.
-/
theorem confirm_probe_ub_transmute_invalid_enum_tag__b7_c29 :
    probeMirDiffExecBounded 64 ubTransmuteInvalidEnumTagB7C29Body
      (.running
        (initMachineStateWithMemory
          ubTransmuteInvalidEnumTagB7C29Body [] emptyMemory)) =
      (MirDiffTag.normalScalar 1 1, "none") :=
  rfl

/--
Variant of `ColorTag` transmute that feeds out-of-range byte `3_u8` (`validRange`
is `0..=2`), verifying that invalid discriminant transmutation still faults with
`MirDiffTag.ub` at the transmute statement span.
-/
def ubTransmuteInvalidEnumTagOutOfRangeBody : CapturedMir :=
  let colorTy : Ty :=
    { kind := .adt "miri_diff_corpus::ColorTag" [], layoutIdx := 0 }
  let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 5 }
  { ubTransmuteInvalidEnumTagB7C29Body with
    defPath := "miri_diff_corpus::ub_transmute_invalid_enum_tag_out_of_range"
    localDecls :=
      [ { mutability := .mut, ty := colorTy, debugName := .none } ]
    basicBlocks :=
      [ { statements :=
            [ { kind :=
                  .assign { local_ := 0, projection := [] }
                    (.cast .transmute
                      (.constant
                        { ty := u8Ty
                          val := .scalar (.int { bits := 3, sizeBytes := 1 }) })
                      colorTy)
                span := "src/lib.rs:5006:32: 5006:46" } ]
          terminator := { kind := .return_, span := "src/lib.rs:5007:2: 5007:2" }
          isCleanup := false } ] }

theorem confirm_ub_transmute_invalid_enum_tag_out_of_range :
    evalMirDiffTagBounded 64 ubTransmuteInvalidEnumTagOutOfRangeBody
      (initMachineStateWithMemory
        ubTransmuteInvalidEnumTagOutOfRangeBody [] emptyMemory) =
      MirDiffTag.ub ∧
    probeMirDiffExecBounded 64 ubTransmuteInvalidEnumTagOutOfRangeBody
      (.running
        (initMachineStateWithMemory
          ubTransmuteInvalidEnumTagOutOfRangeBody [] emptyMemory)) =
      (MirDiffTag.ub, "src/lib.rs:5006:32: 5006:46") :=
  ⟨rfl, rfl⟩

/--
Adversarial edge-case bodies for scalar-represented enum return classification:

1. Direct `Rvalue.aggregate` construction of `ColorTag::Blue` (`variantIdx = 2`)
   combined with an in-body `Rvalue.discriminant` check and a zero-sized
   `fnAbi.ret.layout` placeholder (exercising fallback to `_0` in `layouts`).
2. `#[repr(u16)]` fieldless enum (`sizeBytes = 2`).
3. `core::cmp::Ordering::Less` (`variantIdx = 0`, 1-byte two's complement `255`).
4. Single-variant `#[repr(u8)]` enum with non-zero explicit discriminant (`5`).
5. Niche-encoded payload enum `Option<bool>::None` (`variantIdx = 0` in MIR,
   where variant `1` carries a field so `None` must NOT be misclassified as raw
   scalar `0` instead of its Rust niche byte `2`).
-/
def directColorTagWithDiscrAndZeroFnAbiBody : CapturedMir :=
  let colorTy : Ty :=
    { kind := .adt "miri_diff_corpus::ColorTag" [], layoutIdx := 0 }
  let u64Layout : TypeLayout :=
    { size := { bytes := 8 }
      align := { bytes := 8 }
      backendRepr :=
        .scalar
          (.initialized
            (.int 64 false)
            { start := 0, end_ := 18446744073709551615 })
      fields := .primitive
      variants := .single 0
      isUninhabited := false }
  let u64Ty : Ty := { kind := .uint .u64, layoutIdx := 6 }
  let zeroPlaceholderLayout : TypeLayout :=
    { size := { bytes := 0 }
      align := { bytes := 1 }
      backendRepr := .memory
      fields := .arbitrary [] []
      variants := .empty
      isUninhabited := false }
  { defPath := "sym_test::direct_color_blue_with_discr"
    phase := .runtimeOptimized
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := colorTy, debugName := .none }
      , { mutability := .mut, ty := u64Ty, debugName := .none } ]
    basicBlocks :=
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate
                    (.adt "miri_diff_corpus::ColorTag" 2 .none)
                    []))
            , mkStmt (.storageLive 1)
            , mkStmt
                (.assign { local_ := 1, projection := [] }
                  (.discriminant { local_ := 0, projection := [] })) ]
          terminator :=
            mkTerm
              (.switchInt
                (.move { local_ := 1, projection := [] })
                { branches := [(2, 1)], otherwise := 2 })
          isCleanup := false }
      , { statements := [mkStmt (.storageDead 1)]
          terminator := mkTerm .return_
          isCleanup := false }
      , { statements := []
          terminator := mkTerm .unreachable
          isCleanup := false } ]
    fnAbi :=
      { args := []
        ret := { layout := zeroPlaceholderLayout, mode := .ignore }
        conv := .rust
        canUnwind := true }
    layouts :=
      { ubTransmuteInvalidEnumTagB7C29Layouts with
        entries :=
          ubTransmuteInvalidEnumTagB7C29Layouts.entries ++ [u64Layout] }
    allocations := [] }

def reprU16FieldlessEnumBody : CapturedMir :=
  let wideLayout : TypeLayout :=
    { size := { bytes := 2 }
      align := { bytes := 2 }
      backendRepr :=
        .scalar (.initialized (.int 16 false) { start := 0, end_ := 2 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 16 false) { start := 0, end_ := 2 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let wideTy : Ty := { kind := .adt "sym_test::WideTag" [], layoutIdx := 0 }
  { mkMirBody "sym_test::wide_tag_two" 0 [mkDecl .mut wideTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::WideTag" 2 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [wideLayout] } }

def orderingLessReturnBody : CapturedMir :=
  let ordLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 true) { start := 255, end_ := 1 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 true) { start := 255, end_ := 1 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let ordTy : Ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := 0 }
  { mkMirBody "sym_test::ordering_less" 0 [mkDecl .mut ordTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "core::cmp::Ordering" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [ordLayout] } }

def singleVariantReprU8FiveBody : CapturedMir :=
  let singleLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 5, end_ := 5 })
      fields := .arbitrary [] []
      variants := .single 0
      isUninhabited := false }
  let singleTy : Ty := { kind := .adt "sym_test::SingleFive" [], layoutIdx := 0 }
  { mkMirBody "sym_test::single_five" 0 [mkDecl .mut singleTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::SingleFive" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [singleLayout] } }

def nicheOptionBoolNoneBody : CapturedMir :=
  let optBoolLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 0, end_ := 2 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 0, end_ := 2 })
          0
          [ .arbitrary [] []
          , .arbitrary [{ bytes := 0 }] [0] ]
      isUninhabited := false }
  let optBoolTy : Ty :=
    { kind := .adt "core::option::Option" [.bool], layoutIdx := 0 }
  { mkMirBody "sym_test::option_bool_none" 0 [mkDecl .mut optBoolTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "core::option::Option" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [optBoolLayout] } }

theorem scalar_enum_return_edge_cases_confirmed :
    probeMirDiffBounded 16 directColorTagWithDiscrAndZeroFnAbiBody
      (initMachineStateWithMemory
        directColorTagWithDiscrAndZeroFnAbiBody [] emptyMemory) =
      (MirDiffTag.normalScalar 2 1, "none") ∧
    probeMirDiffBounded 16 reprU16FieldlessEnumBody
      (initMachineStateWithMemory
        reprU16FieldlessEnumBody [] emptyMemory) =
      (MirDiffTag.normalScalar 2 2, "none") ∧
    probeMirDiffBounded 16 orderingLessReturnBody
      (initMachineStateWithMemory
        orderingLessReturnBody [] emptyMemory) =
      (MirDiffTag.normalScalar 255 1, "none") ∧
    probeMirDiffBounded 16 singleVariantReprU8FiveBody
      (initMachineStateWithMemory
        singleVariantReprU8FiveBody [] emptyMemory) =
      (MirDiffTag.normalScalar 5 1, "none") ∧
    probeMirDiffBounded 16 nicheOptionBoolNoneBody
      (initMachineStateWithMemory
        nicheOptionBoolNoneBody [] emptyMemory) =
      (MirDiffTag.normalOther, "none") :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Kernel-checked `TotalVerificationResult` certification for
`ub_transmute_invalid_enum_tag__b7_c29` via
`verifyTotalMirDiffScalarPointBounded`.
-/
theorem confirm_total_claim_ub_transmute_invalid_enum_tag__b7_c29 :
    TotalVerificationResult
      { body := ubTransmuteInvalidEnumTagB7C29Body
        pre := fun a m => a = [] ∧ m = emptyMemory
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := 1, sizeBytes := 1 } ∨
            ∃ variantIdx,
              retVal = .aggregate variantIdx .nil ∧
              scalarEnumReturnTag?
                ubTransmuteInvalidEnumTagB7C29Body variantIdx =
                .some (1, 1) } :=
  verifyTotalMirDiffScalarPointBounded
    ubTransmuteInvalidEnumTagB7C29Body 64 [] emptyMemory 1 1

/--
`rustc`-captured layout for `#[repr(u8)] pub enum SingleFive { Only = 5 }`:
`rustc` emits `VariantsShape.multiple` with one empty `FieldsShape` and
`validRange = 5..=5` while MIR constructs `Value.aggregate 0 []`.
-/
def rustcCapturedSingleFiveBody : CapturedMir :=
  let singleLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 5, end_ := 5 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 5, end_ := 5 })
          0
          [.arbitrary [] []]
      isUninhabited := false }
  let singleTy : Ty :=
    { kind := .adt "sym_test::RustcSingleFive" [], layoutIdx := 0 }
  { mkMirBody "sym_test::rustc_single_five" 0 [mkDecl .mut singleTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::RustcSingleFive" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [singleLayout] } }

/--
User-defined `#[repr(i8)]` contiguous negative-start enum
`enum SignedContig { NegTwo = -2, NegOne = -1, Zero = 0 }` (`254..=0`) returning
variant `0` (`NegTwo = 254`).
-/
def userSignedContigI8Body : CapturedMir :=
  let scLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 true) { start := 254, end_ := 0 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 true) { start := 254, end_ := 0 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let scTy : Ty := { kind := .adt "sym_test::SignedContig" [], layoutIdx := 0 }
  { mkMirBody "sym_test::signed_contig_neg_two" 0 [mkDecl .mut scTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::SignedContig" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [scLayout] } }

/--
User-defined `#[repr(i16)]` contiguous signed enum
`enum SignedI16 { Neg = -1, Zero = 0, Pos = 1 }` (`65535..=1`) returning variant
`0` (`Neg = 65535`, `sizeBytes = 2`).
-/
def userSignedContigI16Body : CapturedMir :=
  let i16EnumLayout : TypeLayout :=
    { size := { bytes := 2 }
      align := { bytes := 2 }
      backendRepr :=
        .scalar (.initialized (.int 16 true) { start := 65535, end_ := 1 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 16 true) { start := 65535, end_ := 1 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let i16EnumTy : Ty := { kind := .adt "sym_test::SignedI16" [], layoutIdx := 0 }
  { mkMirBody "sym_test::signed_i16_neg" 0 [mkDecl .mut i16EnumTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::SignedI16" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [i16EnumLayout] } }

/--
Non-zero-based unsigned contiguous enum
`#[repr(u8)] enum NonZeroContig { A = 10, B = 11, C = 12 }` returning variant
`1` (`B = 11`).
-/
def nonZeroUnsignedContigBody : CapturedMir :=
  let nzLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 10, end_ := 12 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 10, end_ := 12 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let nzTy : Ty := { kind := .adt "sym_test::NonZeroContig" [], layoutIdx := 0 }
  { mkMirBody "sym_test::nonzero_contig_b" 0 [mkDecl .mut nzTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::NonZeroContig" 1 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [nzLayout] } }

/--
Gapped explicit-discriminant enum `#[repr(u8)] enum Gapped { A = 1, B = 5 }`
(`validRange = 1..=5`, `2` variants): per-variant discriminants are not stored
in `TypeLayout`, so returning `B` (`variantIdx = 1`) must report `.normalOther`
rather than fabricating `1` (`A`).
-/
def gappedExplicitDiscrEnumBody : CapturedMir :=
  let gapLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 1, end_ := 5 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 1, end_ := 5 })
          0
          [.arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let gapTy : Ty := { kind := .adt "sym_test::Gapped" [], layoutIdx := 0 }
  { mkMirBody "sym_test::gapped_b" 0 [mkDecl .mut gapTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::Gapped" 1 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [gapLayout] } }

/--
Niche-encoded `Option<OnlyZero>::None` (`validRange = 0..=1`, `2` variants where
`Some(OnlyZero)` occupies byte `0` and `None` uses niche byte `1`): even though
`wrappingRangeCount` equals `2`, `allVariantsFieldless` rejects the payload
variant so `None` (`variantIdx = 0`) is not misclassified as byte `0`.
-/
def nicheOptionOnlyZeroNoneBody : CapturedMir :=
  let optZeroLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 0, end_ := 1 })
          0
          [ .arbitrary [] []
          , .arbitrary [{ bytes := 0 }] [0] ]
      isUninhabited := false }
  let onlyZeroKind : RigidTy := .adt "sym_test::OnlyZero" []
  let optZeroTy : Ty :=
    { kind := .adt "core::option::Option" [onlyZeroKind], layoutIdx := 0 }
  { mkMirBody "sym_test::option_only_zero_none" 0 [mkDecl .mut optZeroTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "core::option::Option" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [optZeroLayout] } }

/--
Concrete zero-sized ADT return local (`UnitStruct` with `size.bytes = 0` in
`body.layouts`) paired with a synthetic positive-sized scalar
`fnAbi.ret.layout`: `resolveReturnLayout?` must keep the concrete zero-sized
layout and report `.normalOther`.
-/
def zstLocalWithScalarFnAbiBody : CapturedMir :=
  let zstLayout : TypeLayout :=
    { size := { bytes := 0 }
      align := { bytes := 1 }
      backendRepr := .memory
      fields := .arbitrary [] []
      variants := .single 0
      isUninhabited := false }
  let bogusScalarRetLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 0, end_ := 0 })
      fields := .arbitrary [] []
      variants := .single 0
      isUninhabited := false }
  let zstTy : Ty := { kind := .adt "sym_test::UnitStruct" [], layoutIdx := 0 }
  { mkMirBody "sym_test::zst_with_scalar_fnabi" 0 [mkDecl .mut zstTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::UnitStruct" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    fnAbi :=
      { args := []
        ret := { layout := bogusScalarRetLayout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [zstLayout] } }

/--
Scalar-represented enum return when `body.layouts` is empty, exercising fallback
to `body.fnAbi.ret.layout` for `ColorTag::Green` (`variantIdx = 1`).
-/
def emptyLayoutsFnAbiFallbackBody : CapturedMir :=
  let colorLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 0, end_ := 2 })
      fields := .arbitrary [{ bytes := 0 }] [0]
      variants :=
        .multiple
          (.initialized (.int 8 false) { start := 0, end_ := 2 })
          0
          [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
      isUninhabited := false }
  let colorTy : Ty :=
    { kind := .adt "miri_diff_corpus::ColorTag" [], layoutIdx := 0 }
  { mkMirBody "sym_test::empty_layouts_fnabi_fallback" 0 [mkDecl .mut colorTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "miri_diff_corpus::ColorTag" 1 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    fnAbi :=
      { args := []
        ret := { layout := colorLayout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [] } }

/--
Malformed 1-byte scalar layout whose `validRange` endpoint `300` exceeds
`scalarModulus 1 = 256`: rejected so out-of-width bit patterns never escape as
`.normalScalar`.
-/
def outOfWidthRangeScalarEnumBody : CapturedMir :=
  let badLayout : TypeLayout :=
    { size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr :=
        .scalar (.initialized (.int 8 false) { start := 300, end_ := 300 })
      fields := .arbitrary [] []
      variants := .single 0
      isUninhabited := false }
  let badTy : Ty := { kind := .adt "sym_test::BadRange" [], layoutIdx := 0 }
  { mkMirBody "sym_test::bad_range_enum" 0 [mkDecl .mut badTy]
      [ { statements :=
            [ mkStmt
                (.assign { local_ := 0, projection := [] }
                  (.aggregate (.adt "sym_test::BadRange" 0 .none) [])) ]
          terminator := mkTerm .return_
          isCleanup := false } ] with
    layouts :=
      { pointerBits := 64, isLittleEndian := true, entries := [badLayout] } }

theorem scalar_enum_return_b1_hardening_confirmed :
    probeMirDiffBounded 16 rustcCapturedSingleFiveBody
      (initMachineStateWithMemory
        rustcCapturedSingleFiveBody [] emptyMemory) =
      (MirDiffTag.normalScalar 5 1, "none") ∧
    probeMirDiffBounded 16 userSignedContigI8Body
      (initMachineStateWithMemory
        userSignedContigI8Body [] emptyMemory) =
      (MirDiffTag.normalScalar 254 1, "none") ∧
    probeMirDiffBounded 16 userSignedContigI16Body
      (initMachineStateWithMemory
        userSignedContigI16Body [] emptyMemory) =
      (MirDiffTag.normalScalar 65535 2, "none") ∧
    probeMirDiffBounded 16 nonZeroUnsignedContigBody
      (initMachineStateWithMemory
        nonZeroUnsignedContigBody [] emptyMemory) =
      (MirDiffTag.normalScalar 11 1, "none") ∧
    probeMirDiffBounded 16 gappedExplicitDiscrEnumBody
      (initMachineStateWithMemory
        gappedExplicitDiscrEnumBody [] emptyMemory) =
      (MirDiffTag.normalOther, "none") ∧
    probeMirDiffBounded 16 nicheOptionOnlyZeroNoneBody
      (initMachineStateWithMemory
        nicheOptionOnlyZeroNoneBody [] emptyMemory) =
      (MirDiffTag.normalOther, "none") ∧
    probeMirDiffBounded 16 zstLocalWithScalarFnAbiBody
      (initMachineStateWithMemory
        zstLocalWithScalarFnAbiBody [] emptyMemory) =
      (MirDiffTag.normalOther, "none") ∧
    probeMirDiffBounded 16 emptyLayoutsFnAbiFallbackBody
      (initMachineStateWithMemory
        emptyLayoutsFnAbiFallbackBody [] emptyMemory) =
      (MirDiffTag.normalScalar 1 1, "none") ∧
    probeMirDiffBounded 16 outOfWidthRangeScalarEnumBody
      (initMachineStateWithMemory
        outOfWidthRangeScalarEnumBody [] emptyMemory) =
      (MirDiffTag.normalOther, "none") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 13. Safe Panics Across Uninterpreted External Calls (`verifyModularSafePanicMirBounded`) -/

private def unitMirTy : Ty := { kind := .tuple [], layoutIdx := 0 }
private def neverMirTy : Ty := { kind := .never, layoutIdx := 0 }
private def fmtArgumentsMirTy : Ty :=
  { kind := .adt "core::fmt::Arguments" [], layoutIdx := 0 }

/--
Calls the unlinked `core::fmt::Arguments::<'a>::from_str` into `_1` and then
`core::panicking::panic_fmt(move _1)` (`target = .none`), as the expansion of
`panic!("...")` does.
-/
def fmtPanicMir : CapturedMir :=
  mkMirBody "sym_test::fmt_panic" 0
    [ mkDecl .mut unitMirTy
    , mkDecl .mut fmtArgumentsMirTy
    , mkDecl .not neverMirTy ]
    [ { statements := [ mkStmt (.storageLive 1), mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::fmt::Arguments::<'a>::from_str")
            [u32ConstOperand 7]
            { local_ := 1, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::panicking::panic_fmt")
            [.move { local_ := 1, projection := [] }]
            { local_ := 2, projection := [] }
            .none
            .continue_)
        isCleanup := false } ]

/--
The pure differential classifier stops at the external call, so a
`known_anneal_bug_ratchet` for `fmtPanicMir` must also check
`reachesModularSafePanicBounded`, which continues past it.
-/
theorem fmtPanic_classifier_stops_at_external_call :
    evalMirDiffTagBounded 16 fmtPanicMir
        (initMachineStateWithMemory fmtPanicMir [] emptyMemory) =
      .externalCall "core::fmt::Arguments::<'a>::from_str" ∧
    reachesPanicBounded 16 fmtPanicMir
        (initMachineStateWithMemory fmtPanicMir [] emptyMemory) = false ∧
    reachesModularSafePanicBounded 16 fmtPanicMir
        (initMachineStateWithMemory fmtPanicMir [] emptyMemory) = true :=
  ⟨rfl, rfl, rfl⟩

/--
Modular safe-panic certificate for `fmtPanicMir`, stated as generated `Verify`
certificates state it: the frame-preserving contract is spelled out with
`Trusted.*` constants only.
-/
theorem fmtPanic_modular_safe_panic_verified :
    ModularVerificationResult
      { body := fmtPanicMir
        envAssumed := MirCallContract.holdsOn
          { pre := fun _ => True
            post := fun req ans =>
              match ans with
              | .returned _ memAfter => callFramePreserved req.memory memAfter
              | .panicked memAfter => callFramePreserved req.memory memAfter
              | .aborted => True }
        pre := fun args mem => args = [] ∧ mem = emptyMemory
        post := fun _ _ _ _ => False } ∧
    ¬ ({ body := fmtPanicMir
         pre := fun args mem => args = [] ∧ mem = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  verifyModularSafePanicMirBounded fmtPanicMir [] 16 [] emptyMemory

/--
`refuteTotalClaimByBoundedPanicAcrossCalls` refutes the `TotalClaim` of
`fmtPanicMir` along either answer under which execution panics: the callee
returns (execution then reaches `core::panicking::panic_fmt`) or the callee
unwinds. An aborting callee yields `.ret .abort`, which the panic detector does
not count as a panic.
-/
theorem fmtPanic_total_refuted_along_returned_and_panicked :
    reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory) 16
        fmtPanicMir (initMachineStateWithMemory fmtPanicMir [] emptyMemory) =
      true ∧
    reachesPanicAcrossCallsBounded (fun req => .panicked req.memory) 16
        fmtPanicMir (initMachineStateWithMemory fmtPanicMir [] emptyMemory) =
      true ∧
    ¬ ({ body := fmtPanicMir
         pre := fun args mem => args = [] ∧ mem = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds ∧
    reachesPanicAcrossCallsBounded (fun _ => .aborted) 16 fmtPanicMir
        (initMachineStateWithMemory fmtPanicMir [] emptyMemory) = false :=
  ⟨rfl,
   rfl,
   refuteTotalClaimByBoundedPanicAcrossCalls _ 16 [] emptyMemory ⟨rfl, rfl⟩
     (fun req => .panicked req.memory),
   rfl⟩

/--
Panics without any external call (`255 + 4` overflows `u8`): the modular
checker agrees with `reachesPanicBounded` on call-free bodies.
-/
theorem advanceOffset_modular_safe_panic_verified :
    ModularVerificationResult
      { body := advanceOffsetSymMir
        envAssumed := framePreservingCallContract.holdsOn
        pre := fun a m =>
          a = [.scalar { bits := 255, sizeBytes := 1 }] ∧ m = emptyMemory
        post := fun _ _ _ _ => False } ∧
    ¬ ({ body := advanceOffsetSymMir
         pre := fun a m =>
           a = [.scalar { bits := 255, sizeBytes := 1 }] ∧ m = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  verifyModularSafePanicMirBounded advanceOffsetSymMir [] 8
    [.scalar { bits := 255, sizeBytes := 1 }] emptyMemory

/-- Linked helper that panics through `core::panicking::panic`. -/
def panickingHelperMir : CapturedMir :=
  mkMirBody "sym_test::panicking_helper" 0
    [ mkDecl .mut unitMirTy, mkDecl .not neverMirTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::panicking::panic")
            []
            { local_ := 1, projection := [] }
            .none
            .continue_)
        isCleanup := false } ]

/--
Calls the unlinked `sym_test::external_log` and then the linked
`sym_test::panicking_helper`, which panics. Resolving the helper after the
external call requires the restored callee table.
-/
def extCallThenLinkedPanicMir : CapturedMir :=
  mkMirBody "sym_test::ext_call_then_linked_panic" 0
    [ mkDecl .mut unitMirTy, mkDecl .mut u32MirTy, mkDecl .mut unitMirTy ]
    [ { statements := [ mkStmt (.storageLive 1), mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::external_log")
            []
            { local_ := 1, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::panicking_helper")
            []
            { local_ := 2, projection := [] }
            (.some 2)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Modular safe-panic certificate with a linked `callees` table. -/
theorem extCallThenLinkedPanic_modular_safe_panic_verified :
    ModularVerificationResult
      { body := extCallThenLinkedPanicMir
        envAssumed := framePreservingCallContract.holdsOn
        pre := fun a m => a = [] ∧ m = emptyMemory
        post := fun _ _ _ _ => False
        callees := [panickingHelperMir] } ∧
    ¬ ({ body := extCallThenLinkedPanicMir
         pre := fun a m => a = [] ∧ m = emptyMemory
         post := fun _ _ _ _ => True
         callees := [panickingHelperMir] } : TotalClaim).holds :=
  verifyModularSafePanicMirBounded extCallThenLinkedPanicMir
    [panickingHelperMir] 24 [] emptyMemory

/--
Calls the unlinked `sym_test::external_get` into `_0` and returns it: an
external call that returns normally admits no modular safe-panic certificate,
and no path that returns from the call panics.
-/
def extCallReturnsMir : CapturedMir :=
  mkMirBody "sym_test::ext_call_returns" 0
    [ mkDecl .mut u32MirTy ]
    [ { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::external_get")
            []
            { local_ := 0, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem extCallReturns_modular_safe_panic_rejected :
    ¬ (∀ answers : MirCallAnswerStream,
        reachesModularSafePanicExecBounded 8 extCallReturnsMir answers
          (.running
            (initMachineStateWithMemory extCallReturnsMir [] emptyMemory)) =
          true) ∧
    reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory) 8
        extCallReturnsMir
        (initMachineStateWithMemory extCallReturnsMir [] emptyMemory) =
      false ∧
    ¬ ({ body := extCallReturnsMir
         pre := fun args mem => args = [] ∧ mem = emptyMemory
         post := fun _ _ _ _ => True } : TotalClaim).holds := by
  refine ⟨fun h_all => ?_, rfl,
    refuteTotalClaimByBoundedPanicAcrossCalls _ 8 [] emptyMemory ⟨rfl, rfl⟩
      (fun req => .panicked req.memory)⟩
  have h_true := h_all MirCallAnswerStream.unitEmpty
  have h_false :
      reachesModularSafePanicExecBounded 8 extCallReturnsMir
        MirCallAnswerStream.unitEmpty
        (.running
          (initMachineStateWithMemory extCallReturnsMir [] emptyMemory)) =
          false := rfl
  rw [h_false] at h_true
  nomatch h_true

/--
Aborts through `core::panicking::panic_nounwind` without any external call. The
modular checker accepts it, because an abort never returns normally, but no
path panics, so `verifyModularSafePanicMirBounded` cannot certify it and its
closed instance `reachesModularSafePanicBounded` is `false`. A
`known_anneal_bug_ratchet` can therefore still record a Miri `panic` test on
which Anneal aborts.
-/
def abortOnlyMir : CapturedMir :=
  mkMirBody "sym_test::abort_only" 0
    [ mkDecl .mut unitMirTy, mkDecl .not neverMirTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "core::panicking::panic_nounwind")
            []
            { local_ := 1, projection := [] }
            .none
            .continue_)
        isCleanup := false } ]

theorem abortOnly_modular_safe_panic_rejected :
    (∀ answers : MirCallAnswerStream,
      reachesModularSafePanicExecBounded 8 abortOnlyMir answers
        (.running (initMachineStateWithMemory abortOnlyMir [] emptyMemory)) =
        true) ∧
    reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory) 8
        abortOnlyMir (initMachineStateWithMemory abortOnlyMir [] emptyMemory) =
      false ∧
    reachesModularSafePanicBounded 8 abortOnlyMir
        (initMachineStateWithMemory abortOnlyMir [] emptyMemory) = false :=
  ⟨fun _ => rfl, rfl, rfl⟩

/--
Calls the unlinked `sym_test::external_flag` into `_1` and branches on it,
returning normally when it is nonzero: the checker rejects a body whose outcome
depends on a returned value.
-/
def extCallBranchesMir : CapturedMir :=
  mkMirBody "sym_test::ext_call_branches" 0
    [ mkDecl .mut unitMirTy, mkDecl .mut boolMirTy, mkDecl .not neverMirTy ]
    [ { statements := [ mkStmt (.storageLive 1), mkStmt (.storageLive 2) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::external_flag")
            []
            { local_ := 1, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.switchInt
            (.copy { local_ := 1, projection := [] })
            { branches := [(0, 2)], otherwise := 3 })
        isCleanup := false }
    , { statements := []
        terminator :=
          mkTerm (.call
            (fnConstOp "core::panicking::panic")
            []
            { local_ := 2, projection := [] }
            .none
            .continue_)
        isCleanup := false }
    , { statements :=
          [ mkStmt (.assign { local_ := 0, projection := [] }
              (.aggregate .tuple [])) ]
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem extCallBranches_modular_safe_panic_rejected :
    reachesModularSafePanicExecBounded 16 extCallBranchesMir
        (fun _ => (.scalar { bits := 1, sizeBytes := 1 }, emptyMemory))
        (.running
          (initMachineStateWithMemory extCallBranchesMir [] emptyMemory)) =
      false ∧
    reachesModularSafePanicBounded 16 extCallBranchesMir
        (initMachineStateWithMemory extCallBranchesMir [] emptyMemory) =
      false :=
  ⟨rfl, rfl⟩

/--
Reaches `unreachable` (undefined behavior) after the external call returns:
the checker rejects a fault on any answer path.
-/
def extCallThenUbMir : CapturedMir :=
  mkMirBody "sym_test::ext_call_then_ub" 0
    [ mkDecl .mut unitMirTy, mkDecl .mut u32MirTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::external_get")
            []
            { local_ := 1, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .unreachable
        isCleanup := false } ]

theorem extCallThenUb_modular_safe_panic_rejected :
    reachesModularSafePanicBounded 8 extCallThenUbMir
        (initMachineStateWithMemory extCallThenUbMir [] emptyMemory) =
      false ∧
    reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory) 8
        extCallThenUbMir
        (initMachineStateWithMemory extCallThenUbMir [] emptyMemory) =
      false :=
  ⟨rfl, rfl⟩

/--
Calls the linked callee `sym_test::fmt_panic`, which itself performs an external
call (`core::fmt::Arguments::<'a>::from_str`) while `callStack` is non-empty and
then panics via `core::panicking::panic_fmt`, unwinding back through the
restored caller frame on `callStack`.
-/
def callerOfFmtPanicMir : CapturedMir :=
  mkMirBody "sym_test::caller_of_fmt_panic" 0
    [ mkDecl .mut unitMirTy, mkDecl .mut unitMirTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::fmt_panic")
            []
            { local_ := 1, projection := [] }
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]

theorem callerOfFmtPanic_modular_safe_panic_verified :
    ModularVerificationResult
      { body := callerOfFmtPanicMir
        envAssumed := framePreservingCallContract.holdsOn
        pre := fun a m => a = [] ∧ m = emptyMemory
        post := fun _ _ _ _ => False
        callees := [fmtPanicMir] } ∧
    ¬ ({ body := callerOfFmtPanicMir
         pre := fun a m => a = [] ∧ m = emptyMemory
         post := fun _ _ _ _ => True
         callees := [fmtPanicMir] } : TotalClaim).holds :=
  verifyModularSafePanicMirBounded callerOfFmtPanicMir
    [fmtPanicMir] 24 [] emptyMemory

/--
Calls an unlinked diverging function (`target = .none` that is not a built-in
panic or abort entrypoint): `framePreservingCallContract` permits `.returned`,
on which `resumeExternalDivergingCall` faults with `.ub`, so the modular
safe-panic checker rejects it.
-/
def divergingExtCallMir : CapturedMir :=
  mkMirBody "sym_test::diverging_ext_call" 0
    [ mkDecl .mut unitMirTy, mkDecl .not neverMirTy ]
    [ { statements := [ mkStmt (.storageLive 1) ]
        terminator :=
          mkTerm (.call
            (fnConstOp "sym_test::external_diverging")
            []
            { local_ := 1, projection := [] }
            .none
            .continue_)
        isCleanup := false } ]

theorem divergingExtCall_modular_safe_panic_rejected :
    reachesModularSafePanicBounded 8 divergingExtCallMir
        (initMachineStateWithMemory divergingExtCallMir [] emptyMemory) =
      false ∧
    reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory) 8
        divergingExtCallMir
        (initMachineStateWithMemory divergingExtCallMir [] emptyMemory) =
      false :=
  ⟨rfl, rfl⟩

end Anneal.Rustc.V2026_06_01.SymbolicEvalTests

/-!
Namespace-shadowing regression check verifying that generated modules (such as
`MiriOracleProbe` and `MiriOracleConfirm` in `crates/cargo-anneal/`) that run
`open Anneal.Rustc.V2026_06_01.SymbolicEval` and also emit a local
`def probeMirDiffExecBounded` resolve without ambiguity, and that
`SymbolicEval.probeMirDiffExecBounded` resolves cleanly alongside it.
-/
namespace MiriOracleShadowCompatCheck

-- Keep in sync with the `open` header that `crates/cargo-anneal/src/miri_oracle.rs` emits
-- for `MiriOracleProbe` / `MiriOracleConfirm` (including the otherwise-unused
-- `Trusted.Sequence`), so this check sees the same name environment.
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

def probeMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    MirDiffTag × String :=
  match fuel with
  | 0 => (.outOfFuel, "none")
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (.unit, _)) => (.normalUnit, "none")
    | .ret (.normal (.scalar sc, _)) =>
      (.normalScalar sc.bits sc.sizeBytes, "none")
    | .ret (.normal (_, _)) => (.normalOther, "none")
    | .ret .panic => (.panic, "none")
    | .ret .abort => (.abort, "none")
    | .tau st' => probeMirDiffExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => (.ub, "none")
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, "none")
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, "none")
    | .vis (.inr (.inl _)) k =>
      probeMirDiffExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, "none")

theorem local_and_qualified_probe_resolve :
    probeMirDiffExecBounded
      8
      Anneal.Rustc.V2026_06_01.SymbolicEvalTests.addBoundedMir
      (.running
        (initMachineStateWithMemory
          Anneal.Rustc.V2026_06_01.SymbolicEvalTests.addBoundedMir
          [ .scalar { bits := 10, sizeBytes := 1 }
          , .scalar { bits := 20, sizeBytes := 1 } ]
          emptyMemory)) =
      (MirDiffTag.normalScalar 30 1, "none") ∧
    Anneal.Rustc.V2026_06_01.SymbolicEval.probeMirDiffExecBounded
      64
      Anneal.Rustc.V2026_06_01.SymbolicEvalTests.ubTransmuteInvalidEnumTagB7C29Body
      (.running
        (initMachineStateWithMemory
          Anneal.Rustc.V2026_06_01.SymbolicEvalTests.ubTransmuteInvalidEnumTagB7C29Body
          []
          emptyMemory)) =
      (MirDiffTag.normalScalar 1 1, "none") :=
  ⟨rfl, rfl⟩

end MiriOracleShadowCompatCheck
