import Trusted
import Anneal
import Mir.WireframeDemo.parse_compression_flag
import Specs.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace Proof.WireframeDemo.parse_compression_flag

set_option linter.all false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.parse_compression_flag

/-!
Kernel-checked review proof for `wireframe_demo::parse_compression_flag`
(Journey 3B, `#125`).

Verifies `refineSafeSpec` (`MirContractHoldsWithSafety`):
1. Safe `parse_compression_flag` executes without Undefined Behavior across all
   `256` `u8` inputs (`0..=255`), including values `2..=255` outside `requires`.
2. Whenever `rustRequires` holds (`(flags_byte & 1) == flags_byte`, i.e. `0` or
   `1`), both the Rust `#[anneal_spec::spec]` `ensures` clause and
   `compressionFlagPost` hold.
3. `rustRequires` is provably non-vacuous (`nonVacuousRequires`).
-/


open Anneal.PureMirExec

private theorem wpReq_imp_zero_or_one (b : Nat) :
    MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body [.scalar { bits := b, sizeBytes := 1 }] →
    b = 0 ∨ b = 1 := by
  mir_lift_spec
  intro h_eq
  exact eq_zero_or_one_of_mod2_eq b (Nat.eq_of_beq_eq_true h_eq)

private theorem ensures_holds_one :
    MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] := by
  mir_lift_spec

private theorem ensures_holds_zero :
    MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body [.scalar { bits := 0, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] := by
  mir_lift_spec

private theorem ensures_holds_of_eq_one (b : Nat) (hb1 : b = 1) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] :=
  @Eq.ndrec Nat 1
    (fun x =>
      MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
        [.scalar { bits := x, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }])
    ensures_holds_one b hb1.symm

private theorem ensures_holds_of_eq_zero (b : Nat) (hb0 : b = 0) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] :=
  @Eq.ndrec Nat 0
    (fun x =>
      MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
        [.scalar { bits := x, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }])
    ensures_holds_zero b hb0.symm

private theorem compressionFlagPost_one (b : Nat) (hb1 : b = 1) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 1, sizeBytes := 1 }) := by
  subst hb1
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

private theorem compressionFlagPost_zero (b : Nat) (hb0 : b = 0) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 0, sizeBytes := 1 }) := by
  subst hb0
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

/-- Total-safety + functional verification certificate for `parse_compression_flag`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim := by
  refine verifyMirNoPanicSym _ 6 ?_
  intro args h_pre
  apply Hold.val
  rcases h_pre with ⟨b, _hb, h_args⟩
  rw [h_args]
  have h_mul18 : Nat.mul 1 8 = 8 := rfl
  refine hold_wpParse_full 6 _ _ ?_
  dsimp only [Mir.WireframeDemo.parse_compression_flag.body,
    parseBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree, operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    invalidateConflictingBorrows, mirNormalPost, boolToScalar,
    Mir.WireframeDemo.parse_compression_flag.layouts,
    sharedBorrowPerm, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsFreeze, rigidTyIsFreeze, stringEq,
    reqCtx, ensCtx, parseCtx,
    Obligations.WireframeDemo.parse_compression_flag.claim,
    Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec,
    Obligations.WireframeDemo.parse_compression_flag.rustEnsures,
    Obligations.WireframeDemo.parse_compression_flag.defaultPost,
    ItemSpec.post,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  by_cases h_odd : b % 2 = 1
  · rw [beq_mod2_zero_of_odd b h_odd]
    exact ⟨fun h_req_pair =>
      let hb1 : b = 1 :=
        eq_one_of_zero_or_one_and_odd b
          (rustRequires_imp_zero_or_one b h_req_pair) h_odd
      ⟨ensures_holds_of_eq_one b hb1, compressionFlagPost_one b hb1⟩⟩
  · rw [beq_mod2_zero_of_not_odd b h_odd]
    exact ⟨fun h_req_pair =>
      let hb0 : b = 0 :=
        eq_zero_of_zero_or_one_and_not_odd b
          (rustRequires_imp_zero_or_one b h_req_pair) h_odd
      ⟨ensures_holds_of_eq_zero b hb0, compressionFlagPost_zero b hb0⟩⟩

/-- Non-vacuity witness confirming `parse_compression_flag`'s functional
`rustRequires` contract is satisfiable (`flags_byte = 1`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.parse_compression_flag.rustRequires a := by
  refine ⟨[.scalar { bits := 1, sizeBytes := 1 }], ⟨rfl, ?_⟩⟩
  mir_lift_spec

end Proof.WireframeDemo.parse_compression_flag
