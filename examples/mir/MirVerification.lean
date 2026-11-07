import Trusted
import Anneal

namespace AnnealExamples.MirVerification

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.BitValidity
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.TraceCheck

/-!
Worked vertical slices of Rust `Runtime(PostCleanup)` MIR verification over
coinductive interaction trees (`ITree MirEffect MirOutcome`) and open Dijkstra
predicate transformers (`EffectWP`, `DWLP`, `DWP`) across all five trusted
verification gates (`VerificationResult`, `StatefulVerificationResult`,
`TraceVerificationResult`, `TotalVerificationResult`, and
`ModularVerificationResult`):

1. **Checked `u32` arithmetic vs. unchecked overflow UB** (`example_add_u32_safe_and_total`)
2. **Companion boolean specifications** (`example_companion_bool_spec_holds`)
3. **Trace-aware `switchInt` verification** (`example_branch_obs_trace_verified`)
4. **Tree Borrows mutable reborrowing vs. disabled-child aliasing UB**
   (`example_tree_borrows_reborrow_and_aliasing_refutation`)
5. **Coinductive partial correctness (`DWLP`) vs. inductive total correctness (`DWP`)**
   (`example_loops_total_vs_coinductive_partial`)
6. **Impure-by-default external/FFI calls & modular `ITree.interp` linking**
   (`example_impure_ffi_refutation_and_modular_contract`,
    `example_horizontal_caller_callee_linking`)
7. **Disjoint-footprint separation-logic framing & exclusivity**
   (`example_unalign_set_mir_and_framed`, `example_partial_heap_exclusivity`)
8. **Byte-level layout certificate checkers & unsafe pointer/slice obligations**
   (`example_layout_certificate_checkers`,
    `example_unsafe_pointer_and_slice_obligations`)
-/

/-! ## Helper Constructors for Self-Contained `CapturedMir` Fixtures -/

private def u16MirTy : Ty := { kind := .uint .u16, layoutIdx := 0 }
private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
private def u16RefMirTy : Ty := { kind := .ref .not (.uint .u16), layoutIdx := 0 }
private def u16MutRefMirTy : Ty := { kind := .ref .mut (.uint .u16), layoutIdx := 0 }
private def u32MutRefMirTy : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
private def fnDefMirTy (defPath : DefPath) : Ty := { kind := .fnDef defPath [], layoutIdx := 0 }

private def fnItemOperand (defPath : DefPath) : Operand :=
  .constant { ty := fnDefMirTy defPath, val := .zeroSized }

private def u32ConstOperand (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

@[reducible, simp]
private def defaultU32TypeLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible, simp]
private def defaultU32FnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU32TypeLayout, mode := .direct }
  conv := .rust
  canUnwind := false
}

@[reducible, simp]
private def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

@[reducible, simp]
private def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "MirVerification.lean" }

@[reducible, simp]
private def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "MirVerification.lean" }

private def mkMirBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultU32FnAbi
  layouts := emptyLayoutTable
  allocations := []
}

private theorem observe_cofix_tau
    {step : MirExecState → MirStepNode} {st₁ st₂ : MirExecState}
    (h : step st₁ = .tau st₂) :
    (ITree.cofix step st₁).observe = .tau (ITree.cofix step st₂) := by
  rw [ITree.observe_cofix, h]; rfl

private theorem observe_cofix_vis
    {step : MirExecState → MirStepNode} {st : MirExecState}
    {i : MirEffect.I} {k : MirEffect.O i → MirExecState}
    (h : step st = .vis i k) :
    (ITree.cofix step st).observe = .vis i (fun o => ITree.cofix step (k o)) := by
  rw [ITree.observe_cofix, h]; rfl

/-! ## 1. Checked `u32` Addition vs. Unchecked Overflow UB & 2. Boolean Specs -/

def addU32UncheckedMirBody : CapturedMir :=
  mkMirBody "demo::add_u32_unchecked" 2
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .not u32MirTy]
    [{ statements :=
         [mkStmt (.assign { local_ := 0, projection := [] }
           (.binaryOp .addUnchecked
             (.copy { local_ := 1, projection := [] })
             (.copy { local_ := 2, projection := [] })))]
       terminator := mkTerm .return_
       isCleanup := false }]

def addU32SafeClaim : Claim where
  body := addU32UncheckedMirBody
  pre args := args = [.scalar ⟨20, 4⟩, .scalar ⟨22, 4⟩]
  post _ ret := ret = .scalar ⟨42, 4⟩

def addU32TotalClaim : TotalClaim where
  body := addU32UncheckedMirBody
  pre args mem := args = [.scalar ⟨20, 4⟩, .scalar ⟨22, 4⟩] ∧ mem = emptyMemory
  post _ _ ret _ := ret = .scalar ⟨42, 4⟩

theorem addU32SafeClaim_verified : VerificationResult addU32SafeClaim := by
  refine Anneal.PureMirExec.verifyMirNoPanic_of_pureExec addU32SafeClaim rfl ?_
  rintro _ rfl
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  rfl

theorem addU32TotalClaim_verified : TotalVerificationResult addU32TotalClaim := by
  refine Anneal.PureMirExec.verifyTotalMir_of_pureExec addU32TotalClaim rfl
    (fun _ _ h => h.2 ▸ Anneal.PureMirExec.rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨rfl, rfl⟩
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  rfl

def overflowAddU32Claim : Claim where
  body := addU32UncheckedMirBody
  pre args := args = [.scalar ⟨4294967295, 4⟩, .scalar ⟨1, 4⟩]
  post _ _ := True

theorem not_overflowAddU32Claim_holds : ¬ overflowAddU32Claim.holds := by
  intro h_holds
  let overflowArgs : List Value := [.scalar ⟨4294967295, 4⟩, .scalar ⟨1, 4⟩]
  have h_safe := (h_holds overflowArgs rfl).1
  let step := stepMirState addU32UncheckedMirBody
  let t := mirCallTree addU32UncheckedMirBody overflowArgs
  have h_obs : t.observe =
      ITreeF.vis (E := MirEffect) (.inl (.fail FailureKind.ub))
        (fun o => ITree.cofix step (PEmpty.elim o)) :=
    observe_cofix_vis (step := step)
      (st := .running (initMachineState addU32UncheckedMirBody overflowArgs))
      (i := .inl (.fail FailureKind.ub)) (k := PEmpty.elim) rfl
  exact h_safe [] t (.refl t)
    ⟨t, .inl (.fail FailureKind.ub), _, .refl t, h_obs, trivial⟩

theorem example_add_u32_safe_and_total :
    VerificationResult addU32SafeClaim ∧
    TotalVerificationResult addU32TotalClaim ∧
    ¬ overflowAddU32Claim.holds :=
  ⟨addU32SafeClaim_verified, addU32TotalClaim_verified, not_overflowAddU32Claim_holds⟩

def eq42BoolSpecMirBody : CapturedMir :=
  mkMirBody "demo::__anodized_ensures_eq42" 1
    [mkDecl .mut boolMirTy, mkDecl .not u32MirTy]
    [{ statements :=
         [mkStmt (.assign { local_ := 0, projection := [] }
           (.binaryOp .eq
             (.copy { local_ := 1, projection := [] })
             (u32ConstOperand 42)))]
       terminator := mkTerm .return_
       isCleanup := false }]

theorem example_companion_bool_spec_holds :
    MirBoolPredicateHolds eq42BoolSpecMirBody [.scalar ⟨42, 4⟩] := by
  -- `#mir_lift_spec` introduction for a call-free, alias-free companion body.
  refine Anneal.PureMirExec.mirBoolPredicateHolds_of_pureExec _ _ rfl ?_
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  rfl

/-! ## 3. Trace-Aware `switchInt` Verification (`TraceVerificationResult`) -/

def branchObsMirBody : CapturedMir :=
  mkMirBody "demo::branch_obs" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [{ statements := []
       terminator := mkTerm (.switchInt
         (.copy { local_ := 1, projection := [] })
         { branches := [(0, 1)], otherwise := 2 })
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 0, projection := [] } (.use (u32ConstOperand 10)))]
       terminator := mkTerm .return_
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 0, projection := [] } (.use (u32ConstOperand 20)))]
       terminator := mkTerm .return_
       isCleanup := false }]

def branchObsTraceClaim : TraceClaim where
  body := branchObsMirBody
  pre args mem :=
    (args = [.scalar ⟨0, 4⟩] ∨ args = [.scalar ⟨7, 4⟩]) ∧ mem = emptyMemory
  post args _ tr out :=
    (args = [.scalar ⟨0, 4⟩] →
      tr = [Event.mk (E := MirEffect) (.inr (.inl (.emit (.event 0)))) PUnit.unit] ∧
      ∃ mem', out = .normal (.scalar ⟨10, 4⟩, mem')) ∧
    (args = [.scalar ⟨7, 4⟩] →
      tr = [Event.mk (E := MirEffect) (.inr (.inl (.emit (.event 7)))) PUnit.unit] ∧
      ∃ mem', out = .normal (.scalar ⟨20, 4⟩, mem'))

theorem example_branch_obs_trace_verified :
    TraceVerificationResult branchObsTraceClaim := by
  refine verifyTraceMirFuelFree branchObsTraceClaim ?_
  rintro _ _ ⟨(rfl | rfl), rfl⟩
  · refine ⟨fun hf => hf, fun o => ?_⟩
    cases o
    exact ⟨fun _ => ⟨rfl, _, rfl⟩, fun h_abs => by simp at h_abs⟩
  · refine ⟨fun hf => hf, fun o => ?_⟩
    cases o
    exact ⟨fun h_abs => by simp at h_abs, fun _ => ⟨rfl, _, rfl⟩⟩

/-! ## 4. Tree Borrows Mutable Reborrowing vs. Disabled-Child Aliasing UB -/

def reborrowWriteMirBody : CapturedMir :=
  mkMirBody "demo::reborrow_write_ok" 0
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy, mkDecl .mut u32MutRefMirTy]
    [{ statements :=
         [mkStmt (.storageLive 1),
          mkStmt (.storageLive 2),
          mkStmt (.assign { local_ := 1, projection := [] } (.use (u32ConstOperand 5))),
          mkStmt (.assign { local_ := 2, projection := [] }
            (.ref (.mut false) { local_ := 1, projection := [] })),
          mkStmt (.assign { local_ := 2, projection := [.deref] } (.use (u32ConstOperand 99))),
          mkStmt (.assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 2, projection := [.deref] })))]
       terminator := mkTerm .return_
       isCleanup := false }]

def reborrowWriteStatefulClaim : StatefulClaim where
  body := reborrowWriteMirBody
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ retVal mem' :=
    retVal = .scalar ⟨99, 4⟩ ∧
    lookupBorrow mem'.borrows 1 =
      some { tag := 1, targetLocal := 1, targetProjection := [], perm := .active }

theorem reborrowWriteStatefulClaim_verified :
    StatefulVerificationResult reborrowWriteStatefulClaim := by
  refine verifyStatefulMirFuelFree reborrowWriteStatefulClaim ?_
  rintro _ _ ⟨rfl, rfl⟩ retVal mem' h_out
  injection h_out with h_pair; injection h_pair with h_ret h_m
  subst h_ret h_m
  exact ⟨rfl, rfl⟩

def aliasingViolationMirBody : CapturedMir :=
  mkMirBody "demo::aliasing_violation_ub" 0
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32MutRefMirTy, mkDecl .mut u32MutRefMirTy]
    [{ statements :=
         [mkStmt (.storageLive 1),
          mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign { local_ := 1, projection := [] } (.use (u32ConstOperand 5))),
          mkStmt (.assign { local_ := 2, projection := [] }
            (.ref (.mut false) { local_ := 1, projection := [] })),
          mkStmt (.assign { local_ := 3, projection := [] }
            (.ref (.mut false) { local_ := 2, projection := [.deref] })),
          mkStmt (.assign { local_ := 2, projection := [.deref] } (.use (u32ConstOperand 10))),
          mkStmt (.assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [.deref] })))]
       terminator := mkTerm .return_
       isCleanup := false }]

def aliasingViolationClaim : Claim where
  body := aliasingViolationMirBody
  pre args := args = []
  post _ _ := True

theorem not_aliasingViolationClaim_holds : ¬ aliasingViolationClaim.holds := by
  intro h_holds
  have h_safe := (h_holds [] rfl).1
  let s₀ := initMachineState aliasingViolationMirBody []
  let step := stepMirState aliasingViolationMirBody
  let t₀ := ITree.cofix step (.running s₀)
  let st₁ := match step (.running s₀) with | .tau x => x | _ => .running s₀
  let st₂ := match step st₁ with | .tau x => x | _ => .running s₀
  let st₃ := match step st₂ with | .tau x => x | _ => .running s₀
  let st₄ := match step st₃ with | .tau x => x | _ => .running s₀
  let st₅ := match step st₄ with | .tau x => x | _ => .running s₀
  let st₆ := match step st₅ with | .tau x => x | _ => .running s₀
  let st₇ := match step st₆ with | .tau x => x | _ => .running s₀
  have h₁ : t₀.observe = .tau (ITree.cofix step st₁) := observe_cofix_tau rfl
  have h₂ : (ITree.cofix step st₁).observe = .tau (ITree.cofix step st₂) := observe_cofix_tau rfl
  have h₃ : (ITree.cofix step st₂).observe = .tau (ITree.cofix step st₃) := observe_cofix_tau rfl
  have h₄ : (ITree.cofix step st₃).observe = .tau (ITree.cofix step st₄) := observe_cofix_tau rfl
  have h₅ : (ITree.cofix step st₄).observe = .tau (ITree.cofix step st₅) := observe_cofix_tau rfl
  have h₆ : (ITree.cofix step st₅).observe = .tau (ITree.cofix step st₆) := observe_cofix_tau rfl
  have h₇ : (ITree.cofix step st₆).observe = .tau (ITree.cofix step st₇) := observe_cofix_tau rfl
  have h_tau : TauStar t₀ (ITree.cofix step st₇) :=
    .step h₁ (.step h₂ (.step h₃ (.step h₄ (.step h₅ (.step h₆ (.step h₇ (.refl _)))))))
  have h_ub : (ITree.cofix step st₇).observe =
      ITreeF.vis (E := MirEffect) (.inl (.fail FailureKind.ub))
        (fun o => ITree.cofix step (PEmpty.elim o)) :=
    observe_cofix_vis (step := step) (st := st₇)
      (i := .inl (.fail FailureKind.ub)) (k := PEmpty.elim) rfl
  exact h_safe [] t₀ (.refl t₀)
    ⟨ITree.cofix step st₇, .inl (.fail FailureKind.ub), _, h_tau, h_ub, trivial⟩

theorem example_tree_borrows_reborrow_and_aliasing_refutation :
    StatefulVerificationResult reborrowWriteStatefulClaim ∧
    ¬ aliasingViolationClaim.holds :=
  ⟨reborrowWriteStatefulClaim_verified, not_aliasingViolationClaim_holds⟩

/-! ## 5. Bounded Countdown Loop (`DWP`) vs. Infinite Loop (`DWLP` vs. `¬ TotalClaim`) -/

def countdownMirBody : CapturedMir :=
  mkMirBody "demo::countdown_loop" 1
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy]
    [{ statements := []
       terminator := mkTerm (.switchInt
         (.copy { local_ := 1, projection := [] })
         { branches := [(0, 2)], otherwise := 1 })
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 1, projection := [] }
           (.binaryOp .sub (.copy { local_ := 1, projection := [] }) (u32ConstOperand 1)))]
       terminator := mkTerm (.goto 0)
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 0, projection := [] } (.use (u32ConstOperand 0)))]
       terminator := mkTerm .return_
       isCleanup := false }]

def countdownTotalClaim : TotalClaim where
  body := countdownMirBody
  pre args mem := args = [.scalar ⟨3, 4⟩] ∧ mem = emptyMemory
  post _ _ ret _ := ret = .scalar ⟨0, 4⟩

theorem countdownTotalClaim_verified : TotalVerificationResult countdownTotalClaim := by
  refine Anneal.PureMirExec.verifyTotalMir_of_pureExec countdownTotalClaim rfl
    (fun _ _ h => h.2 ▸ Anneal.PureMirExec.rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨rfl, rfl⟩
  -- The lifting rules unroll the three loop iterations; the step budget is
  -- synthesized by the rules rather than chosen by hand.
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  rfl

def infiniteLoopMirBody : CapturedMir :=
  mkMirBody "demo::infinite_loop" 0
    [mkDecl .mut u32MirTy]
    [{ statements := [], terminator := mkTerm (.goto 0), isCleanup := false }]

def infiniteLoopPartialClaim : Claim where
  body := infiniteLoopMirBody
  pre args := args = []
  post _ _ := False

def infiniteLoopTotalClaim : TotalClaim where
  body := infiniteLoopMirBody
  pre args _ := args = []
  post _ _ _ _ := True

theorem infiniteLoopPartialClaim_verified :
    VerificationResult infiniteLoopPartialClaim := by
  refine verifyByDWLP infiniteLoopPartialClaim ?_
  rintro _ rfl
  let t₀ := mirCallTree infiniteLoopMirBody []
  refine DWLP.coinduct (fun t _ => t = t₀) ?_ rfl
  rintro t _ rfl
  have h_obs : t₀.observe = .tau t₀ := by
    unfold t₀ mirCallTree mirTree; rw [ITree.observe_cofix]; rfl
  simp only [h_obs]

theorem not_infiniteLoopTotalClaim_holds : ¬ infiniteLoopTotalClaim.holds := by
  intro h_total
  let t₀ := mirStatefulTree infiniteLoopMirBody [] emptyMemory
  have h_obs : t₀.observe = .tau t₀ := by
    unfold t₀ mirStatefulTree mirTree; rw [ITree.observe_cofix]; rfl
  have h_div : Diverges t₀ :=
    Diverges.coinduct (fun x => x = t₀)
      (fun x hx => by subst hx; simp only [h_obs])
      t₀ rfl
  exact (h_total [] emptyMemory rfl).2.2.1 ⟨[], t₀, .refl t₀, h_div⟩

theorem example_loops_total_vs_coinductive_partial :
    TotalVerificationResult countdownTotalClaim ∧
    VerificationResult infiniteLoopPartialClaim ∧
    ¬ infiniteLoopTotalClaim.holds :=
  ⟨countdownTotalClaim_verified,
   infiniteLoopPartialClaim_verified,
   not_infiniteLoopTotalClaim_holds⟩

/-! ## 6. Impure-by-Default External FFI Calls & Horizontal `ITree.interp` Linking -/

def ffiDoubleCallMirBody : CapturedMir :=
  mkMirBody "demo::ffi_double_call_assert_eq" 0
    [mkDecl .mut u32MirTy, mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy, mkDecl .mut boolMirTy]
    [{ statements :=
         [mkStmt (.storageLive 1), mkStmt (.storageLive 2), mkStmt (.storageLive 3)]
       terminator := mkTerm (.call (fnItemOperand "ffi::rand_u32") []
         { local_ := 1, projection := [] } (some 1) .unreachable)
       isCleanup := false },
     { statements := []
       terminator := mkTerm (.call (fnItemOperand "ffi::rand_u32") []
         { local_ := 2, projection := [] } (some 2) .unreachable)
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 3, projection := [] }
           (.binaryOp .eq
             (.copy { local_ := 1, projection := [] })
             (.copy { local_ := 2, projection := [] })))]
       terminator := mkTerm (.assert (.copy { local_ := 3, projection := [] })
         true 3 .unreachable)
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 0, projection := [] } (.use (u32ConstOperand 1)))]
       terminator := mkTerm .return_
       isCleanup := false }]

def impureFfiDoubleCallClaim : Claim where
  body := ffiDoubleCallMirBody
  pre args := args = []
  post _ _ := True

theorem not_impureFfiDoubleCallClaim_holds : ¬ impureFfiDoubleCallClaim.holds := by
  intro h_holds
  have h_safe := (h_holds [] rfl).1
  let s₀ := initMachineState ffiDoubleCallMirBody []
  let step := stepMirState ffiDoubleCallMirBody
  let t₀ := ITree.cofix step (.running s₀)
  let st_a := match step (.running s₀) with | .tau x => x | _ => .running s₀
  let st_b := match step st_a with | .tau x => x | _ => .running s₀
  let st_c := match step st_b with | .tau x => x | _ => .running s₀
  let s_c := match st_c with | .running x => x | _ => s₀
  have h_ta : t₀.observe = .tau (ITree.cofix step st_a) := observe_cofix_tau rfl
  have h_tb : (ITree.cofix step st_a).observe = .tau (ITree.cofix step st_b) := observe_cofix_tau rfl
  have h_tc : (ITree.cofix step st_b).observe = .tau (ITree.cofix step st_c) := observe_cofix_tau rfl
  let req₁ : MirCallReq := { defPath := "ffi::rand_u32", args := [], memory := s_c.memory }
  let k₁ : MirCallAns → MirExecState :=
    resumeExternalCall s_c s_c.frame.locals { local_ := 1, projection := [] } 1 .unreachable
  have h_vis₁ : (ITree.cofix step st_c).observe =
      ITreeF.vis (E := MirEffect) (.inr (.inr (.call req₁)))
        (fun ans => ITree.cofix step (k₁ ans)) :=
    observe_cofix_vis (step := step) (st := st_c)
      (i := .inr (.inr (.call req₁))) (k := k₁) rfl
  let ans₁ : MirCallAns := .returned (.scalar ⟨0, 4⟩) s_c.memory
  let t₁ := ITree.cofix step (k₁ ans₁)
  let s₁ := match k₁ ans₁ with | .running x => x | _ => s₀
  let req₂ : MirCallReq := { defPath := "ffi::rand_u32", args := [], memory := s₁.memory }
  let k₂ : MirCallAns → MirExecState :=
    resumeExternalCall s₁ s₁.frame.locals { local_ := 2, projection := [] } 2 .unreachable
  have h_vis₂ : t₁.observe =
      ITreeF.vis (E := MirEffect) (.inr (.inr (.call req₂)))
        (fun ans => ITree.cofix step (k₂ ans)) :=
    observe_cofix_vis (step := step) (st := k₁ ans₁)
      (i := .inr (.inr (.call req₂))) (k := k₂) rfl
  let ans₂ : MirCallAns := .returned (.scalar ⟨1, 4⟩) s₁.memory
  let t₂ := ITree.cofix step (k₂ ans₂)
  let st₃ := match step (k₂ ans₂) with | .tau x => x | _ => .running s₀
  let t₃ := ITree.cofix step st₃
  have h_tau₂ : t₂.observe = .tau t₃ := observe_cofix_tau rfl
  have h_ub₃ : t₃.observe =
      ITreeF.vis (E := MirEffect) (.inl (.fail FailureKind.ub))
        (fun o => ITree.cofix step (PEmpty.elim o)) :=
    observe_cofix_vis (step := step) (st := st₃)
      (i := .inl (.fail FailureKind.ub)) (k := PEmpty.elim) rfl
  have h_reach :
      Reaches t₀
        [Event.mk (E := MirEffect) (.inr (.inr (.call req₁))) ans₁,
         Event.mk (E := MirEffect) (.inr (.inr (.call req₂))) ans₂]
        t₂ :=
    .tau h_ta (.tau h_tb (.tau h_tc
      (.vis h_vis₁ (fun hf => hf) ans₁
        (.vis h_vis₂ (fun hf => hf) ans₂ (.refl t₂)))))
  exact h_safe _ t₂ h_reach
    ⟨t₃, .inl (.fail FailureKind.ub), _, .step h_tau₂ (.refl t₃), h_ub₃, trivial⟩

def pureConstSevenContract : CallContract MirCallReq (fun _ => MirCallAns) where
  pre req := req.defPath = "ffi::rand_u32" ∧ req.args = []
  post req ans := ans = .returned (.scalar ⟨7, 4⟩) req.memory

theorem pureConstFfiModularClaim_verified :
    ModularVerificationResult
      { body := ffiDoubleCallMirBody
        envAssumed := envSatisfiesContract pureConstSevenContract
        pre := fun args mem => args = [] ∧ mem = emptyMemory
        post := fun _ _ ret _ => ret = .scalar ⟨1, 4⟩ } := by
  refine verifyModularMirFuelFree pureConstSevenContract ffiDoubleCallMirBody
    (fun args mem => args = [] ∧ mem = emptyMemory)
    (fun _ _ ret _ => ret = .scalar ⟨1, 4⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨⟨rfl, rfl⟩, fun ans₁ h_ans₁ => ?_⟩
  subst h_ans₁
  refine ⟨⟨rfl, rfl⟩, fun ans₂ h_ans₂ => ?_⟩
  subst h_ans₂
  intro retVal _ h_out
  injection h_out with h_pair; injection h_pair with h_ret _
  exact h_ret.symm

theorem example_impure_ffi_refutation_and_modular_contract :
    ¬ impureFfiDoubleCallClaim.holds ∧
    ModularVerificationResult
      { body := ffiDoubleCallMirBody
        envAssumed := envSatisfiesContract pureConstSevenContract
        pre := fun args mem => args = [] ∧ mem = emptyMemory
        post := fun _ _ ret _ => ret = .scalar ⟨1, 4⟩ } :=
  ⟨not_impureFfiDoubleCallClaim_holds, pureConstFfiModularClaim_verified⟩

def calleeAddOneMirBody : CapturedMir :=
  mkMirBody "math::add_one_u32" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy]
    [{ statements :=
         [mkStmt (.assign { local_ := 0, projection := [] }
           (.binaryOp .add (.copy { local_ := 1, projection := [] }) (u32ConstOperand 1)))]
       terminator := mkTerm .return_
       isCleanup := false }]

def callerAddTwoMirBody : CapturedMir :=
  mkMirBody "app::add_two_u32" 1
    [mkDecl .mut u32MirTy, mkDecl .not u32MirTy, mkDecl .mut u32MirTy]
    [{ statements := [mkStmt (.storageLive 2)]
       terminator := mkTerm (.call (fnItemOperand "math::add_one_u32")
         [.copy { local_ := 1, projection := [] }]
         { local_ := 2, projection := [] } (some 1) .unreachable)
       isCleanup := false },
     { statements :=
         [mkStmt (.assign { local_ := 0, projection := [] }
           (.binaryOp .add (.copy { local_ := 2, projection := [] }) (u32ConstOperand 1)))]
       terminator := mkTerm .return_
       isCleanup := false }]

def addOneAt40Contract : CallContract MirCallReq (fun _ => MirCallAns) where
  pre req :=
    req.defPath = "math::add_one_u32" ∧
    req.args = [.scalar ⟨40, 4⟩] ∧
    req.memory = emptyMemory
  post _ ans := ans = .returned (.scalar ⟨41, 4⟩) emptyMemory

theorem callerAddTwoModular_verified :
    ModularVerificationResult
      { body := callerAddTwoMirBody
        envAssumed := envSatisfiesContract addOneAt40Contract
        pre := fun args mem => args = [.scalar ⟨40, 4⟩] ∧ mem = emptyMemory
        post := fun _ _ ret _ => ret = .scalar ⟨42, 4⟩ } := by
  refine verifyModularMirFuelFree addOneAt40Contract callerAddTwoMirBody
    (fun args mem => args = [.scalar ⟨40, 4⟩] ∧ mem = emptyMemory)
    (fun _ _ ret _ => ret = .scalar ⟨42, 4⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨⟨rfl, rfl, rfl⟩, fun ans h_ans => ?_⟩
  subst h_ans
  intro retVal _ h_out
  injection h_out with h_pair; injection h_pair with h_ret _
  exact h_ret.symm

theorem calleeAddOne_satisfies_contract :
    ∀ req : MirCallReq,
      req.defPath = calleeAddOneMirBody.defPath →
      addOneAt40Contract.pre req →
      DWLP mirNoCallWP
        (mirStatefulTree calleeAddOneMirBody req.args req.memory)
        (fun out _ => addOneAt40Contract.post req (outcomeToCallAns req.memory out))
        PUnit.unit := by
  rintro req _ ⟨_, h_args, h_mem⟩
  rw [h_args, h_mem]
  apply (Anneal.MirFuelFree.dwp_of_mirNoCallWpConverges ?_).toDWLP
  refine Anneal.MirFuelFree.MirNoCallWpConverges.mono ?_ (Anneal.PureMirExec.mirNoCallWpConverges_of_pureExec (post := fun retVal => retVal = .scalar ⟨41, 4⟩) (by rfl) ?_)
  · intro out h_out
    cases out with
    | normal rv => rcases rv with ⟨retVal, mem'⟩; rcases h_out with ⟨rfl, rfl⟩; rfl
    | panic => exact h_out.elim
    | abort => exact h_out.elim
  · apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
    apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    exact Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
      (by rfl) rfl

def rejectOtherCallsHandler : ExternalCallHandler :=
  fun _ => ITree.fail (E := MirClosedEffect) FailureKind.unsupported

theorem example_horizontal_caller_callee_linking :
    (fun args mem =>
      (mirHandledTree callerAddTwoMirBody args mem
        (linkCalleeHandler calleeAddOneMirBody rejectOtherCallsHandler)).toPartial) ≤
      MirClosedStatefulContractSpec
        (fun args mem => args = [.scalar ⟨40, 4⟩] ∧ mem = emptyMemory)
        (fun args mem => args = [.scalar ⟨40, 4⟩] ∧ mem = emptyMemory)
        (fun _ _ ret _ => ret = .scalar ⟨42, 4⟩) := by
  refine linkVerifiedMirCallee callerAddTwoModular_verified
    calleeAddOneMirBody rejectOtherCallsHandler calleeAddOne_satisfies_contract ?_
  intro req _ h_ne h_pre _
  exact False.elim (h_ne h_pre.1)

/-! ## 7. Disjoint-Footprint Separation-Logic Framing & Exclusivity -/

private def returnStubMirBody : CapturedMir :=
  mkMirBody "zerocopy::caller_return_stub" 0
    [mkDecl .mut u16RefMirTy, mkDecl .not u16MirTy, mkDecl .not u16MirTy]
    [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]

def unalignSetRawPtr : RawPtrVal := { allocId := 3, offset := 1, tag := 1 }
def disjointCallerRawPtr : RawPtrVal := { allocId := 5, offset := 0, tag := 9 }

def unalignSetCallerFrame (v : Value) : SavedCallerFrame := {
  callerBody := returnStubMirBody
  frame := {
    blockIdx := 0
    stmtIdx := 0
    locals :=
      [.uninit, .uninit, .uninit,
       .init (.aggregate 0 [.scalar ⟨0, 1⟩, .aggregate 0 [v]])]
  }
  destination := { local_ := 0, projection := [] }
  returnTarget := 0
}

def unalignSetInitMem (oldVal : Value) : Memory := {
  borrows :=
    [{ tag := 1, targetLocal := 3, targetProjection := [], perm := .active },
     { tag := 2, targetLocal := 4, targetProjection := [], perm := .frozen },
     { tag := 9, targetLocal := 5, targetProjection := [], perm := .frozen }]
  nextTag := 10
  callStack := [unalignSetCallerFrame oldVal]
}

def unalignSetMirBody : CapturedMir :=
  mkMirBody "zerocopy::Unalign::set" 3
    [mkDecl .mut u16MirTy, mkDecl .not u16MutRefMirTy,
     mkDecl .not u16MirTy, mkDecl .mut u16MirTy]
    [{ statements :=
         [mkStmt (.assign { local_ := 1, projection := [.deref, .field 0 u16MirTy] }
            (.use (.copy { local_ := 2, projection := [] }))),
          mkStmt (.assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 1, projection := [.deref, .field 0 u16MirTy] })))]
       terminator := mkTerm .return_
       isCleanup := false }]

def unalignSetStatefulClaim : StatefulClaim where
  body := unalignSetMirBody
  pre args mem :=
    ∃ oldVal : Value,
      args = [.ptr { allocId := 1, offsetBytes := 1 } 8,
              .scalar ⟨77, 2⟩,
              .aggregate 0 [oldVal]] ∧
      mem = unalignSetInitMem oldVal
  post _ mem retVal mem' :=
    retVal = .scalar ⟨77, 2⟩ ∧
    (BorrowToken unalignSetRawPtr .active).atFootprint
      { addrs := [], tags := [1] } mem' ∧
    (LifetimeToken 2).atFootprint { addrs := [], tags := [2] } mem' ∧
    AgreeOnFootprint { addrs := [], tags := [9] } mem mem'

theorem unalign_set_mir_verified :
    StatefulVerificationResult unalignSetStatefulClaim := by
  refine verifyStatefulMirFuelFree unalignSetStatefulClaim ?_
  rintro _ _ ⟨oldVal, rfl, rfl⟩ retVal mem' h_out
  injection h_out with h_pair; injection h_pair with h_ret h_m
  subst h_ret h_m
  refine ⟨rfl,
    ⟨⟨{ tag := 1, targetLocal := 3, targetProjection := [], perm := .active },
      rfl, rfl, rfl⟩, rfl⟩,
    ⟨⟨{ tag := 2, targetLocal := 4, targetProjection := [], perm := .frozen },
      rfl, (fun h => nomatch h)⟩, rfl⟩,
    ⟨(fun _ _ ha => nomatch ha), fun tag ht => ?_⟩⟩
  simp at ht; subst ht; rfl

theorem unalign_set_mir_framed_verified :
    StatefulVerificationResult
      (frameStatefulClaim unalignSetStatefulClaim
        ((BorrowToken disjointCallerRawPtr .frozen).atFootprint
          { addrs := [], tags := [9] })) :=
  statefulVerificationResult_frame_disjoint
    unalign_set_mir_verified
    (supportedBy_borrowToken disjointCallerRawPtr .frozen)
    (fun _ _ _ _ _ h_post => h_post.2.2.2)

theorem example_unalign_set_mir_and_framed :
    StatefulVerificationResult unalignSetStatefulClaim ∧
    StatefulVerificationResult
      (frameStatefulClaim unalignSetStatefulClaim
        ((BorrowToken disjointCallerRawPtr .frozen).atFootprint
          { addrs := [], tags := [9] })) :=
  ⟨unalign_set_mir_verified, unalign_set_mir_framed_verified⟩

theorem example_partial_heap_exclusivity
    (rp : RawPtrVal) (v₁ v₂ : Value) (p₁ p₂ : TreeBorrowPerm) (h : PartialHeap) :
    ¬ sepConj (PointsTo rp v₁) (PointsTo rp v₂) h ∧
    ¬ sepConj (BorrowToken rp p₁) (BorrowToken rp p₂) h :=
  ⟨pointsTo_star_exclusive rp v₁ v₂ h, borrowToken_star_exclusive rp p₁ p₂ h⟩

/-! ## 8. Layout Certificate Checkers & Unsafe Pointer/Slice Obligations -/

@[reducible]
def packetHeaderLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries :=
    [{ size := { bytes := 6 }
       align := { bytes := 1 }
       backendRepr := .memory
       fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }, { bytes := 4 }] [0, 1, 2]
       variants := .single 0
       isUninhabited := false }]
}

@[reducible]
def packetHeaderTy : Ty :=
  { kind := .adt "test::PacketHeader" [.uint .u16, .uint .u16, .uint .u16], layoutIdx := 0 }

@[reducible]
def unalignU32LayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries :=
    [{ size := { bytes := 4 }
       align := { bytes := 1 }
       backendRepr := .memory
       fields := .arbitrary [{ bytes := 0 }] [0]
       variants := .single 0
       isUninhabited := false }]
}

@[reducible]
def unalignU32Ty : Ty :=
  { kind := .adt "zerocopy::Unalign" [.uint .u32], layoutIdx := 0 }

@[reducible]
def mixedHeaderLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries :=
    [{ size := { bytes := 8 }
       align := { bytes := 1 }
       backendRepr := .memory
       fields := .arbitrary
         [{ bytes := 0 }, { bytes := 1 }, { bytes := 2 }, { bytes := 4 }]
         [0, 1, 2, 3]
       variants := .single 0
       isUninhabited := false }]
}

@[reducible]
def mixedHeaderTy : Ty :=
  { kind := .adt "test::MixedHeader" [.uint .u8, .uint .u8, .uint .u16, .uint .u32]
    layoutIdx := 0 }

theorem example_layout_certificate_checkers :
    swapBytes16 (swapBytes16 0x1234) = 0x1234 ∧
    IsUnaligned packetHeaderLayoutTable packetHeaderTy ∧
    IsFromZeros packetHeaderLayoutTable packetHeaderTy ∧
    IsFromBytes packetHeaderLayoutTable packetHeaderTy ∧
    IsIntoBytes packetHeaderLayoutTable packetHeaderTy ∧
    IsFromBytes unalignU32LayoutTable unalignU32Ty ∧
    IsIntoBytes unalignU32LayoutTable unalignU32Ty ∧
    IsUnaligned mixedHeaderLayoutTable mixedHeaderTy ∧
    IsFromZeros mixedHeaderLayoutTable mixedHeaderTy ∧
    IsFromBytes mixedHeaderLayoutTable mixedHeaderTy ∧
    IsIntoBytes mixedHeaderLayoutTable mixedHeaderTy :=
  ⟨swapBytes16_involutive (by decide),
   checkUnaligned_sound packetHeaderLayoutTable packetHeaderTy rfl,
   checkFromZeros_sound packetHeaderLayoutTable packetHeaderTy rfl,
   checkFromBytes_sound packetHeaderLayoutTable packetHeaderTy rfl,
   checkIntoBytes_sound packetHeaderLayoutTable packetHeaderTy rfl,
   checkFromBytes_sound unalignU32LayoutTable unalignU32Ty rfl,
   checkIntoBytes_sound unalignU32LayoutTable unalignU32Ty rfl,
   checkUnaligned_sound mixedHeaderLayoutTable mixedHeaderTy rfl,
   checkFromZeros_sound mixedHeaderLayoutTable mixedHeaderTy rfl,
   checkFromBytes_sound mixedHeaderLayoutTable mixedHeaderTy rfl,
   checkIntoBytes_sound mixedHeaderLayoutTable mixedHeaderTy rfl⟩

theorem example_unsafe_pointer_and_slice_obligations :
    (ValidSliceSplit { allocId := 1, offset := 0, tag := 1 } 2 4 2 2 ∧
     NonOverlappingPtrs
       { allocId := 1, offset := 0, tag := 1 }
       (sliceSplitRightPtr { allocId := 1, offset := 0, tag := 1 } 2 2)
       (2 * 2)) ∧
    (UnalignRawPtrSafe { allocId := 1, offset := 1, tag := 1 } 2 4 ∧
     evalPtrOffset { allocId := 1, offset := 1, tag := 1 } 0 4 =
       some { allocId := 1, offset := 1, tag := 1 }) ∧
    (ValidArrayToSliceCast { allocId := 1, offset := 0, tag := 1 } 2 2 4 8 ∧
     evalPtrOffset { allocId := 1, offset := 0, tag := 1 } (4 * 2) 8 =
       some { allocId := 1, offset := 8, tag := 1 }) := by
  have hSplit : ValidSliceSplit { allocId := 1, offset := 0, tag := 1 } 2 4 2 2 := by
    simp [ValidSliceSplit, ValidSliceRange, sliceSplitRightPtr]
  have hUnalign : UnalignRawPtrSafe { allocId := 1, offset := 1, tag := 1 } 2 4 :=
    unalignRawPtrSafe_of_validSliceRange (by simp [ValidSliceRange])
  have hArray : ValidArrayToSliceCast { allocId := 1, offset := 0, tag := 1 } 2 2 4 8 := by
    simp [ValidArrayToSliceCast, AlignedPtr, ValidSliceRange]
  exact
    ⟨⟨hSplit, validSliceSplit_disjoint hSplit⟩,
     ⟨hUnalign, evalPtrOffset_zero_of_unalignRawPtrSafe hUnalign⟩,
     ⟨hArray, evalPtrOffset_end_of_validArrayToSliceCast hArray⟩⟩

/-! ## 9. Runtime Trace Replay & Differential-Testing Triage Diagnostics (`TraceReplayDiag`) -/

@[reducible]
def rawAdd42Trace : RawByteTrace where
  rawArgs := [[20, 0, 0, 0], [22, 0, 0, 0]]
  initMem := emptyMemory
  inlinedCallees := []
  events := []
  outcome := .normal [42, 0, 0, 0]

@[reducible]
def rawAddTamperedOutcomeTrace : RawByteTrace :=
  { rawAdd42Trace with outcome := .normal [99, 0, 0, 0] }

@[reducible]
def rawAddOverflowUbTrace : RawByteTrace where
  rawArgs := [[255, 255, 255, 255], [1, 0, 0, 0]]
  initMem := emptyMemory
  inlinedCallees := []
  events := []
  outcome := .normal [0, 0, 0, 0]

theorem example_trace_replay_diag_and_soundness :
    (∃ obsTrace tr out,
      decodeRawByteTrace addU32UncheckedMirBody [] [] rawAdd42Trace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree addU32UncheckedMirBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out) ∧
    (diagnoseRawByteTraceFullBounded 8 addU32UncheckedMirBody [] [] rawAdd42Trace).isOk = true ∧
    (diagnoseRawByteTraceFullBounded 8 addU32UncheckedMirBody [] [] rawAdd42Trace).tagName = "ok" ∧
    (match diagnoseRawByteTraceFullBounded 8 addU32UncheckedMirBody [] [] rawAddTamperedOutcomeTrace with
     | .outcomeMismatch (.normal (.scalar ⟨42, 4⟩, _)) (.normal (.scalar ⟨99, 4⟩)) => true
     | _ => false) = true ∧
    (diagnoseRawByteTraceFullBounded 8 addU32UncheckedMirBody [] [] rawAddTamperedOutcomeTrace).tagName =
      "outcome_mismatch" ∧
    diagnoseRawByteTraceFullBounded 8 addU32UncheckedMirBody [] [] rawAddOverflowUbTrace =
      .stepFaulted .ub 0 0 ∧
    diagnoseRawByteTraceFullBounded 1 addU32UncheckedMirBody [] [] rawAdd42Trace =
      .outOfFuel 0 1 :=
  ⟨checkRawByteTraceFullBounded_sound 8 addU32UncheckedMirBody [] [] rawAdd42Trace rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl⟩

/-! ## 10. Polymorphic `MirAst` (`RigidTy.param`, `RigidTy.alias`, Parametric `LayoutTable`, and `CapturedMir.instantiate`) -/

@[reducible]
def paramTMirTy : Ty := { kind := .param 0 "T", layoutIdx := 0 }

@[reducible]
def pairParamTMirTy : Ty :=
  { kind := .tuple [.param 0 "T", .param 0 "T"], layoutIdx := 1 }

@[reducible]
def paramTPlaceholderLayout : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def pairParamTCompoundLayout : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 0 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def polySwapLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [paramTPlaceholderLayout, pairParamTCompoundLayout]
}

/--
Polymorphic `CapturedMir` body `fn swap_pair<T>(a: T, b: T) -> (T, T)` using
`RigidTy.param 0 "T"`, parametric `LayoutTable` slots (`0` for `T`, `1` for
`(T, T)`), field projections typed with `paramTMirTy`, and a `TraitImplEntry`.
-/
@[reducible]
def polySwapPairMirBody : CapturedMir := {
  defPath := "demo::swap_pair"
  argCount := 2
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  traitImpls := [
    { traitRef := { defPath := "core::clone::Clone", args := [.param 0 "T"] }
      implPath := "demo::impl_clone_T" }
  ]
  localDecls := [
    mkDecl .mut pairParamTMirTy,
    mkDecl .not paramTMirTy,
    mkDecl .not paramTMirTy,
    mkDecl .mut pairParamTMirTy
  ]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign { local_ := 3, projection := [] }
          (.aggregate .tuple
            [.copy { local_ := 1, projection := [] },
             .copy { local_ := 2, projection := [] }])),
        mkStmt (.assign { local_ := 0, projection := [] }
          (.aggregate .tuple
            [.copy { local_ := 3, projection := [.field 1 paramTMirTy] },
             .copy { local_ := 3, projection := [.field 0 paramTMirTy] }])),
        mkStmt (.storageDead 3)
      ]
      terminator := mkTerm .return_
      isCleanup := false }
  ]
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := {
    args := [
      { layout := paramTPlaceholderLayout, mode := .direct },
      { layout := paramTPlaceholderLayout, mode := .direct }
    ]
    ret := { layout := pairParamTCompoundLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := polySwapLayoutTable
  allocations := []
}

@[reducible]
def polySwapPairU32MirBody : CapturedMir :=
  polySwapPairMirBody.instantiate [(.uint .u32, defaultU32TypeLayout)]

def polySwapPairU32Claim : Claim where
  body := polySwapPairU32MirBody
  pre args := args = [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]
  post _ ret := ret = .aggregate 0 [.scalar ⟨20, 4⟩, .scalar ⟨10, 4⟩]

theorem polySwapPairU32Claim_verified : VerificationResult polySwapPairU32Claim := by
  refine Anneal.PureMirExec.verifyMirNoPanic_of_pureExec polySwapPairU32Claim rfl ?_
  rintro _ rfl
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  rfl

@[reducible]
def defaultBoolTypeLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def interleavedPolyLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [defaultU32TypeLayout, paramTPlaceholderLayout]
}

@[reducible]
def defaultU64TypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.int 64 false) { start := 0, end_ := 8 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def polyUnionCompoundLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .union 2
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [0, 1]
}

theorem example_polymorphic_mir_instantiate_and_verify :
    polySwapPairMirBody.instantiate [] = polySwapPairMirBody ∧
    polySwapPairMirBody.wellFormed = true ∧
    (polySwapPairMirBody.instantiate [(.uint .u32, defaultU32TypeLayout)]).wellFormed =
      polySwapPairMirBody.wellFormed ∧
    polySwapPairU32MirBody.wellFormed = true ∧
    polySwapPairU32MirBody.typeParamCount = 0 ∧
    polySwapPairU32MirBody.genericParams = [] ∧
    polySwapPairU32MirBody.traitImpls =
      [{ traitRef := { defPath := "core::clone::Clone", args := [.uint .u32] }
         implPath := "demo::impl_clone_T" }] ∧
    polySwapPairU32MirBody.layouts.entries =
      [defaultU32TypeLayout,
       { size := { bytes := 8 }
         align := { bytes := 4 }
         backendRepr := .memory
         fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
         variants := .single 0
         isUninhabited := false
         fieldLayouts := [] },
       defaultU32TypeLayout] ∧
    (interleavedPolyLayoutTable.instantiate [(.bool, defaultBoolTypeLayout)]).entries =
      [defaultU32TypeLayout, defaultBoolTypeLayout, defaultBoolTypeLayout] ∧
    (polyUnionCompoundLayout.recomputeFromFieldLayouts
      [defaultU32TypeLayout, defaultU64TypeLayout]).size =
      { bytes := 8 } ∧
    (polyUnionCompoundLayout.recomputeFromFieldLayouts
      [defaultU32TypeLayout, defaultU64TypeLayout]).fields =
      .union 2 ∧
    (RigidTy.instantiate [(.uint .u32, defaultU32TypeLayout)]
      (RigidTy.instantiate [(.param 0 "U", paramTPlaceholderLayout)]
        (.tuple [.param 0 "T", .param 1 "U"]))) =
      RigidTy.instantiate
        (TypeSubst.compose
          [(.param 0 "U", paramTPlaceholderLayout)]
          [(.uint .u32, defaultU32TypeLayout)])
        (.tuple [.param 0 "T", .param 1 "U"]) ∧
    polySwapPairU32MirBody.fnAbi.ret.layout.size = { bytes := 8 } ∧
    VerificationResult polySwapPairU32Claim :=
  ⟨CapturedMir.instantiate_nil polySwapPairMirBody,
   rfl,
   CapturedMir.instantiate_wellFormed polySwapPairMirBody [(.uint .u32, defaultU32TypeLayout)],
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   RigidTy.instantiate_instantiate
     [(.param 0 "U", paramTPlaceholderLayout)]
     [(.uint .u32, defaultU32TypeLayout)]
     (.tuple [.param 0 "T", .param 1 "U"]),
   rfl,
   polySwapPairU32Claim_verified⟩

/-! ## 11. Signature-Typed Predicates (`argsMatchSignature`, `retMatchesSignature`) across Slices, Struct Refs, ADTs, Raw/Fn Pointers & Polymorphic Bodies -/

@[reducible]
def sigU8TypeLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def sigUsizeTypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def sigThinPtrTypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def sigRawPtrTypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 18446744073709551615 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def sigWideSliceTypeLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
    (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
  fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

@[reducible]
def sigUsercopyStructTypeLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
    (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
  fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [1, 1]
}

@[reducible]
def sigOptionU32TypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .scalarPair
    (.initialized (.int 32 false) { start := 0, end_ := 1 })
    (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple
    (.initialized (.int 32 false) { start := 0, end_ := 1 })
    0
    [.arbitrary [] [], .arbitrary [{ bytes := 4 }] [0]]
  isUninhabited := false
}

@[reducible]
def sigResultSliceSplitTypeLayout : TypeLayout := {
  size := { bytes := 40 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple
    (.initialized (.int 64 false) { start := 0, end_ := 1 })
    0
    [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
  isUninhabited := false
}

@[reducible]
def sigSuiteLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    sigU8TypeLayout,               -- 0: u8
    sigUsizeTypeLayout,            -- 1: usize
    sigThinPtrTypeLayout,          -- 2: &T / fn(...) -> usize
    sigUsercopyStructTypeLayout,   -- 3: Usercopy (immediately after slot 2 for &Usercopy)
    sigWideSliceTypeLayout,        -- 4: &[u8] / &mut [MaybeUninit<u8>]
    sigOptionU32TypeLayout,        -- 5: Option<u32>
    sigResultSliceSplitTypeLayout, -- 6: Result<&[u8], (&[u8], &[MaybeUninit<u8>])>
    sigRawPtrTypeLayout,           -- 7: *mut u8 / *const u8
    paramTPlaceholderLayout        -- 8: generic param T placeholder
  ]
}

@[reducible]
def mkSigSuiteBody (argTys : List Ty) (retTy : Ty) (tParams : Nat := 0) : CapturedMir := {
  defPath := "demo::sig_suite"
  argCount := argTys.length
  typeParamCount := tParams
  localDecls := mkDecl .mut retTy :: argTys.map (mkDecl .not)
  basicBlocks := []
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultU32FnAbi
  layouts := sigSuiteLayoutTable
  allocations := []
}

@[reducible]
def sigSuiteLiveMem : Memory := {
  emptyMemory with
  globals := [
    { allocId := 10
      bytes := [some 1, some 2, some 3, some 4]
      relocations := []
      align := { bytes := 1 }
      mutability := .not },
    { allocId := 11
      bytes := [none, none, none, none]
      relocations := []
      align := { bytes := 1 }
      mutability := .mut }
  ]
  borrows := [
    { tag := 20
      targetLocal := 0
      targetProjection := []
      perm := .frozen
      rangeOffset := 0
      rangeLen := 16 },
    { tag := 21
      targetLocal := 1
      targetProjection := []
      perm := .active
      rangeOffset := 0
      rangeLen := 4 }
  ]
  callerLocals := [
    .init (.aggregate 0 [.scalar ⟨0x1000, 8⟩, .scalar ⟨0x2000, 8⟩]),
    .init (.aggregate 0 [
      .aggregate 0 [.unit],
      .aggregate 0 [.scalar ⟨99, 1⟩]
    ])
  ]
}

/--
Kernel-checked verification across all five `BRIEF-4.1` signature obligation
categories:
1. Wide slice parameters (`&[u8]`, `&mut [MaybeUninit<u8>]`, including
   uninitialized `MaybeUninit::uninit()` elements),
2. Struct reference parameters (`&Usercopy`, `&Range<usize>`),
3. ADT return types (`Option<u32>`,
   `Result<&[u8], (&[u8], &[MaybeUninit<u8>])>`),
4. Raw pointers (`*mut u8`, `*const u8`) and function pointers
   (`fn(*mut u8, *const u8, usize) -> usize`),
5. Polymorphic functions (`body.typeParamCount > 0`) before and after
   `CapturedMir.instantiate`.
-/
theorem example_signature_predicates_and_polymorphic_obligations :
    -- 1. Wide slice parameters: &[u8] and &mut [MaybeUninit<u8>]
    argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .ref .not (.slice (.uint .u8)), layoutIdx := 4 },
         { kind := .ref .mut (.slice (.adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8])),
           layoutIdx := 4 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨4, 8⟩],
       .aggregate 0 [.ptr ⟨21, 0⟩ 8, .scalar ⟨2, 8⟩]]
      sigSuiteLiveMem ∧
    ¬ argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .ref .not (.slice (.uint .u8)), layoutIdx := 4 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨5, 8⟩]]
      sigSuiteLiveMem ∧
    -- 2. Struct reference parameters: &Usercopy and &Range<usize>
    argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .ref .not (.adt "usercopy::Usercopy" []), layoutIdx := 2 },
         { kind := .ref .not (.adt "core::ops::range::Range" [.uint .usize]), layoutIdx := 2 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.ptr ⟨20, 0⟩ 8, .ptr ⟨20, 0⟩ 8]
      sigSuiteLiveMem ∧
    ¬ argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .ref .not (.adt "core::ops::range::Range" [.uint .usize]), layoutIdx := 2 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.ptr ⟨20, 4⟩ 8]
      sigSuiteLiveMem ∧
    -- 3. ADT return types: Option<u32> and Result<&[u8], (&[u8], &[MaybeUninit<u8>])>
    retMatchesSignature
      (mkSigSuiteBody [] { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 5 })
      (.aggregate 0 [])
      sigSuiteLiveMem ∧
    retMatchesSignature
      (mkSigSuiteBody [] { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 5 })
      (.aggregate 1 [.scalar ⟨42, 4⟩])
      sigSuiteLiveMem ∧
    retMatchesSignature
      (mkSigSuiteBody []
        { kind := .adt "core::result::Result"
            [.ref .not (.slice (.uint .u8)),
             .tuple [
               .ref .not (.slice (.uint .u8)),
               .ref .not (.slice (.adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8]))
             ]],
          layoutIdx := 6 })
      (.aggregate 0 [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨4, 8⟩]])
      sigSuiteLiveMem ∧
    retMatchesSignature
      (mkSigSuiteBody []
        { kind := .adt "core::result::Result"
            [.ref .not (.slice (.uint .u8)),
             .tuple [
               .ref .not (.slice (.uint .u8)),
               .ref .not (.slice (.adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8]))
             ]],
          layoutIdx := 6 })
      (.aggregate 1 [
        .aggregate 0 [
          .aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨2, 8⟩],
          .aggregate 0 [.ptr ⟨21, 0⟩ 8, .scalar ⟨2, 8⟩]
        ]])
      sigSuiteLiveMem ∧
    -- 4. Raw pointers (*mut u8, *const u8) and fn(*mut u8, *const u8, usize) -> usize
    argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .rawPtr .mut (.uint .u8), layoutIdx := 7 },
         { kind := .rawPtr .not (.uint .u8), layoutIdx := 7 },
         { kind := .fnPtr
             [.rawPtr .mut (.uint .u8), .rawPtr .not (.uint .u8), .uint .usize]
             (.uint .usize) .unsafe_ .rust,
           layoutIdx := 2 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.scalar ⟨0, 8⟩, .ptr ⟨999, 3⟩ 8, .ptr ⟨77, 0⟩ 8]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkSigSuiteBody
        [{ kind := .fnPtr
             [.rawPtr .mut (.uint .u8), .rawPtr .not (.uint .u8), .uint .usize]
             (.uint .usize) .unsafe_ .rust,
           layoutIdx := 2 }]
        { kind := .uint .usize, layoutIdx := 1 })
      [.scalar ⟨0, 8⟩]
      emptyMemory ∧
    -- 5. Polymorphic body before and after CapturedMir.instantiate
    ¬ argsMatchSignature
      polySwapPairMirBody
      [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]
      emptyMemory ∧
    argsMatchSignature
      polySwapPairU32MirBody
      [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]
      emptyMemory ∧
    retMatchesSignature
      polySwapPairU32MirBody
      (.aggregate 0 [.scalar ⟨20, 4⟩, .scalar ⟨10, 4⟩])
      emptyMemory ∧
    ¬ argsMatchSignature
      polySwapPairU32MirBody
      [.scalar ⟨10, 1⟩, .scalar ⟨20, 4⟩]
      emptyMemory := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat,
    pow2Nat,
    Trusted.Sequence.get?,
    Trusted.Sequence.length,
    UintTy.byteWidth,
    UintTy.bitWidth,
    IntTy.byteWidth,
    IntTy.bitWidth,
    FloatTy.byteWidth,
    appendTypeLayouts,
    setTypeLayoutAt,
    lookupFieldLayouts,
    computeArbitraryFieldsAux,
    computeUnionSizeAndAlign,
    computeAggregateBackendRepr,
    tagScalarByteWidth,
    recomputeVariantShapesAux,
    TypeLayout.recomputeFromFieldLayouts,
    Trusted.Rustc.V2026_06_01.Layout.substitutePlaceholderEntries,
    Trusted.Rustc.V2026_06_01.Layout.recomputeEntriesWith,
    LayoutTable.appendParamLayouts,
    LayoutTable.lookup,
    TypeSubst.lookup,
    TypeSubst.layouts,
    TypeSubst.length,
    RigidTy.instantiate,
    RigidTy.instantiateList,
    RigidTy.hasSubstParam,
    RigidTy.hasSubstParamList,
    RigidTy.isCompoundSubstParam,
    RigidTy.isTrivialZst,
    RigidTy.computeLayout,
    RigidTy.computeLayoutList,
    Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LayoutTable.instantiate,
    Ty.instantiate,
    ConstOperand.instantiate,
    TraitRef.instantiate,
    TraitImplEntry.instantiate,
    TraitImplEntry.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.appendTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.collectBodyTys,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteTyParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeTyCompoundLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteDeclParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeDeclCompoundLayoutsAux,
    LayoutTable.instantiateForBody,
    LayoutTable.instantiateForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.recomputeMode,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateForDecl,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateListForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.FnAbi.instantiate,
    dropGenericParams,
    CapturedMir.instantiate
  ] <;> decide

/-! ## 12. Signature Predicates over Capture-Shaped Layout Tables: Pointer Fields, Captured Field Layouts, Unrecorded Pointee Layouts & the Monomorphic Signature Guard -/

/-- `struct Cursor<'a> { buf: &'a [u8], pos: usize }` as interned by
`anneal-rustc-capture` (`fieldLayouts` in source field order). -/
@[reducible]
def rcCursorTypeLayout : TypeLayout := {
  size := { bytes := 24 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 16 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [2, 0]
}

/-- `NonNull<u8> { pointer: *const u8 }`: the nonzero niche lives on the struct
layout, while the captured field layout is the nullable `*const u8`. -/
@[reducible]
def rcNonNullU8TypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr :=
    .scalar (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [3]
}

/-- `struct Usercopy { a: usize, b: usize }` with captured field layouts. -/
@[reducible]
def rcUsercopyTypeLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
    (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
  fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [0, 0]
}

/-- `&dyn core::fmt::Debug`: a non-null data pointer and a non-null vtable
pointer. -/
@[reducible]
def rcWideDynTypeLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
    (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
  fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

/-- `Option<bool>`, whose `None` variant occupies the bool niche value `2`. -/
@[reducible]
def rcOptionBoolTypeLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 2 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple
    (.initialized (.int 8 false) { start := 0, end_ := 2 })
    0
    [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]]
  isUninhabited := false
}

/-- `enum Tagged<T> { Data(u8, T), Empty }` at `T = bool`, with an explicit
`u8` tag. -/
@[reducible]
def rcTaggedBoolTypeLayout : TypeLayout := {
  size := { bytes := 3 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple
    (.initialized (.int 8 false) { start := 0, end_ := 1 })
    0
    [.arbitrary [{ bytes := 1 }, { bytes := 2 }] [0, 1], .arbitrary [] []]
  isUninhabited := false
}

/-- `ControlFlow<u8, bool>`: `Continue(bool)` is variant `0` and `Break(u8)` is
variant `1`, the reverse of the type-argument order. -/
@[reducible]
def rcControlFlowU8BoolTypeLayout : TypeLayout := {
  size := { bytes := 2 }
  align := { bytes := 1 }
  backendRepr := .scalarPair
    (.initialized (.int 8 false) { start := 0, end_ := 1 })
    (.initialized (.int 8 false) { start := 0, end_ := 255 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple
    (.initialized (.int 8 false) { start := 0, end_ := 1 })
    0
    [.arbitrary [{ bytes := 1 }] [0], .arbitrary [{ bytes := 1 }] [0]]
  isUninhabited := false
}

/-- `struct TaggedStruct<T> { tag: u8, val: T }` at `T = bool` without captured
`fieldLayouts` (e.g. after layout instantiation or beyond the capture recursion
depth): its `ScalarPair` `backendRepr` validates `tag: u8` (`0..=255`) and
`val: bool` (`0..=1`) instead of mistyping field `0` positionally as `T = bool`. -/
@[reducible]
def rcTaggedStructBoolTypeLayout : TypeLayout := {
  size := { bytes := 2 }
  align := { bytes := 1 }
  backendRepr := .scalarPair
    (.initialized (.int 8 false) { start := 0, end_ := 255 })
    (.initialized (.int 8 false) { start := 0, end_ := 1 })
  fields := .arbitrary [{ bytes := 0 }, { bytes := 1 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

/-- `Cell<u32>` without captured `fieldLayouts`: its only field is an
`UnsafeCell<u32>`, not a `u32`. -/
@[reducible]
def rcCellU32TypeLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
}

/-- `UnsafeCell<bool>` without captured `fieldLayouts`: its only field is a
`bool`. -/
@[reducible]
def rcUnsafeCellBoolTypeLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
}

/-- `struct Reordered { a: u8, b: u32 }` without captured `fieldLayouts`: rustc
places `b` at offset `0`, so the first `ScalarPair` component is `b`. -/
@[reducible]
def rcReorderedTypeLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .scalarPair
    (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    (.initialized (.int 8 false) { start := 0, end_ := 255 })
  fields := .arbitrary [{ bytes := 4 }, { bytes := 0 }] [1, 0]
  variants := .single 0
  isUninhabited := false
}

/-- Deduplicated layout table shaped like `anneal-rustc-capture` output: no
pointee layout is interned next to the shared thin-pointer slot `1`. -/
@[reducible]
def rcLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    sigUsizeTypeLayout,           -- 0: usize
    sigThinPtrTypeLayout,         -- 1: &Usercopy (shared by every thin reference)
    sigWideSliceTypeLayout,       -- 2: &[u8]
    sigRawPtrTypeLayout,          -- 3: *const u8
    rcCursorTypeLayout,           -- 4: Cursor<'_>
    rcNonNullU8TypeLayout,        -- 5: NonNull<u8>
    rcUsercopyTypeLayout,         -- 6: Usercopy
    rcWideDynTypeLayout,          -- 7: &dyn Debug / &mut dyn Debug
    rcOptionBoolTypeLayout,       -- 8: Option<bool>
    rcTaggedBoolTypeLayout,       -- 9: Tagged<bool>
    rcControlFlowU8BoolTypeLayout, -- 10: ControlFlow<u8, bool>
    rcTaggedStructBoolTypeLayout,  -- 11: TaggedStruct<bool> (without fieldLayouts)
    rcCellU32TypeLayout,           -- 12: Cell<u32> (without fieldLayouts)
    rcUnsafeCellBoolTypeLayout,    -- 13: UnsafeCell<bool> (without fieldLayouts)
    rcReorderedTypeLayout          -- 14: Reordered (without fieldLayouts)
  ]
}

@[reducible]
def mkRcBody (argTys : List Ty) (retTy : Ty) (extraLocals : List Ty := []) :
    CapturedMir := {
  defPath := "demo::rc_suite"
  argCount := argTys.length
  localDecls :=
    mkDecl .mut retTy ::
      List.append (argTys.map (mkDecl .not)) (extraLocals.map (mkDecl .mut))
  basicBlocks := []
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultU32FnAbi
  layouts := rcLayoutTable
  allocations := []
}

@[reducible]
def rcMem : Memory := {
  emptyMemory with
  globals := [
    { allocId := 10
      bytes := [some 1, some 2, some 3, some 4]
      relocations := []
      align := { bytes := 1 }
      mutability := .not }
  ]
  borrows := [
    { tag := 20
      targetLocal := 0
      targetProjection := []
      perm := .frozen
      rangeOffset := 0
      rangeLen := 16 },
    { tag := 22
      targetLocal := 0
      targetProjection := []
      perm := .disabled
      rangeOffset := 0
      rangeLen := 16 },
    { tag := 23
      targetLocal := 1
      targetProjection := []
      perm := .frozen
      rangeOffset := 0
      rangeLen := 8 },
    { tag := 24
      targetLocal := 0
      targetProjection := [.field 1 { kind := .uint .usize, layoutIdx := 0 }]
      perm := .frozen
      rangeOffset := 8
      rangeLen := 8 },
    -- Projection-governed sub-place borrows, as `Rvalue.ref` creates them
    -- (`&usercopy.b` resolves; field `5` does not exist).
    { tag := 25
      targetLocal := 0
      targetProjection := [.field 1 { kind := .uint .usize, layoutIdx := 0 }]
      perm := .frozen },
    { tag := 26
      targetLocal := 0
      targetProjection := [.field 5 { kind := .uint .usize, layoutIdx := 0 }]
      perm := .frozen },
    { tag := 27
      targetLocal := 0
      targetProjection := [.subslice 1 2 false]
      perm := .frozen }
  ]
  callerLocals := [
    .init (.aggregate 0 [.scalar ⟨1, 8⟩, .scalar ⟨2, 8⟩]),
    .init (.aggregate 0 [.scalar ⟨1, 8⟩])
  ]
}

@[reducible]
def rcUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }

@[reducible]
def rcRefUsercopyTy : Ty :=
  { kind := .ref .not (.adt "usercopy::Usercopy" []), layoutIdx := 1 }

@[reducible]
def rcUsercopyTy : Ty := { kind := .adt "usercopy::Usercopy" [], layoutIdx := 6 }

/--
Kernel-checked signature validation over a capture-shaped layout table:
1. Struct fields of pointer type (`Cursor { buf: &[u8], .. }`) validate against
   their pointer `ScalarLayout` and its `WrappingRange` (null `buf` rejected).
2. Captured field layouts are authoritative over type arguments:
   `NonNull<u8>`'s field is a `*const u8`, and the struct-level nonzero niche
   rejects a null pointer.
3. A `&Usercopy` receiver whose pointee layout is not recorded must point into
   a live borrow with compatible permission and within `[rangeOffset, rangeOffset + rangeLen]`
   (dangling, `.disabled`, and before-`rangeOffset` references are rejected), and when
   a `Usercopy` local records the layout, the borrowed caller value is validated against it.
-/
theorem example_capture_shaped_signature_predicates :
    argsMatchSignature
      (mkRcBody [{ kind := .adt "demo::Cursor" [], layoutIdx := 4 }] rcUsizeTy)
      [.aggregate 0 [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨4, 8⟩], .scalar ⟨0, 8⟩]]
      rcMem ∧
    ¬ argsMatchSignature
      (mkRcBody [{ kind := .adt "demo::Cursor" [], layoutIdx := 4 }] rcUsizeTy)
      [.aggregate 0 [.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨4, 8⟩], .scalar ⟨0, 8⟩]]
      rcMem ∧
    argsMatchSignature
      (mkRcBody
        [{ kind := .adt "core::ptr::non_null::NonNull" [.uint .u8], layoutIdx := 5 }]
        rcUsizeTy)
      [.aggregate 0 [.ptr ⟨10, 0⟩ 8]]
      rcMem ∧
    ¬ argsMatchSignature
      (mkRcBody
        [{ kind := .adt "core::ptr::non_null::NonNull" [.uint .u8], layoutIdx := 5 }]
        rcUsizeTy)
      [.aggregate 0 [.scalar ⟨0, 8⟩]]
      rcMem ∧
    argsMatchSignature (mkRcBody [rcRefUsercopyTy] rcUsizeTy) [.ptr ⟨20, 0⟩ 8] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefUsercopyTy] rcUsizeTy) [.ptr ⟨24, 8⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefUsercopyTy] rcUsizeTy) [.ptr ⟨24, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefUsercopyTy] rcUsizeTy) [.ptr ⟨99, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefUsercopyTy] rcUsizeTy) [.ptr ⟨22, 0⟩ 8] rcMem ∧
    argsMatchSignature
      (mkRcBody [rcRefUsercopyTy] rcUsizeTy [rcUsercopyTy]) [.ptr ⟨20, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature
      (mkRcBody [rcRefUsercopyTy] rcUsizeTy [rcUsercopyTy]) [.ptr ⟨23, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature
      (mkRcBody [rcRefUsercopyTy] rcUsizeTy [rcUsercopyTy]) [.ptr ⟨20, 8⟩ 8] rcMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    rcMem,
    rcLayoutTable,
    mkRcBody,
    rcUsizeTy,
    rcRefUsercopyTy,
    rcUsercopyTy,
    rcCursorTypeLayout,
    rcNonNullU8TypeLayout,
    rcUsercopyTypeLayout,
    sigUsizeTypeLayout,
    sigThinPtrTypeLayout,
    sigWideSliceTypeLayout,
    sigRawPtrTypeLayout
  ] <;> decide

@[reducible]
def rcRefDynTy (m : Mutability) : Ty :=
  { kind := .ref m (.dynamic "core::fmt::Debug"), layoutIdx := 7 }

@[reducible]
def rcRefExternTy : Ty :=
  { kind := .ref .not (.foreign "demo::Opaque"), layoutIdx := 1 }

/--
Kernel-checked validation of references whose pointee layout is known only at
run time, which are inhabited and therefore must not make signature-typed
preconditions unsatisfiable:
1. `&dyn Trait` is a wide pointer whose data pointer must be live and whose
   vtable word must be non-null. Thin pointers, null vtables, dangling data
   pointers, and `&mut dyn Trait` through a frozen borrow are rejected.
2. `&ExternType` is a thin pointer that must point into a live allocation.
-/
theorem example_dyn_and_extern_reference_signatures :
    argsMatchSignature (mkRcBody [rcRefDynTy .not] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨0x5000, 8⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefDynTy .not] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨20, 0⟩ 8, .scalar ⟨0x5000, 8⟩]] rcMem ∧
    retMatchesSignature (mkRcBody [] (rcRefDynTy .not))
      (.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨0x5000, 8⟩]) rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefDynTy .not] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨10, 0⟩ 8, .scalar ⟨0, 8⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefDynTy .not] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨0x5000, 8⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefDynTy .not] rcUsizeTy)
      [.ptr ⟨10, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefDynTy .mut] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨20, 0⟩ 8, .scalar ⟨0x5000, 8⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefExternTy] rcUsizeTy) [.ptr ⟨10, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefExternTy] rcUsizeTy) [.ptr ⟨99, 0⟩ 8] rcMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    rcMem,
    rcLayoutTable,
    mkRcBody,
    rcUsizeTy,
    rcRefDynTy,
    rcRefExternTy,
    rcCursorTypeLayout,
    rcNonNullU8TypeLayout,
    rcUsercopyTypeLayout,
    rcWideDynTypeLayout,
    sigUsizeTypeLayout,
    sigThinPtrTypeLayout,
    sigWideSliceTypeLayout,
    sigRawPtrTypeLayout
  ] <;> decide

@[reducible]
def rcOptionBoolTy : Ty :=
  { kind := .adt "core::option::Option" [.bool], layoutIdx := 8 }

@[reducible]
def rcTaggedBoolTy : Ty := { kind := .adt "demo::Tagged" [.bool], layoutIdx := 9 }

@[reducible]
def rcControlFlowU8BoolTy : Ty :=
  { kind := .adt "core::ops::control_flow::ControlFlow" [.uint .u8, .bool],
    layoutIdx := 10 }

@[reducible]
def rcTaggedStructBoolTy : Ty :=
  { kind := .adt "demo::TaggedStruct" [.bool], layoutIdx := 11 }

/--
Kernel-checked typing of multi-variant enum payloads and single-variant generic
structs without captured `fieldLayouts`:
1. `Option<T>` and `Result<T, E>` payloads are exactly their type arguments, so
   `Some(2)` is rejected as an `Option<bool>`.
2. Other generic enums are checked structurally, because their payload types
   need not follow their type arguments: `Tagged<bool>::Data(200, true)` has a
   `u8` field, and `ControlFlow<u8, bool>::Break(200)` is variant `1` although
   `u8` is the first type argument. Variant indices and payload arity are still
   checked.
3. Single-variant generic structs without captured `fieldLayouts` (other than
   standard-library single-type wrappers `Range`/`ManuallyDrop`/`UnsafeCell`/`Cell`)
   validate against `parentLayout.backendRepr` rather than positional `adtArgs`, so
   `TaggedStruct<bool> { tag: 200, val: true }` is accepted and `val = 2` is rejected.
-/
theorem example_generic_enum_payload_signatures :
    retMatchesSignature (mkRcBody [] rcOptionBoolTy)
      (.aggregate 1 [.scalar ⟨1, 1⟩]) rcMem ∧
    retMatchesSignature (mkRcBody [] rcOptionBoolTy) (.aggregate 0 []) rcMem ∧
    ¬ retMatchesSignature (mkRcBody [] rcOptionBoolTy)
      (.aggregate 1 [.scalar ⟨2, 1⟩]) rcMem ∧
    argsMatchSignature (mkRcBody [rcTaggedBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨200, 1⟩, .scalar ⟨1, 1⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcTaggedBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨200, 1⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcControlFlowU8BoolTy] rcUsizeTy)
      [.aggregate 1 [.scalar ⟨200, 1⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcControlFlowU8BoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨1, 1⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcControlFlowU8BoolTy] rcUsizeTy)
      [.aggregate 2 [.scalar ⟨200, 1⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcTaggedStructBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨200, 1⟩, .scalar ⟨1, 1⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcTaggedStructBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨200, 1⟩, .scalar ⟨2, 1⟩]] rcMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    rcMem,
    rcLayoutTable,
    mkRcBody,
    rcUsizeTy,
    rcOptionBoolTy,
    rcTaggedBoolTy,
    rcControlFlowU8BoolTy,
    rcTaggedStructBoolTy,
    rcCursorTypeLayout,
    rcNonNullU8TypeLayout,
    rcUsercopyTypeLayout,
    rcWideDynTypeLayout,
    rcOptionBoolTypeLayout,
    rcTaggedBoolTypeLayout,
    rcControlFlowU8BoolTypeLayout,
    rcTaggedStructBoolTypeLayout,
    sigUsizeTypeLayout,
    sigThinPtrTypeLayout,
    sigWideSliceTypeLayout,
    sigRawPtrTypeLayout
  ] <;> decide

@[reducible]
def rcCellU32Ty : Ty := { kind := .adt "core::cell::Cell" [.uint .u32], layoutIdx := 12 }

@[reducible]
def rcUnsafeCellBoolTy : Ty :=
  { kind := .adt "core::cell::UnsafeCell" [.bool], layoutIdx := 13 }

@[reducible]
def rcReorderedTy : Ty := { kind := .adt "demo::Reordered" [], layoutIdx := 14 }

@[reducible]
def rcRefUsizeTy : Ty := { kind := .ref .not (.uint .usize), layoutIdx := 1 }

@[reducible]
def rcRefOpaqueTy : Ty := { kind := .ref .not (.adt "demo::Opaque" []), layoutIdx := 1 }

@[reducible]
def rcRefSliceUsizeTy : Ty := { kind := .ref .not (.slice (.uint .usize)), layoutIdx := 2 }

/--
Kernel-checked validation of aggregates without captured field layouts and of
references to borrowed sub-places:
1. `Cell<u32>` holds an `UnsafeCell<u32>`, not a `u32`, so its field is checked
   against the `u32` scalar after unwrapping the newtype; `UnsafeCell<T>` holds
   a `T` and is typed by its type argument.
2. `struct Reordered { a: u8, b: u32 }` places `b` at offset `0`, so `b` is
   checked against the first `ScalarPair` component and `a` against the second.
3. Borrowing the sub-place `usercopy.b` records the projection `[.field 1]`, and
   borrowing a subslice records `[.subslice 1 2 false]`. The projected caller
   value is validated against a known pointee or slice element type, a pointee
   of unrecorded layout only requires the projection to resolve, and an
   unresolvable projection or oversized subslice length is rejected.
-/
theorem example_layoutless_fields_and_subplace_borrows :
    argsMatchSignature (mkRcBody [rcCellU32Ty] rcUsizeTy)
      [.aggregate 0 [.aggregate 0 [.scalar ⟨5, 4⟩]]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcCellU32Ty] rcUsizeTy)
      [.aggregate 0 [.aggregate 0 [.scalar ⟨5, 1⟩]]] rcMem ∧
    argsMatchSignature (mkRcBody [rcUnsafeCellBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨1, 1⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcUnsafeCellBoolTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨2, 1⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcReorderedTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨70000, 4⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcReorderedTy] rcUsizeTy)
      [.aggregate 0 [.scalar ⟨5, 4⟩, .scalar ⟨70000, 4⟩]] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefUsizeTy] rcUsizeTy) [.ptr ⟨25, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefUsizeTy] rcUsizeTy) [.ptr ⟨26, 0⟩ 8] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefOpaqueTy] rcUsizeTy) [.ptr ⟨25, 0⟩ 8] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefOpaqueTy] rcUsizeTy) [.ptr ⟨26, 0⟩ 8] rcMem ∧
    argsMatchSignature (mkRcBody [rcRefSliceUsizeTy] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨27, 0⟩ 8, .scalar ⟨1, 8⟩]] rcMem ∧
    ¬ argsMatchSignature (mkRcBody [rcRefSliceUsizeTy] rcUsizeTy)
      [.aggregate 0 [.ptr ⟨27, 0⟩ 8, .scalar ⟨2, 8⟩]] rcMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    rcMem,
    rcLayoutTable,
    mkRcBody,
    rcUsizeTy,
    rcCellU32Ty,
    rcUnsafeCellBoolTy,
    rcReorderedTy,
    rcRefUsizeTy,
    rcRefOpaqueTy,
    rcRefSliceUsizeTy,
    rcCellU32TypeLayout,
    rcUnsafeCellBoolTypeLayout,
    rcReorderedTypeLayout,
    readProjectedValue,
    extractSubslice,
    takeValues,
    dropValues,
    Trusted.Sequence.get?,
    Trusted.Sequence.length,
    sigUsizeTypeLayout,
    sigThinPtrTypeLayout,
    sigWideSliceTypeLayout
  ] <;> decide

/--
The monomorphic signature guard emitted beside `statefulClaim`, `totalClaim`,
`modularClaim`, and `ubExceptionClaim` certificates rejects generic bodies and
unlowered signature types, and accepts monomorphic and instantiated bodies
(including the `&dyn Trait` signature validated above).
-/
theorem example_signature_monomorphic_guard :
    signatureIsMonomorphic
        (mkRcBody [{ kind := .adt "demo::Cursor" [], layoutIdx := 4 }] rcUsizeTy) =
      true ∧
    signatureIsMonomorphic (mkRcBody [rcRefDynTy .not] rcUsizeTy) = true ∧
    signatureIsMonomorphic polySwapPairMirBody = false ∧
    signatureIsMonomorphic polySwapPairU32MirBody = true ∧
    signatureIsMonomorphic
        (mkRcBody [{ kind := .other "T", layoutIdx := 0 }] rcUsizeTy) =
      false := by
  decide

end AnnealExamples.MirVerification
