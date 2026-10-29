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

private def defaultU32TypeLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

private def defaultU32FnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU32TypeLayout, mode := .direct }
  conv := .rust
  canUnwind := false
}

private def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

private def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "MirVerification.lean" }

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
  refine verifyMirBounded addU32SafeClaim 4 ?_
  rintro _ rfl retVal _ h_out
  injection h_out with h_pair; injection h_pair with h_ret _
  exact h_ret.symm

theorem addU32TotalClaim_verified : TotalVerificationResult addU32TotalClaim := by
  refine verifyTotalMirBounded addU32TotalClaim 4 ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨.scalar ⟨42, 4⟩, _, rfl, rfl⟩

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
  refine mirBoolPredicateHolds_of_bounded 4 eq42BoolSpecMirBody [.scalar ⟨42, 4⟩] ?_
  intro retVal _ h_out
  injection h_out with h_pair; injection h_pair with h_ret _
  exact h_ret.symm

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
  refine verifyTraceMirBounded branchObsTraceClaim 5 ?_
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
  refine verifyStatefulMirBounded reborrowWriteStatefulClaim 10 ?_
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
  refine verifyTotalMirBounded countdownTotalClaim 16 ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨.scalar ⟨0, 4⟩, _, rfl, rfl⟩

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
  refine verifyModularMirBounded pureConstSevenContract ffiDoubleCallMirBody
    (fun args mem => args = [] ∧ mem = emptyMemory)
    (fun _ _ ret _ => ret = .scalar ⟨1, 4⟩) 11 ?_
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
  refine verifyModularMirBounded addOneAt40Contract callerAddTwoMirBody
    (fun args mem => args = [.scalar ⟨40, 4⟩] ∧ mem = emptyMemory)
    (fun _ _ ret _ => ret = .scalar ⟨42, 4⟩) 6 ?_
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
  apply dwlp_cofix_of_wpCoalBounded (fuel := 4)
  exact rfl

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
  refine verifyStatefulMirBounded unalignSetStatefulClaim 5 ?_
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

end AnnealExamples.MirVerification
