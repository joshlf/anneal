/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Safety
import LeanMiriSpec.Correspondence.Witness
import LeanMiriSpec.Correspondence.WitLM1_2
import LeanMiriSpec.Correspondence.WitLM4_2
import LeanMiriSpec.Correspondence.WitLM3_2
import LeanMiriSpec.Correspondence.WitLM2_1
import LeanMiriSpec.Correspondence.WitLM2_2
import LeanMiriSpec.Correspondence.WitLM2_3
import LeanMiriSpec.Correspondence.WitLM2_4
import LeanMiriSpec.Correspondence.WitLM4_1
import LeanMiriSpec.Correspondence.WitLM3_3
import LeanMiriSpec.Correspondence.WitLM1_3

/-!
# `LM-4.3`: `miri-diff` Formal Witness Suite

Kernel-checked whole-program witnesses, modeled on the `miri-diff` corpus
(`tests/miri-diff/corpus/src/lib.rs`, `tests/miri-diff/manifest.toml`), for the
whole-program semantics of `Safety.lean`: Anneal's `mirTree` (`TreeSafe`,
`ReachesRet`, `MirReachesUB`) and `lean-miri`'s `RunLoop` semantics
`miriSystem` (`System.Safe`, `System.PartialCorrect`,
`System.ReachesOutcome (.undefinedBehavior _)`, `InfiniteRun`). Every witness
runs both machines on the same body; `AgreeReturns` and `AgreeUB` bundle the
agreeing whole-program facts.

1. Scalars: `w1_div_returns`, `w1_div_by_zero_ub`, `w1_div_treeSafe_iff_miriSafe`
   (the unconditional equivalence for every divisor), `w1_switch_case`,
   `w1_switch_otherwise`, `w1_switch_treeSafe_iff_miriSafe` (for every
   scrutinee), `w1_cast_sign_extend`, `w1_cast_treeSafe_iff_miriSafe`,
   `w1_checked_add_no_overflow`, `w1_checked_add_overflow_ub`,
   `w1_checked_add_treeSafe_iff_miriSafe` (for every `rhs`, through the
   body-specific closed simulation `checkedAdd_stepClosedSim`), the terminating
   conditional loop `w1_count_loop_returns` (`SwitchInt` exit, in the
   unconditional fragment), the diverging safe loop `w1_loop_diverges_safely`
   (`InfiniteRun`, `System.Safe`, `TreeSafe`), the agreeing `.unsupported`
   outcome `w1_tail_call_unsupported`, and the divergences
   `w1_assert_continue_divergence`, `w1_storageDead_returnPlace_class_divergence`
   (`.blocked` in `lean-miri`, undefined behavior in Anneal), and
   `w1_transmute_bool_divergence` (`.unsupported` transmutes in `lean-miri`).
2. Aggregates: `w2_array_index_returns` (safe `Index` and `ConstantIndex`, from
   entry), `w2_array_index_oob_ub`, `w2_padded_struct_returns`,
   `w2_enum_downcast_switch_returns`, `w2_union_init_prefix_returns` (a safe
   union write-then-read, from entry), `w2_union_init_prefix_lockstep`, and
   `w2_union_uninit_bytes_ub`.
3. Raw pointers: `w3_rawPtr_write_read_returns`, `w3_rawPtr_return` (a returned
   raw pointer), `w3_use_after_storageDead_ub`, `w3_arith_offset_returns` (a
   returned `arith_offset` pointer), and `w3_arith_offset_uninit_ub`.
4. Tree Borrows: `w4_child_write_then_parent_read_returns` (`I-10`),
   `w4_safe_ref_return` (a returned `&u64`), `w4_unsafe_cell_vs_freeze`
   (`I-11`), and `w4_protected_reservedFrz_conflict_ub`, the last two with the
   agreeing `lean-miri` Tree Borrows accesses (`TreeBorrowsRel`,
   `Tree.NormalTreeState.performAccess`), and the boundary witness
   `w4_disabled_read_divergence` (whole-program `lean-miri` runs do not check
   Tree Borrows permissions).
5. Multi-frame calls: `w5_call_return`, `w5_protector_release_returns`
   (`GlobalState.endCall` releasing a live protector on the way to an agreeing
   root return), `w5_callee_unreachable_ub`, and `w5_callee_uninit_return_ub`.
6. Intrinsics: `w6_assume_true`, `w6_assume_false_ub`, `w6_exact_div_valid`,
   `w6_exact_div_non_multiple_ub`, `w6_ctlz_returns`,
   `w6_saturating_add_returns`, `w6_rotate_left_unsupported_divergence`,
   `w6_write_bytes_returns`, `w6_write_bytes_lockstep`, `w6_write_bytes_oob_ub`,
   `w6_copy_nonoverlapping_disjoint_returns`,
   `w6_copy_nonoverlapping_disjoint_lockstep`, and
   `w6_copy_nonoverlapping_overlap_ub`.

`AgreeReturns` / `AgreeReturnsBits` (both machines `TreeSafe` / `System.Safe`
and returning the same value), `AgreeUB` (both reach undefined behavior and
neither is safe), and `AgreeReaches` (both run in lockstep to related states)
bundle the agreeing whole-program facts. Executions without memory allocation
are checked by kernel evaluation (`decide`, `decide +kernel`) of `runLoopFuel`
and `runAnnealBounded`; executions that allocate reuse the step-by-step traces
of the `LM-2` … `LM-4.2` witness modules through `MiriPath` / `AnnealPath`.
The `*_lockstep` witnesses reuse upstream bodies that never write `_0`; they
certify the lockstep segment (`AgreeReaches`) and state that Anneal's whole
program then faults at the root return.
-/

namespace LeanMiriSpec.Correspondence.MiriDiffWitnesses

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.Correspondence.Safety

/-! ## 0. Decidable observations and their whole-program meaning -/

/-- Scalar bits of an Anneal normal return of `sz` bytes. -/
def annealRetBits? (sz : Nat) : AnnealRunOutcome → Option Nat
  | .returned (.scalar ⟨b, sb⟩) _ => if sb == sz then some b else none
  | _ => none

/-- Whether an Anneal bounded run stopped with undefined behavior. -/
def annealIsUB : AnnealRunOutcome → Bool
  | .faulted .ub => true
  | _ => false

/-- Whether a `RunLoop` run stopped with an undefined-behavior report. -/
def miriIsUB (o : MiriRunLoopOutcome) : Bool :=
  match o.stoppedError? with
  | some e => Miri.Interpreter.RunLoop.reportsUB e
  | none => false

theorem anneal_returns_of_bits {body : CapturedMir} {N sz b : Nat} {s : MachineState}
    (h : annealRetBits? sz (runAnnealBounded body N s) = some b) :
    TreeSafe (mirTree body s) ∧
      ∃ tr mem, ReachesRet (mirTree body s) tr (.normal (.scalar ⟨b, sz⟩, mem)) := by
  generalize hr : runAnnealBounded body N s = o at h
  cases o with
  | returned v mem =>
    cases v with
    | scalar sc =>
      rcases sc with ⟨b', sb⟩
      simp only [annealRetBits?] at h
      split at h
      · next hsb =>
        injection h with h
        subst h
        have hsb' : sb = sz := by simpa using hsb
        subst hsb'
        obtain ⟨hsafe, ⟨tr, htr⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned hr
        exact ⟨hsafe, tr, mem, htr⟩
      · cases h
    | _ => simp [annealRetBits?] at h
  | _ => simp [annealRetBits?] at h

theorem anneal_ub_of_obs {body : CapturedMir} {N : Nat} {s : MachineState}
    (h : annealIsUB (runAnnealBounded body N s) = true) :
    MirReachesUB (mirTree body s) ∧ ¬ TreeSafe (mirTree body s) := by
  generalize hr : runAnnealBounded body N s = o at h
  cases o with
  | faulted k =>
    cases k with
    | ub =>
      obtain ⟨hns, hub⟩ := anneal_fault_of_runAnnealBounded_faulted hr
      exact ⟨hub rfl, hns⟩
    | _ => simp [annealIsUB] at h
  | _ => simp [annealIsUB] at h

theorem miri_returns_of_bits {H : AnnealMiriHooks} {N sz b : Nat} {m : AnnealStepState}
    (h : (runLoopFuel H N m).returnedOperand?.bind (operandScalarBits? sz) = some b) :
    (miriSystem H).Safe m ∧ (miriSystem H).PartialCorrect m (fun v => operandScalarBits? sz v = some b) ∧
      ∃ v, (miriSystem H).ReachesOutcome m (.returned v) ∧ operandScalarBits? sz v = some b := by
  rw [Option.bind_eq_some_iff] at h
  exact miri_returns_of_observation h

theorem miri_ub_of_obs {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    (h : miriIsUB (runLoopFuel H N m) = true) :
    (∃ e, (miriSystem H).ReachesOutcome m (.undefinedBehavior e)) ∧ ¬ (miriSystem H).Safe m := by
  unfold miriIsUB at h
  split at h
  · next e he =>
    obtain ⟨hr, hns⟩ := miri_ub_of_observation he h
    exact ⟨⟨e, hr⟩, hns⟩
  · cases h

/-- Both machines run `body` from `entryA` / `entryM` to a normal root return:
Anneal is `TreeSafe` and returns `retVal`; `lean-miri`'s `RunLoop` semantics is
`System.Safe`, reaches `.returned v`, and is partially correct only for `v`. -/
def AgreeReturns (body : CapturedMir) (H : AnnealMiriHooks) (entryA : MachineState)
    (entryM : AnnealStepState) (retVal : Value) (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  TreeSafe (mirTree body entryA) ∧
  (∃ tr mem, ReachesRet (mirTree body entryA) tr (.normal (retVal, mem))) ∧
  (miriSystem H).Safe entryM ∧
  (miriSystem H).ReachesOutcome entryM (.returned v) ∧
  (miriSystem H).PartialCorrect entryM (· = v)

/-- Both machines reach undefined behavior when running `body` from `entryA` / `entryM`. -/
def AgreeUB (body : CapturedMir) (H : AnnealMiriHooks) (entryA : MachineState)
    (entryM : AnnealStepState) : Prop :=
  MirReachesUB (mirTree body entryA) ∧ ¬ TreeSafe (mirTree body entryA) ∧
  (∃ e, (miriSystem H).ReachesOutcome entryM (.undefinedBehavior e)) ∧
  ¬ (miriSystem H).Safe entryM

theorem agreeReturns_of_paths {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {retVal : Value} {mem : Memory} {v : Miri.Interpreter.Operand AnnealProv}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAr : stepMirFn body sₙ = .retNormal retVal mem)
    (hM : MiriPath H preM mₙ) (hMr : H.coreStep () mₙ = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () mₙ).2 = .ok v) :
    AgreeReturns body H entryA entryM retVal v := by
  obtain ⟨⟨hts, ⟨tr, hrr⟩, _⟩, hsafe, hreach, huniq⟩ :=
    wholeProgram_returns hpa hpm hA hAr hM hMr hemp hop
  refine ⟨hts, ⟨tr, mem, hrr⟩, hsafe, hreach, fun v' hv' => ?_⟩
  have := huniq _ hv'
  injection this

theorem agreeUB_of_paths {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {e : Miri.Interpreter.StepError}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAf : stepMirFn body sₙ = .fail .ub)
    (hM : MiriPath H preM mₙ) (hMe : H.coreStep () mₙ = (m', .error e))
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    AgreeUB body H entryA entryM := by
  obtain ⟨⟨hub', hns⟩, hreach, hnsafe⟩ := wholeProgram_ub hpa hpm hA hAf hM hMe hub
  exact ⟨hub', hns, ⟨e, hreach⟩, hnsafe⟩

theorem agreeReturns_of_bits_path {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA : MachineState} {entryM mₙ m' : AnnealStepState} {N sz b : Nat}
    {v : Miri.Interpreter.Operand AnnealProv}
    (ha : annealRetBits? sz (runAnnealBounded body N entryA) = some b)
    (hM : MiriPath H entryM mₙ) (hMr : H.coreStep () mₙ = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () mₙ).2 = .ok v) :
    AgreeReturns body H entryA entryM (.scalar ⟨b, sz⟩) v := by
  obtain ⟨hts, hrr⟩ := anneal_returns_of_bits ha
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_path_return hM hMr hemp hop
  refine ⟨hts, hrr, hsafe, hreach, fun v' hv' => ?_⟩
  have := huniq _ hv'
  injection this

theorem agreeUB_of_obs_path {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA : MachineState} {entryM mₙ m' : AnnealStepState} {N : Nat}
    {e : Miri.Interpreter.StepError}
    (ha : annealIsUB (runAnnealBounded body N entryA) = true)
    (hM : MiriPath H entryM mₙ) (hMe : H.coreStep () mₙ = (m', .error e))
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    AgreeUB body H entryA entryM := by
  obtain ⟨hub', hns⟩ := anneal_ub_of_obs ha
  have h := miri_outcome_of_path_error hM hMe
  rw [classifyError_eq_ub_iff.2 ⟨hub, rfl⟩] at h
  exact ⟨hub', hns, ⟨e, h.1⟩, h.2⟩

/-- Both machines return the `sz`-byte scalar `b` when running `body` from
`entryA` / `entryM`: Anneal is `TreeSafe` and returns `b`; `lean-miri`'s
`RunLoop` semantics is `System.Safe`, reaches a return operand with scalar
bits `b`, and is partially correct for that postcondition. -/
def AgreeReturnsBits (body : CapturedMir) (H : AnnealMiriHooks) (entryA : MachineState)
    (entryM : AnnealStepState) (sz b : Nat) : Prop :=
  TreeSafe (mirTree body entryA) ∧
  (∃ tr mem, ReachesRet (mirTree body entryA) tr (.normal (.scalar ⟨b, sz⟩, mem))) ∧
  (miriSystem H).Safe entryM ∧
  (∃ v, (miriSystem H).ReachesOutcome entryM (.returned v) ∧ operandScalarBits? sz v = some b) ∧
  (miriSystem H).PartialCorrect entryM (fun v => operandScalarBits? sz v = some b)

/-- Both machines run `body` from `entryA` / `entryM` to the running states
`sA` / `mB` without stopping: a finite Anneal trace leads from `mirTree body
entryA` to the residual `mirTree body sA`, and `miriSystem` reaches `mB`. -/
def AgreeReaches (body : CapturedMir) (H : AnnealMiriHooks) (entryA sA : MachineState)
    (entryM mB : AnnealStepState) : Prop :=
  (∃ tr, Reaches (mirTree body entryA) tr (mirTree body sA)) ∧ (miriSystem H).Reaches entryM mB

theorem agreeReturnsBits_of_obs {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA : MachineState} {entryM : AnnealStepState} {N M sz b : Nat}
    (ha : annealRetBits? sz (runAnnealBounded body N entryA) = some b)
    (hm : (runLoopFuel H M entryM).returnedOperand?.bind (operandScalarBits? sz) = some b) :
    AgreeReturnsBits body H entryA entryM sz b := by
  obtain ⟨hts, hrr⟩ := anneal_returns_of_bits ha
  obtain ⟨hsafe, hpc, hreach⟩ := miri_returns_of_bits hm
  exact ⟨hts, hrr, hsafe, hreach, hpc⟩

theorem agreeUB_of_obs {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA : MachineState} {entryM : AnnealStepState} {N M : Nat}
    (ha : annealIsUB (runAnnealBounded body N entryA) = true)
    (hm : miriIsUB (runLoopFuel H M entryM) = true) : AgreeUB body H entryA entryM := by
  obtain ⟨hub, hns⟩ := anneal_ub_of_obs ha
  obtain ⟨hr, hnm⟩ := miri_ub_of_obs hm
  exact ⟨hub, hns, hr, hnm⟩

theorem agreeReaches_of_paths {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA sA : MachineState} {entryM mB : AnnealStepState}
    (hA : AnnealPath body entryA sA) (hM : MiriPath H entryM mB) :
    AgreeReaches body H entryA sA entryM mB :=
  ⟨reaches_cofix_of_coReach hA.coReach, hM.reaches⟩

/-! ## 1. Scalar arithmetic, casts, `SwitchInt`, `Assert`, and a diverging loop -/

def st (k : StatementKind) : Statement := { kind := k, span := "lm-4.3-witness" }
def tm (k : TerminatorKind) : Terminator := { kind := k, span := "lm-4.3-witness" }
def pl (i : Nat) : Place := { local_ := i, projection := [] }
def tyU8 : Ty := { kind := .uint .u8, layoutIdx := 0 }
def dcl (t : Ty) : LocalDecl := { mutability := .mut, ty := t, debugName := none }
def cU8 (n : Nat) : Operand := .constant { ty := tyU8, val := .scalar (.int ⟨n, 1⟩) }
def cBool (b : Bool) : Operand :=
  .constant { ty := { kind := .bool, layoutIdx := 0 }, val := .scalar (.int ⟨if b then 1 else 0, 1⟩) }
def blk (ss : List Statement) (t : TerminatorKind) : BasicBlockData :=
  { statements := ss, terminator := tm t, isCleanup := false }
def mkBody (name : String) (decls : List LocalDecl) (bbs : List BasicBlockData)
    (layouts : LayoutTable := emptyLayoutTable) : CapturedMir where
  defPath := name
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := decls
  basicBlocks := bbs
  fnAbi := Witness.fnAbi0
  layouts := layouts
  allocations := []

/-- `fn div() -> u8 { let x = 7; x / 7 }`: both machines return `1`. -/
theorem w1_div_returns :
    AgreeReturnsBits (Witness.divBody 7) (annealMiriHooks (Witness.divBody 7))
      (initMachineState (Witness.divBody 7) []) (miriEntryState (Witness.divBody 7)) 1 1 :=
  agreeReturnsBits_of_obs (N := 6) (M := 6) (by decide) (by decide)

/-- Division by zero is undefined behavior in both machines. -/
theorem w1_div_by_zero_ub :
    AgreeUB (Witness.divBody 0) (annealMiriHooks (Witness.divBody 0))
      (initMachineState (Witness.divBody 0) []) (miriEntryState (Witness.divBody 0)) :=
  agreeUB_of_obs (N := 6) (M := 6) (by decide) (by decide)

/-- `divBody d` is in the unconditional closed fragment for every divisor. -/
theorem w1_div_inFragment (d : Nat) (hd : d < 256) : InSafeScalarFragment (Witness.divBody d) :=
  ⟨WellTypedBody.toExt (Witness.wellTypedBody d hd), by simp [Witness.divBody]⟩

/-- The unconditional equivalence, for every divisor at once. -/
theorem w1_div_treeSafe_iff_miriSafe (d : Nat) (hd : d < 256) :
    TreeSafe (mirCallTree (Witness.divBody d) []) ↔
      (miriSystem (annealMiriHooks (Witness.divBody d))).Safe (miriEntryState (Witness.divBody d)) :=
  scalarFragment_treeSafe_iff_miriSafe (w1_div_inFragment d hd)

/-- `SwitchInt` takes case `7` (returning `20`) in both machines. -/
theorem w1_switch_case :
    AgreeReturnsBits (Witness.lm12SwitchBody 7) (annealMiriHooks (Witness.lm12SwitchBody 7))
      (initMachineState (Witness.lm12SwitchBody 7) []) (miriEntryState (Witness.lm12SwitchBody 7))
      1 20 :=
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by decide) (by decide)

/-- `SwitchInt` falls back to `otherwise` (returning `30`) in both machines. -/
theorem w1_switch_otherwise :
    AgreeReturnsBits (Witness.lm12SwitchBody 9) (annealMiriHooks (Witness.lm12SwitchBody 9))
      (initMachineState (Witness.lm12SwitchBody 9) []) (miriEntryState (Witness.lm12SwitchBody 9))
      1 30 :=
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by decide) (by decide)

/-- `lm12SwitchBody d` (a `SwitchInt` on `const d_u8` with cases `0`, `7`, and
`otherwise`) is in the unconditional closed fragment for every `d`. -/
theorem w1_switch_inFragment (d : Nat) (hd : d < 256) :
    InSafeScalarFragment (Witness.lm12SwitchBody d) := by
  have hu8 : IsPrimScalarTy Witness.u8Ty := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hc : ∀ n, n < 256 → WellTypedScalarOperandSyn (Witness.lm12SwitchBody d) (fun _ => True)
      (.constant (Witness.constU8 n)) Witness.u8Ty :=
    fun n hn => .constScalar _ ⟨n, 1⟩ rfl hu8 (Or.inl rfl)
      (by rw [scalarModulus_eq_two_pow]; simpa using hn) rfl (fun h => nomatch h)
      (fun h => nomatch h)
  have hret : ∀ k, k < 256 → WellTypedBasicBlockExt (Witness.lm12SwitchBody d) (fun _ => True)
      { statements := [Witness.mkStmt (.assign (Witness.local_ 0) (.use (.constant (Witness.constU8 k))))],
        terminator := Witness.mkTerm .return_, isCleanup := false } := by
    intro k hk
    refine ⟨rfl, fun stmt hstmt => ?_,
      .return_ Witness.u8Decl rfl trivial rfl (IsPrimScalarTy.size_ne_zero hu8)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
    subst hstmt
    exact .syn _ (.assign _ 0 Witness.u8Decl _ rfl rfl trivial (.use _ _ (hc k hk)))
  refine ⟨⟨(fun p h => nomatch h), fun bb hbb => ?_⟩, by simp [Witness.lm12SwitchBody]⟩
  simp only [Witness.lm12SwitchBody, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl | rfl
  · refine ⟨rfl, (fun stmt hstmt => nomatch hstmt), ?_⟩
    refine .switchInt _ _ Witness.u8Ty rfl (Or.inr (Or.inr ⟨.u8, rfl⟩)) (hc d hd) ?_
      ⟨_, rfl⟩ ?_
    · intro v b hmem
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by decide, fun h => nomatch h⟩
      · exact ⟨by decide, fun h => nomatch h⟩
    · intro v b hmem
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · exact hret 10 (by decide)
  · exact hret 20 (by decide)
  · exact hret 30 (by decide)

/-- The unconditional equivalence for `SwitchInt` branching, for every scrutinee. -/
theorem w1_switch_treeSafe_iff_miriSafe (d : Nat) (hd : d < 256) :
    TreeSafe (mirCallTree (Witness.lm12SwitchBody d) []) ↔
      (miriSystem (annealMiriHooks (Witness.lm12SwitchBody d))).Safe
        (miriEntryState (Witness.lm12SwitchBody d)) :=
  scalarFragment_treeSafe_iff_miriSafe (w1_switch_inFragment d hd)

/-- `-1_i8 as i16` sign-extends to `0xFFFF` in both machines. -/
theorem w1_cast_sign_extend :
    AgreeReturnsBits Witness.lm12CastBody (annealMiriHooks Witness.lm12CastBody)
      (initMachineState Witness.lm12CastBody []) (miriEntryState Witness.lm12CastBody) 2 0xFFFF :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by decide) (by decide)

/-- `lm12CastBody` (an `IntToInt` cast) is in the unconditional closed fragment. -/
theorem w1_cast_inFragment : InSafeScalarFragment Witness.lm12CastBody := by
  have hi8 : IsPrimScalarTy Witness.i8TyW := Or.inr (Or.inr (Or.inl ⟨.i8, rfl⟩))
  have hi16 : IsPrimScalarTy Witness.lm12I16Ty := Or.inr (Or.inr (Or.inl ⟨.i16, rfl⟩))
  refine ⟨⟨(fun p h => nomatch h), fun bb hbb => ?_⟩,
    by simp [Witness.lm12CastBody, Witness.lm12CastBodyOf]⟩
  simp only [Witness.lm12CastBody, Witness.lm12CastBodyOf, List.mem_singleton] at hbb
  subst hbb
  refine ⟨rfl, fun stmt hstmt => ?_,
    .return_ Witness.lm12I16Decl rfl trivial rfl (IsPrimScalarTy.size_ne_zero hi16)⟩
  simp only [List.mem_singleton] at hstmt
  subst hstmt
  exact .intToInt _ 0 Witness.lm12I16Decl _ Witness.i8TyW rfl rfl trivial
    (.constScalar _ ⟨0xFF, 1⟩ rfl hi8 (Or.inl rfl) (by rw [scalarModulus_eq_two_pow]; decide) rfl
      (fun h => nomatch h) (fun h => nomatch h))
    (Or.inr (Or.inl ⟨.i8, rfl⟩)) (Or.inl ⟨.i16, rfl⟩)

/-- The unconditional equivalence for the `IntToInt` cast body. -/
theorem w1_cast_treeSafe_iff_miriSafe :
    TreeSafe (mirCallTree Witness.lm12CastBody []) ↔
      (miriSystem (annealMiriHooks Witness.lm12CastBody)).Safe (miriEntryState Witness.lm12CastBody) :=
  scalarFragment_treeSafe_iff_miriSafe w1_cast_inFragment

/-- Checked addition guarded by an overflow `Assert` (`UnwindAction::Unreachable`):
```text
bb0: StorageLive(_1); _1 = AddWithOverflow(const 65500_u16, const rhs_u16);
     assert(copy (_1.1) == false) -> [success: bb1, unwind: unreachable]
bb1: _0 = copy (_1.0); StorageDead(_1); return
``` -/
def checkedAddBody (rhs : Nat) : CapturedMir :=
  mkBody "lm_4_3_witness::checked_add" [Witness.u16Decl, Witness.u16BoolDecl]
    [blk [st (.storageLive 1),
        st (.assign (pl 1) (.binaryOp .addWithOverflow (.constant (Witness.constU16 65500))
          (.constant (Witness.constU16 rhs))))]
      (.assert (.copy { local_ := 1, projection := [.field 1 Witness.boolTy] }) false 1 .unreachable),
     blk [st (.assign (pl 0) (.use (.copy { local_ := 1, projection := [.field 0 Witness.u16Ty] }))),
        st (.storageDead 1)] .return_]
    Witness.u16BoolLayoutTable

/-- Without overflow (`65500 + 35`), the assertion passes and both machines return `65535`. -/
theorem w1_checked_add_no_overflow :
    AgreeReturnsBits (checkedAddBody 35) (annealMiriHooks (checkedAddBody 35))
      (initMachineState (checkedAddBody 35) []) (miriEntryState (checkedAddBody 35)) 2 65535 :=
  agreeReturnsBits_of_obs (N := 7) (M := 7) (by decide) (by decide)

/-- On overflow (`65500 + 36`), the failed assertion with `unwind: unreachable`
is undefined behavior in both machines. -/
theorem w1_checked_add_overflow_ub :
    AgreeUB (checkedAddBody 36) (annealMiriHooks (checkedAddBody 36))
      (initMachineState (checkedAddBody 36) []) (miriEntryState (checkedAddBody 36)) :=
  agreeUB_of_obs (N := 7) (M := 7) (by decide) (by decide)

/-- A terminating conditional loop (`while i < 3 { i += 1 }`) in the
unconditional fragment: a `SwitchInt` on the `bool` comparison exits the loop.
```text
bb0: StorageLive(_1); StorageLive(_2); _1 = const 0_u8; goto bb1
bb1: _2 = Lt(copy _1, const 3_u8); switchInt(copy _2) -> [0: bb3, otherwise: bb2]
bb2: _1 = Add(copy _1, const 1_u8); goto bb1
bb3: _0 = copy _1; StorageDead(_2); StorageDead(_1); return
``` -/
def countLoopBody : CapturedMir :=
  mkBody "lm_4_3_witness::count_loop" [dcl tyU8, dcl tyU8, dcl Witness.boolTy]
    [blk [st (.storageLive 1), st (.storageLive 2), st (.assign (pl 1) (.use (cU8 0)))] (.goto 1),
     blk [st (.assign (pl 2) (.binaryOp .lt (.copy (pl 1)) (cU8 3)))]
       (.switchInt (.copy (pl 2)) { branches := [(0, 3)], otherwise := 2 }),
     blk [st (.assign (pl 1) (.binaryOp .add (.copy (pl 1)) (cU8 1)))] (.goto 1),
     blk [st (.assign (pl 0) (.use (.copy (pl 1)))), st (.storageDead 2), st (.storageDead 1)]
       .return_]

theorem countLoop_inFragment : InSafeScalarFragment countLoopBody := by
  have hu8 : IsPrimScalarTy tyU8 := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hbool : IsPrimScalarTy Witness.boolTy := Or.inl rfl
  have hu8int : IsIntegralTy tyU8 (translateUintTy .u8) := .uint .u8 rfl
  have hc : ∀ n, n < 256 → WellTypedScalarOperandSyn countLoopBody (fun _ => True) (cU8 n) tyU8 :=
    fun n hn => .constScalar _ ⟨n, 1⟩ rfl hu8 (Or.inl rfl)
      (by rw [scalarModulus_eq_two_pow]; simpa using hn) rfl (fun h => nomatch h)
      (fun h => nomatch h)
  have hcp1 : WellTypedScalarOperandSyn countLoopBody (fun _ => True) (.copy (pl 1)) tyU8 :=
    .copyLocal 1 (dcl tyU8) rfl (IsPrimScalarTy.size_ne_zero hu8) trivial
  refine ⟨⟨(fun p h => nomatch h), fun bb hbb => ?_⟩, by simp [countLoopBody, mkBody]⟩
  simp only [countLoopBody, mkBody, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl | rfl
  · refine ⟨rfl, fun stmt hstmt => ?_, .goto 1 _ rfl rfl⟩
    simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hstmt
    rcases hstmt with rfl | rfl | rfl
    · exact .syn _ (.storageLive _ 1 (dcl tyU8) rfl rfl trivial)
    · exact .syn _ (.storageLive _ 2 (dcl Witness.boolTy) rfl rfl trivial)
    · exact .syn _ (.assign _ 1 (dcl tyU8) _ rfl rfl trivial (.use _ _ (hc 0 (by decide))))
  · refine ⟨rfl, fun stmt hstmt => ?_, ?_⟩
    · simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hstmt
      subst hstmt
      exact .syn _ (.assign _ 2 (dcl Witness.boolTy) _ rfl rfl trivial
        (.binaryOp .lt _ _ tyU8 tyU8 Witness.boolTy hcp1 (hc 3 (by decide))
          (.intCmp .lt tyU8 tyU8 Witness.boolTy _ (Or.inr (Or.inr (Or.inl rfl))) hu8int hu8int rfl)))
    · refine .switchInt _ _ Witness.boolTy rfl (Or.inl rfl)
        (.copyLocal 2 (dcl Witness.boolTy) rfl (IsPrimScalarTy.size_ne_zero hbool) trivial)
        ?_ ⟨_, rfl⟩ ?_
      · intro v b hmem
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact ⟨by decide, fun _ => Or.inl rfl⟩
      · intro v b hmem
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact ⟨_, rfl⟩
  · refine ⟨rfl, fun stmt hstmt => ?_, .goto 1 _ rfl rfl⟩
    simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hstmt
    subst hstmt
    exact .syn _ (.assign _ 1 (dcl tyU8) _ rfl rfl trivial
      (.binaryOp .add _ _ tyU8 tyU8 tyU8 hcp1 (hc 1 (by decide))
        (.intArithOrBitwise .add tyU8 tyU8 tyU8 .u8 (Or.inl rfl) (.uint .u8 rfl) (.uint .u8 rfl)
          (.uint .u8 rfl))))
  · refine ⟨rfl, fun stmt hstmt => ?_,
      .return_ (dcl tyU8) rfl trivial rfl (IsPrimScalarTy.size_ne_zero hu8)⟩
    simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hstmt
    rcases hstmt with rfl | rfl | rfl
    · exact .syn _ (.assign _ 0 (dcl tyU8) _ rfl rfl trivial (.use _ _ hcp1))
    · exact .syn _ (.storageDead _ 2 (dcl Witness.boolTy) rfl rfl (by decide) trivial)
    · exact .syn _ (.storageDead _ 1 (dcl tyU8) rfl rfl (by decide) trivial)

/-- **Conditional loop.** Both machines run the `SwitchInt`-guarded loop three
times and return `3`; by the unconditional fragment, every reachable
`lean-miri` outcome is a return or undefined behavior and safety coincides. -/
theorem w1_count_loop_returns :
    AgreeReturnsBits countLoopBody (annealMiriHooks countLoopBody)
      (initMachineState countLoopBody []) (miriEntryState countLoopBody) 1 3 ∧
    (TreeSafe (mirCallTree countLoopBody []) ↔
      (miriSystem (annealMiriHooks countLoopBody)).Safe (miriEntryState countLoopBody)) ∧
    (∀ o, (miriSystem (annealMiriHooks countLoopBody)).ReachesOutcome
      (miriEntryState countLoopBody) o → o.isReturn ∨ ∃ e, o = .undefinedBehavior e) :=
  ⟨agreeReturnsBits_of_obs (N := 24) (M := 24) (by decide) (by decide),
    scalarFragment_treeSafe_iff_miriSafe countLoop_inFragment,
    scalarFragment_outcomes countLoop_inFragment⟩

/-- `StorageDead(_0); return`: `lean-miri` (as rustc) rejects `StorageDead` of the
return place with the non-UB `StackError.cannotMakeReturnPlaceDead`, a
`.blocked` outcome, while Anneal kills `_0` and its root return is undefined
behavior. Neither machine is safe, but their failure classes differ
(`annealStepHooks_storageDead_returnPlace`), which is why the fragments
exclude `StorageDead(_0)`. -/
def storageDeadZeroBody : CapturedMir :=
  mkBody "lm_4_3_witness::storage_dead_return_place" [dcl tyU8] [blk [st (.storageDead 0)] .return_]

theorem w1_storageDead_returnPlace_class_divergence :
    (miriSystem (annealMiriHooks storageDeadZeroBody)).ReachesOutcome
      (miriEntryState storageDeadZeroBody) (.blocked (.stack .cannotMakeReturnPlaceDead)) ∧
    ¬ (miriSystem (annealMiriHooks storageDeadZeroBody)).Safe (miriEntryState storageDeadZeroBody) ∧
    MirReachesUB (mirCallTree storageDeadZeroBody []) ∧
    ¬ TreeSafe (mirCallTree storageDeadZeroBody []) := by
  have h : runLoopFuel (annealMiriHooks storageDeadZeroBody) 1 (miriEntryState storageDeadZeroBody) =
      .stopped (miriEntryState storageDeadZeroBody) (.stack .cannotMakeReturnPlaceDead) := rfl
  have hm := miri_outcome_of_runLoopFuel_stopped h
  exact ⟨hm.1, hm.2, anneal_ub_of_obs (body := storageDeadZeroBody) (N := 3)
    (s := initMachineState storageDeadZeroBody []) (by decide)⟩

/-- An unresolvable tail call (`bb0: tailcall const 0_u8()`) is unsupported in
both machines: Anneal fails with `FailureKind.unsupported` and `lean-miri`
reaches an `.unsupported` outcome, so the failure classes agree
(`FaultAgrees`) outside the fragments. -/
def tailCallBody : CapturedMir :=
  mkBody "lm_4_3_witness::tail_call" [dcl tyU8] [blk [] (.tailCall (cU8 0) [])]

theorem w1_tail_call_unsupported :
    (∃ e, (miriSystem (annealMiriHooks tailCallBody)).ReachesOutcome
      (miriEntryState tailCallBody) (.unsupported e)) ∧
    ¬ (miriSystem (annealMiriHooks tailCallBody)).Safe (miriEntryState tailCallBody) ∧
    MirReachesFault (mirCallTree tailCallBody []) .unsupported ∧
    ¬ TreeSafe (mirCallTree tailCallBody []) := by
  have ha : runAnnealBounded tailCallBody 1 (initMachineState tailCallBody []) =
      .faulted .unsupported := rfl
  obtain ⟨e, he⟩ : ∃ e, runLoopFuel (annealMiriHooks tailCallBody) 1 (miriEntryState tailCallBody) =
      .stopped (miriEntryState tailCallBody) e ∧ isUnsupportedError e = true ∧
      Miri.Interpreter.RunLoop.reportsUB e = false :=
    ⟨_, rfl, rfl, rfl⟩
  have hm := miri_outcome_of_runLoopFuel_stopped he.1
  have hc : classifyError e = .unsupported e := by
    unfold classifyError; rw [he.2.2, he.2.1]; rfl
  rw [hc] at hm
  exact ⟨⟨e, hm.1⟩, hm.2, anneal_reachesFault_of_runAnnealBounded_faulted ha,
    (anneal_fault_of_runAnnealBounded_faulted ha).1⟩

/-- `_0 = const b_u8 as bool (Transmute); return`. -/
def transmuteBoolBody (b : Nat) : CapturedMir where
  defPath := "lm_4_3_witness::transmute_bool"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [{ mutability := .mut, ty := { kind := .bool, layoutIdx := 0 }, debugName := none }]
  basicBlocks := [
    { statements := [
        { kind := .assign ⟨0, .nil⟩
            (.cast .transmute
              (.constant { ty := { kind := .uint .u8, layoutIdx := 0 }, val := .scalar (.int ⟨b, 1⟩) })
              { kind := .bool, layoutIdx := 0 })
          span := "lm-4.3-witness" }]
      terminator := { kind := .return_, span := "lm-4.3-witness" }
      isCleanup := false }]
  fnAbi := { args := [], ret := { layout := Witness.lm24U8Layout, mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := emptyLayoutTable
  allocations := []

/-- Whole-program certificate from a decidable observation of an unsupported stop. -/
theorem miri_unsupported_of_obs {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    (h : ((runLoopFuel H N m).stoppedError?.map fun e =>
          !Miri.Interpreter.RunLoop.reportsUB e && isUnsupportedError e) = some true) :
    (∃ e, (miriSystem H).ReachesOutcome m (.unsupported e)) ∧ ¬ (miriSystem H).Safe m := by
  cases hs : (runLoopFuel H N m).stoppedError? with
  | none => rw [hs] at h; cases h
  | some e =>
    rw [hs] at h
    dsimp only [Option.map] at h
    injection h with h
    have ⟨hnub, hunsup⟩ : (!Miri.Interpreter.RunLoop.reportsUB e) = true ∧
        isUnsupportedError e = true := Bool.and_eq_true_iff.1 h
    have hub_f : Miri.Interpreter.RunLoop.reportsUB e = false := by
      revert hnub; cases Miri.Interpreter.RunLoop.reportsUB e <;> decide
    obtain ⟨m', hm'⟩ := MiriRunLoopOutcome.stoppedError?_spec hs
    have hout := miri_outcome_of_runLoopFuel_stopped hm'
    rw [classifyError_eq_unsupported_iff.2 ⟨hub_f, hunsup, rfl⟩] at hout
    exact ⟨⟨e, hout.1⟩, hout.2⟩

/-- **Divergence witness** (`CastKind.transmute`, `_0 = const b_u8 as bool
(Transmute)`): `annealCastHooks` fails closed on transmutes.
1. For `b = 1` (`pass_bool_transmute_valid`), Anneal is `TreeSafe` and returns
   `true`, whereas `miriSystem` reaches `.unsupported` (not `Safe`).
2. For `b = 2` (`ub_transmute_invalid_bool`), Anneal reaches undefined behavior,
   whereas `miriSystem` reaches `.unsupported`: a failure-class divergence. -/
theorem w1_transmute_bool_divergence :
    (TreeSafe (mirCallTree (transmuteBoolBody 1) []) ∧
      (∃ tr mem, ReachesRet (mirCallTree (transmuteBoolBody 1) []) tr (.normal (.scalar ⟨1, 1⟩, mem))) ∧
      (∃ e, (miriSystem (annealMiriHooks (transmuteBoolBody 1))).ReachesOutcome
        (miriEntryState (transmuteBoolBody 1)) (.unsupported e)) ∧
      ¬ (miriSystem (annealMiriHooks (transmuteBoolBody 1))).Safe
        (miriEntryState (transmuteBoolBody 1))) ∧
    (MirReachesUB (mirCallTree (transmuteBoolBody 2) []) ∧
      (∃ e, (miriSystem (annealMiriHooks (transmuteBoolBody 2))).ReachesOutcome
        (miriEntryState (transmuteBoolBody 2)) (.unsupported e)) ∧
      ¬ (miriSystem (annealMiriHooks (transmuteBoolBody 2))).Safe
        (miriEntryState (transmuteBoolBody 2))) := by
  have ha1 := anneal_returns_of_bits (body := transmuteBoolBody 1) (N := 3)
    (s := initMachineState (transmuteBoolBody 1) []) (sz := 1) (b := 1) (by decide)
  have hm1 := miri_unsupported_of_obs (H := annealMiriHooks (transmuteBoolBody 1)) (N := 1)
    (m := miriEntryState (transmuteBoolBody 1)) (by decide +kernel)
  have ha2 := anneal_ub_of_obs (body := transmuteBoolBody 2) (N := 2)
    (s := initMachineState (transmuteBoolBody 2) []) (by decide)
  have hm2 := miri_unsupported_of_obs (H := annealMiriHooks (transmuteBoolBody 2)) (N := 1)
    (m := miriEntryState (transmuteBoolBody 2)) (by decide +kernel)
  exact ⟨⟨ha1.1, ha1.2, hm1.1, hm1.2⟩, ⟨ha2.1, hm2.1, hm2.2⟩⟩

/-- A diverging safe loop in the unconditional fragment:
```text
bb0: StorageLive(_1); _1 = const 7_u8; _0 = Add(copy _1, const 1_u8);
     StorageDead(_1); goto bb1
bb1: goto bb0
``` -/
def loopBody : CapturedMir :=
  mkBody "lm_4_3_witness::spin" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1), st (.assign (pl 1) (.use (cU8 7))),
        st (.assign (pl 0) (.binaryOp .add (.copy (pl 1)) (cU8 1))), st (.storageDead 1)]
      (.goto 1),
     blk [] (.goto 0)]

/-- Anneal's state at the head of the loop after one full iteration. -/
def loopHead : MachineState :=
  match runAnnealBounded loopBody 6 (initMachineState loopBody []) with
  | .running s => s
  | _ => initMachineState loopBody []

theorem loop_prefix : runAnnealBounded loopBody 6 (initMachineState loopBody []) = .running loopHead :=
  rfl

theorem loop_cycle : runAnnealBounded loopBody (5 + 1) loopHead = .running loopHead := rfl

theorem loop_wellTyped : WellTypedBody loopBody := by
  refine ⟨(fun p h => nomatch h), fun bb hbb => ?_⟩
  have hu8 : IsPrimScalarTy tyU8 := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hc : ∀ n, n < 256 → WellTypedScalarOperandSyn loopBody (fun _ => True) (cU8 n) tyU8 :=
    fun n hn => .constScalar _ ⟨n, 1⟩ rfl hu8 (Or.inl rfl)
      (by rw [scalarModulus_eq_two_pow]; simpa using hn) rfl (fun h => nomatch h)
      (fun h => nomatch h)
  simp only [loopBody, mkBody, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · refine ⟨rfl, fun stmt hstmt => ?_, Or.inl ⟨1, _, rfl, rfl⟩⟩
    simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hstmt
    rcases hstmt with rfl | rfl | rfl | rfl
    · exact .storageLive _ 1 (dcl tyU8) rfl rfl trivial
    · exact .assign _ 1 (dcl tyU8) _ rfl rfl trivial (.use _ _ (hc 7 (by decide)))
    · exact .assign _ 0 (dcl tyU8) _ rfl rfl trivial
        (.binaryOp .add _ _ tyU8 tyU8 tyU8 (.copyLocal 1 (dcl tyU8) rfl (by decide) trivial)
          (hc 1 (by decide))
          (.intArithOrBitwise .add tyU8 tyU8 tyU8 .u8 (Or.inl rfl) (.uint .u8 rfl) (.uint .u8 rfl)
            (.uint .u8 rfl)))
    · exact .storageDead _ 1 (dcl tyU8) rfl rfl (by decide) trivial
  · exact ⟨rfl, (fun stmt hstmt => nomatch hstmt), Or.inl ⟨0, _, rfl, rfl⟩⟩

theorem loop_inFragment : InSafeScalarFragment loopBody :=
  ⟨WellTypedBody.toExt loop_wellTyped, by simp [loopBody, mkBody]⟩

/-- **Diverging safe loop.** Anneal never stops and is `TreeSafe` and never
returns; `lean-miri`'s `RunLoop` semantics has an `InfiniteRun`, is
`System.Safe`, and reaches no terminal outcome. -/
theorem w1_loop_diverges_safely :
    Miri.OperationalSafety.InfiniteRun (miriSystem (annealMiriHooks loopBody))
      (miriEntryState loopBody) ∧
    (miriSystem (annealMiriHooks loopBody)).Safe (miriEntryState loopBody) ∧
    (∀ o, ¬ (miriSystem (annealMiriHooks loopBody)).ReachesOutcome (miriEntryState loopBody) o) ∧
    TreeSafe (mirCallTree loopBody []) ∧
    (∀ tr r, ¬ ReachesRet (mirCallTree loopBody []) tr r) := by
  have hforever := anneal_forall_running_of_lasso loop_prefix loop_cycle
  obtain ⟨hinf, hsafe, hno⟩ := miri_infiniteRun_of_anneal_forever
    (scalarFragmentExt_stepClosedSim loop_inFragment.wellTyped) (scalarFragment_entry loop_inFragment)
    hforever
  exact ⟨hinf, hsafe, hno, anneal_safe_of_forall_running hforever⟩

/-- **Divergence witness** (`Assert` with `UnwindAction::Continue`): a failing
assertion makes Anneal panic (`MirOutcome.panic`, a defined outcome, so the tree
is `TreeSafe`), whereas `annealTerminatorHooks.assertPanic` reports undefined
behavior, so `lean-miri`'s semantics is not `System.Safe`. This is why the
closed fragments exclude unwinding `Assert`s.
```text
bb0: assert(const false == true) -> [success: bb1, unwind: continue]
bb1: return
``` -/
def assertContinueBody : CapturedMir :=
  mkBody "lm_4_3_witness::assert_continue" [dcl tyU8]
    [blk [] (.assert (cBool false) true 1 .continue_), blk [] .return_]

theorem w1_assert_continue_divergence :
    TreeSafe (mirCallTree assertContinueBody []) ∧
    (∃ e, (miriSystem (annealMiriHooks assertContinueBody)).ReachesOutcome
      (miriEntryState assertContinueBody) (.undefinedBehavior e)) ∧
    ¬ (miriSystem (annealMiriHooks assertContinueBody)).Safe (miriEntryState assertContinueBody) := by
  have hm := miri_ub_of_obs (H := annealMiriHooks assertContinueBody) (N := 2)
    (m := miriEntryState assertContinueBody) (by decide)
  refine ⟨?_, hm.1, hm.2⟩
  have hs : stepMirFn assertContinueBody (initMachineState assertContinueBody []) =
      .retOutcome .panic := rfl
  rw [mirCallTree, mirTree_eq_cofix, treeSafe_cofix_iff]
  intro y hy hf
  cases hy with
  | refl _ =>
    change IsFaultNode (stepMirFn assertContinueBody (initMachineState assertContinueBody [])) at hf
    rw [hs] at hf
    obtain ⟨_, _, h, _⟩ := hf
    cases h
  | head h _ =>
    cases h with
    | tau h =>
      change stepMirFn assertContinueBody (initMachineState assertContinueBody []) = _ at h
      rw [hs] at h; cases h
    | vis h _ _ =>
      change stepMirFn assertContinueBody (initMachineState assertContinueBody []) = _ at h
      rw [hs] at h; cases h

/-! ## 6. Intrinsics -/

/-- `bb0: assume(const b); _0 = const 7_u8; return`. -/
def assumeBody (b : Bool) : CapturedMir :=
  mkBody "lm_4_3_witness::assume" [dcl tyU8]
    [blk [st (.intrinsic (.assume (cBool b))), st (.assign (pl 0) (.use (cU8 7)))] .return_]

/-- `assume(true)` is a no-op: both machines return `7`. -/
theorem w6_assume_true :
    AgreeReturnsBits (assumeBody true) (annealMiriHooks (assumeBody true))
      (initMachineState (assumeBody true) []) (miriEntryState (assumeBody true)) 1 7 :=
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by decide) (by decide)

/-- `assume(false)` is undefined behavior in both machines. -/
theorem w6_assume_false_ub :
    AgreeUB (assumeBody false) (annealMiriHooks (assumeBody false))
      (initMachineState (assumeBody false) []) (miriEntryState (assumeBody false)) :=
  agreeUB_of_obs (N := 4) (M := 4) (by decide) (by decide)

/-- `exact_div::<u32>(a, 7)` (`bb0: _0 = exact_div(const a, const 7) -> bb1; bb1: return`). -/
def exactDivBody (a : Nat) : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::exact_div" WitnessLM4_2.u32K
    (WitnessLM4_2.binArgs WitnessLM4_2.u32K a 7 4) WitnessLM4_2.u32K

/-- `exact_div(42, 7)` (`pass_exact_div_valid`) returns `6` in both machines. -/
theorem w6_exact_div_valid :
    AgreeReturnsBits (exactDivBody 42) (annealMiriHooks (exactDivBody 42))
      (initMachineState (exactDivBody 42) []) (miriEntryState (exactDivBody 42)) 4 6 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by decide +kernel) (by decide +kernel)

/-- `exact_div(43, 7)` (`ub_exact_div_non_multiple`) is undefined behavior in both machines. -/
theorem w6_exact_div_non_multiple_ub :
    AgreeUB (exactDivBody 43) (annealMiriHooks (exactDivBody 43))
      (initMachineState (exactDivBody 43) []) (miriEntryState (exactDivBody 43)) :=
  agreeUB_of_obs (N := 3) (M := 3) (by decide +kernel) (by decide +kernel)

/-- `ctlz::<u32>(1)` returns `31` in both machines. -/
def ctlzBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::ctlz" WitnessLM4_2.u32K
    (WitnessLM4_2.bitArgs WitnessLM4_2.u32K 1 4) WitnessLM4_2.u32K

theorem w6_ctlz_returns :
    AgreeReturnsBits ctlzBody (annealMiriHooks ctlzBody) (initMachineState ctlzBody [])
      (miriEntryState ctlzBody) 4 31 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by decide +kernel) (by decide +kernel)

/-- `saturating_add::<u8>(250, 10)` saturates to `255` in both machines. -/
def saturatingAddBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::saturating_add" WitnessLM4_2.u8K
    (WitnessLM4_2.binArgs WitnessLM4_2.u8K 250 10 1) WitnessLM4_2.u8K

theorem w6_saturating_add_returns :
    AgreeReturnsBits saturatingAddBody (annealMiriHooks saturatingAddBody)
      (initMachineState saturatingAddBody []) (miriEntryState saturatingAddBody) 1 255 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by decide +kernel) (by decide +kernel)

/-- **Divergence witness** (`rotate_left`): `rotate_left::<u32>(0x80000001, 1)`
returns `3` in Anneal (`TreeSafe`), while `lean-miri`'s pinned dispatcher
leaves `rotate_left` to its MIR fallback body and the step fails closed with an
`.unsupported` outcome (`WitnessLM4_2.wit_lm4_2_rotate_left_divergence`). -/
def rotateLeftBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::rotate_left" WitnessLM4_2.u32K
    (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K

theorem w6_rotate_left_unsupported_divergence :
    TreeSafe (mirCallTree rotateLeftBody []) ∧
    (∃ tr mem, ReachesRet (mirCallTree rotateLeftBody []) tr (.normal (.scalar ⟨3, 4⟩, mem))) ∧
    (∃ msg, (miriSystem (annealMiriHooks rotateLeftBody)).ReachesOutcome
      (miriEntryState rotateLeftBody) (.unsupported (.unsupported msg))) ∧
    ¬ (miriSystem (annealMiriHooks rotateLeftBody)).Safe (miriEntryState rotateLeftBody) := by
  obtain ⟨hts, hrr⟩ := anneal_returns_of_bits (body := rotateLeftBody) (N := 3)
    (s := initMachineState rotateLeftBody []) (sz := 4) (b := 3) (by decide +kernel)
  obtain ⟨_, m', msg, herr⟩ := WitnessLM4_2.wit_lm4_2_rotate_left_divergence
  have heq : miriEntryState rotateLeftBody =
      WitnessLM4_2.callMiriPre "core::intrinsics::rotate_left" WitnessLM4_2.u32K
        (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K := rfl
  have hout := miri_outcome_of_path_error (H := annealMiriHooks rotateLeftBody)
    (.refl (miriEntryState rotateLeftBody)) (by rw [heq]; exact herr)
  exact ⟨hts, hrr, ⟨msg, hout.1⟩, hout.2⟩

/-! ## 3. Raw pointers -/

theorem lm31AddrOf_prefix_anneal : runAnnealBounded Witness.lm31AddrOfBody 3
    (initMachineState Witness.lm31AddrOfBody []) = .running Witness.lm31AddrOfAnnealPre := rfl

theorem lm31AddrOf_prefix_miri : runLoopFuel (annealMiriHooks Witness.lm31AddrOfBody) 3
    (miriEntryState Witness.lm31AddrOfBody) = .running Witness.lm31AddrOfMiriPre := rfl

/-- `&raw mut` + `*ptr` write and read (`lm31AddrOfBody`):
```text
bb0: StorageLive(_1); StorageLive(_2); _1 = const 42_u64; _2 = &raw mut _1;
     (*_2) = const 99_u64; _0 = copy (*_2); StorageDead(_2); StorageDead(_1); return
```
Both machines run from their entry states to a normal return of `99_u64`. -/
theorem w3_rawPtr_write_read_returns :
    AgreeReturns Witness.lm31AddrOfBody (annealMiriHooks Witness.lm31AddrOfBody)
      (initMachineState Witness.lm31AddrOfBody []) (miriEntryState Witness.lm31AddrOfBody)
      (.scalar ⟨99, 8⟩) (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))) := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, _, _, hs₁, hm₁, hs₂, hm₂, _, hs₃, hm₃,
    hs₄, hm₄, hs₅, hm₅, _, _, hret, hmret, _, hop⟩ := Witness.wit_lm3_1_end_to_end_return_real_steps
  exact agreeReturns_of_paths lm31AddrOf_prefix_anneal lm31AddrOf_prefix_miri
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
      (.step .silent hs₅ (.refl _)))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hm₅)
        (.step hm₅ (frames_ne_of_step_ok_true hmret) (.refl _))))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₅).2 = _; rw [hop])

theorem lm31Dangling_prefix_anneal : runAnnealBounded Witness.lm31DanglingBody 3
    (initMachineState Witness.lm31DanglingBody []) = .running Witness.lm31DanglingAnnealPre := rfl

theorem lm31Dangling_prefix_miri : runLoopFuel (annealMiriHooks Witness.lm31DanglingBody) 3
    (miriEntryState Witness.lm31DanglingBody) = .running Witness.lm31DanglingMiriPre := rfl

/-- Dangling raw pointer after `StorageDead` (use-after-free, `lm31DanglingBody`):
```text
bb0: StorageLive(_1); StorageLive(_2); _1 = const 42_u64; _2 = &raw const _1;
     StorageDead(_1); _0 = copy (*_2); return
```
Both machines reach undefined behavior from their entry states. -/
theorem w3_use_after_storageDead_ub :
    AgreeUB Witness.lm31DanglingBody (annealMiriHooks Witness.lm31DanglingBody)
      (initMachineState Witness.lm31DanglingBody []) (miriEntryState Witness.lm31DanglingBody) := by
  obtain ⟨s₁, s₂, m₁, m₂, m₃, msg, hs₁, hm₁, _, hs₂, hm₂, hrel₂, _, hfail, herr⟩ :=
    Witness.wit_lm3_1_use_after_storageDead_real_steps
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact agreeUB_of_paths lm31Dangling_prefix_anneal lm31Dangling_prefix_miri
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hfail
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _)))
    herr rfl

/-- `_0 = &raw mut _1; return` (`ptr4Body`): both machines return the raw pointer
to `_1` from the pre-state (`step_terminator_return_rawPtr_lm3_1_simulation`),
with `ImmediateRelLM3_1`-related return values. -/
def rawPtrReturnBody : CapturedMir :=
  WitnessLM4_2.ptr4Body WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    .return_

theorem w3_rawPtr_return :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns rawPtrReturnBody (annealMiriHooks rawPtrReturnBody)
        (WitnessLM4_2.ptr4AnnealPre rawPtrReturnBody)
        (WitnessLM4_2.ptr4MiriPre rawPtrReturnBody WitnessLM4_2.rawMutU64K)
        (.ptr { allocId := 1, offsetBytes := 0 } 8) (.immediate imm0) ∧
      get? rawPtrReturnBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_1
        [rawPtrAllocMapEntry rawPtrReturnBody.localDecls rawPtrReturnBody.layouts .mut 1 1
          Witness.lm31AllocId1]
        decl0.ty rawPtrReturnBody.layouts (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0 := by
  let b := rawPtrReturnBody
  have hrel₀ : StateRel b (WitnessLM4_2.ptr4AnnealPre b)
      (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K) :=
    WitnessLM4_2.ptr4_stateRel WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
      WitnessLM4_2.rawMutU64K
      [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
        (.rawPtr .mut (WitnessLM4_2.local42 1)))] .return_
  have himm₀ : ∀ tf, (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨WitnessLM4_2.ptr4_all_immediate b _ tf htf 0, WitnessLM4_2.ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := WitnessLM4_2.mkPtrState b 0 1
    [.init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init (.scalar ⟨42, 8⟩), .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (WitnessLM4_2.ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ (fun _ h => nomatch h) rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (WitnessLM4_2.ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 0 :=
    fun tf₁ htf₁ => himm₁_step _ tf₁ rfl htf₁ 0 (by decide)
      (WitnessLM4_2.ptr4_all_immediate b _ _ rfl 0)
  have hret : stepMirFn b s₁ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₁.memory :=
    rfl
  have hsim₂ := step_terminator_return_rawPtr_lm3_1_simulation hrel₁ (fun _ h => nomatch h)
    rfl rfl rfl rfl rfl rfl rfl himm₁
  rw [hret] at hsim₂
  obtain ⟨decl0, imm0, hdecl0, hop, himm, hmret⟩ := hsim₂.retNormal_rel
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.refl _)) hret
    (.step hm₁ (frames_ne_of_step_ok_true hmret) (.refl _))
    hmret rfl (by change (annealControlHooks.returnOperand () m₁).2 = _; rw [hop])

/-- `arith_offset(copy _2, 1)` with `_2` uninitialized. -/
def arithOffsetUninitBody : CapturedMir :=
  WitnessLM4_2.ptr4Body WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K []
    (WitnessLM4_2.arithOffsetTerm 2 1)

/-- `arith_offset` on an uninitialized pointer is undefined behavior in both machines. -/
theorem w3_arith_offset_uninit_ub :
    AgreeUB arithOffsetUninitBody (annealMiriHooks arithOffsetUninitBody)
      (WitnessLM4_2.ptr4AnnealPre arithOffsetUninitBody)
      (WitnessLM4_2.ptr4MiriPre arithOffsetUninitBody WitnessLM4_2.rawMutU64K) := by
  obtain ⟨hfail, m', msg, herr⟩ := WitnessLM4_2.wit_lm4_2_arith_offset_uninit_ub
  exact agreeUB_of_paths (p := 0) rfl rfl (.refl _) hfail (.refl _) herr rfl

/-! ## 4. Tree Borrows -/

/-- `I-10` child write then parent read through a two-level reborrow
(`tb_child_write_then_parent_read`, `lm32ReborrowTreeBody`):
```text
bb0: _2 = &mut _1; _3 = &mut (*_2); (*_3) = const 99_u64; _0 = copy (*_2); return
```
From the entry state with `_1 = 42_u64`, both machines run to a normal return of
`99_u64` (with `ImmediateRelLM3_2`-related return values), tracking the
`Reserved → Unique` activation and child freeze in the Tree Borrows hierarchy. -/
theorem w4_child_write_then_parent_read_returns :
    ∃ imm0 decl0,
      AgreeReturns Witness.lm32ReborrowTreeBody (annealMiriHooks Witness.lm32ReborrowTreeBody)
        (Witness.mkPre4AnnealLM32 Witness.lm32ReborrowTreeBody (.init (.scalar ⟨42, 8⟩)))
        (Witness.mkPre4MiriLM32 Witness.lm32ReborrowTreeBody Witness.u64Ty Witness.lm32Mls42)
        (.scalar ⟨99, 8⟩) (.immediate imm0) ∧
      get? Witness.lm32ReborrowTreeBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_2
        ([Witness.lm32TreeChild .frozen, Witness.lm32TreeRoot .active].map
          ReborrowMapEntry.toAllocMapEntry)
        decl0.ty Witness.lm32ReborrowTreeBody.layouts (.scalar ⟨99, 8⟩) imm0 := by
  obtain ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, _, hs₃, hm₃, _,
    _, hs₄, hm₄, _, _, hret, hmret, hdecl0, hop, himm⟩ :=
    Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps
  refine ⟨imm0, decl0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hmret)
        (.refl _)))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₄).2 = _; rw [hop])

/-- A safe reference `&u64` returned from the root frame (`LM-3.2`,
`wit_lm3_2_placeMention_and_unified_return_ref_real_steps`):
```text
bb0: _2 = &mut _1; PlaceMention(_2); PlaceMention(*_2); *_2 = const 55_u64;
     _0 = move _2; return
```
Both machines run from the pre-state to a normal return of the reference
(`ImmediateRelLM3_2`-related to the `Active` reborrow of `_1`). -/
theorem w4_safe_ref_return :
    ∃ (b : CapturedMir) (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns b (annealMiriHooks b) (Witness.mkPre4AnnealLM32 b .uninit)
        (Witness.mkPre4MiriLM32 b Witness.refU64Ty
          { value := .live (.immediate .uninit), layout := none })
        (.ptr { allocId := 1, offsetBytes := 0 } 8) (.immediate imm0) ∧
      get? b.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_2
        [{ refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 Witness.lm31AllocId1 with
            perm := .active }]
        decl0.ty b.layouts (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0 := by
  obtain ⟨b, s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, decl0, imm0, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃,
    hs₄, hm₄, hs₅, hm₅, _, _, hret, hmret, hdecl0, hop, himm⟩ :=
    Witness.wit_lm3_2_placeMention_and_unified_return_ref_real_steps.1
  refine ⟨b, decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
      (.step .silent hs₅ (.refl _)))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hm₅)
        (.step hm₅ (frames_ne_of_step_ok_true hmret) (.refl _))))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₅).2 = _; rw [hop])


/-- `runMiriBoundedLM2_2` returns transfer to `RunLoop` returns. -/
theorem runLoopFuel_of_runMiriBoundedLM2_2 {body : CapturedMir} {n : Nat} {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv}
    (h : runMiriBoundedLM2_2 body n m = .returned m' (.ok v)) :
    runLoopFuel (rootHooks (Miri.Interpreter.Step.step
      (annealStepHooksLM2_2 body.localDecls body.layouts))) n m = .returned m' v := by
  induction n generalizing m with
  | zero => cases h
  | succ n ih =>
    rw [runLoopFuel_succ, miriIter_eq]
    simp only [rootHooks]
    rcases hc : Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m with
      ⟨m₁, (e | (_ | _))⟩
    · simp only [runMiriBoundedLM2_2, hc] at h; cases h
    · simp only [runMiriBoundedLM2_2, hc] at h; cases h
    · simp only [runMiriBoundedLM2_2, hc] at h
      simp only [stepToIteration]
      cases hemp : m₁.stack.frames.isEmpty
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hemp, ↓reduceIte] at h ⊢
        injection h with h₁ h₂
        simp only [h₁, h₂, popOutcome]

theorem miriOutcomeScalarBits_spec {sz b : Nat} {o : MiriRunOutcome}
    (h : Witness.miriOutcomeScalarBits sz o = some b) :
    ∃ m' v, o = .returned m' (.ok v) ∧ operandScalarBits? sz v = some b := by
  unfold Witness.miriOutcomeScalarBits at h
  split at h
  · next m' s =>
    refine ⟨m', .immediate (.scalar s), rfl, ?_⟩
    split at h
    · exact h
    · cases h
  · cases h

/-! ## 2. Aggregates: arrays, padded structs, multi-variant enums, unions -/

/-- `LM-2.3` enum pipeline (`lm23Body`): `_1 = Lm23Enum::V1(42_u32)`,
`_2 = discriminant(_1)`, `SwitchInt(_2)`, a `Downcast` field read, and arithmetic,
returning `99_u64`. From block `0` both machines run to the return. -/
theorem w2_enum_downcast_switch_returns :
    ∃ imm0,
      AgreeReturns Witness.lm23Body (.ofHooks Witness.lm23Hooks annealControlHooks)
        (Witness.lm23InitAnneal 0) (Witness.lm23InitMiri 0) (.scalar ⟨99, 8⟩) (.immediate imm0) ∧
      ImmediateRel Witness.lm23U64Ty Witness.lm23Layouts (.scalar ⟨99, 8⟩) imm0 := by
  obtain ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, imm0, hm₁, _, _, hm₂, _, hm₃, _, hm₄, _, hm₅, _, _,
    hm₆, _, hm₇, _, hm₈, hop, himm, hemp⟩ := Witness.wit_lm2_3_full_pipeline_trace
  refine ⟨imm0, agreeReturns_of_bits_path (N := 9) (sz := 8) (b := 99) (by decide)
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hm₅)
        (.step hm₅ (frames_ne_of_step_ok_true hm₆) (.step hm₆ (frames_ne_of_step_ok_true hm₇)
          (.step hm₇ (frames_ne_of_step_ok_true hm₈) (.refl _))))))))
    hm₈ hemp (by change (annealControlHooks.returnOperand () m₇).2 = _; rw [hop]), himm⟩

/-- `LM-2.2` padded struct (`lm22PaddedBody`): writing the fields of a struct
with inter-field padding and reading back `99_u32` agree from the entry state. -/
theorem w2_padded_struct_returns :
    ∃ v, AgreeReturns Witness.lm22PaddedBody
        (rootHooks (Miri.Interpreter.Step.step
          (annealStepHooksLM2_2 Witness.lm22PaddedBody.localDecls Witness.lm22PaddedBody.layouts)))
        (initMachineState Witness.lm22PaddedBody []) Witness.lm22PaddedMiriInit (.scalar ⟨99, 4⟩) v ∧
      operandScalarBits? 4 v = some 99 := by
  obtain ⟨_, _, ha, hm⟩ := Witness.lm22Padded_full_trace_and_returns_agree
  obtain ⟨m', v, hrun, hbits⟩ := miriOutcomeScalarBits_spec hm
  have hloop := runLoopFuel_of_runMiriBoundedLM2_2 hrun
  obtain ⟨hts, hrr⟩ := anneal_returns_of_bits (body := Witness.lm22PaddedBody) (N := 9)
    (s := initMachineState Witness.lm22PaddedBody []) (b := 99) (sz := 4) ha
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_runLoopFuel_returned hloop
  refine ⟨v, ⟨hts, hrr, hsafe, hreach, fun v' hv' => ?_⟩, hbits⟩
  have := huniq _ hv'
  injection this

/-- `runMiriBounded` returns transfer to `RunLoop` returns of `annealMiriHooks`. -/
theorem runLoopFuel_of_runMiriBounded {body : CapturedMir} {n : Nat} {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv}
    (h : runMiriBounded body n m = .returned m' (.ok v)) :
    runLoopFuel (annealMiriHooks body) n m = .returned m' v := by
  induction n generalizing m with
  | zero => cases h
  | succ n ih =>
    rw [runLoopFuel_succ, miriIter_eq]
    simp only [annealMiriHooks, AnnealMiriHooks.ofHooks]
    rcases hc : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m with
      ⟨m₁, (e | (_ | _))⟩
    · simp only [runMiriBounded, hc] at h; cases h
    · simp only [runMiriBounded, hc] at h; cases h
    · simp only [runMiriBounded, hc] at h
      simp only [stepToIteration]
      cases hemp : m₁.stack.frames.isEmpty
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hemp, ↓reduceIte] at h ⊢
        injection h with h₁ h₂
        simp only [h₁, h₂, popOutcome]

/-- `LM-2.1` arrays (`pass_array_index_and_mutation`, `lm21FullFnBody`): from the
entry state, `[i32; 3]`, `[bool; 2]`, and `[char; 2]` locals with
`ConstantIndex` writes and reads, a safe `Index` read `_5 = copy _1[_4]`, a
`ConstantIndex` move, and `25 + (-3)` run to a normal return of `22_i32` in
both machines. -/
theorem w2_array_index_returns :
    AgreeReturns Witness.lm21FullFnBody (annealMiriHooks Witness.lm21FullFnBody)
      (initMachineState Witness.lm21FullFnBody []) (miriEntryState Witness.lm21FullFnBody)
      (.scalar ⟨22, 4⟩)
      (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 22)))) := by
  obtain ⟨mem', m', _, ha, hm, _⟩ := Witness.lm21_signed_bool_char_runBounded_return
  have hentry : miriEntryState Witness.lm21FullFnBody = Witness.lm21FullFnInitMiri := rfl
  have hloop := runLoopFuel_of_runMiriBounded hm
  rw [← hentry] at hloop
  obtain ⟨hts, ⟨tr, hrr⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned ha
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_runLoopFuel_returned hloop
  refine ⟨hts, ⟨tr, mem', hrr⟩, hsafe, hreach, fun v' hv' => ?_⟩
  have := huniq _ hv'
  injection this

/-- `LM-2.1` array `Index` out of bounds (`_2 = 3_usize` on `[u16; 3]`):
both machines reach undefined behavior from the state before the read. -/
theorem w2_array_index_oob_ub :
    AgreeUB Witness.lm21Body (annealMiriHooks Witness.lm21Body)
      (Witness.lm21ArrAnneal 4 (.init (.scalar ⟨3, 8⟩)))
      (Witness.lm21ArrMiri 4 (.scalar (.fromScalarInt Witness.lm21Usize3))) := by
  obtain ⟨hfail, m', msg, herr⟩ := Witness.lm21_index_oob_ub
  exact agreeUB_of_paths (p := 0) rfl rfl (.refl _) hfail (.refl _) herr rfl

/-- `LM-2.4` union (`I-11` initialized prefix): after `_1 = U { a: 5_u8 }` and
`_4 = copy _1`, reading the larger field `_4.1 : u32` touches uninitialized
bytes and is undefined behavior in both machines. -/
theorem w2_union_uninit_bytes_ub :
    AgreeUB Witness.lm24Body
      (.ofHooks (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts)
        annealControlHooks)
      (Witness.lm24InitAnneal 2) (Witness.lm24InitMiri 2) := by
  obtain ⟨m₁, m₂, m₃, msg, hm₁, _, hm₂, hrel₂, _, herr⟩ := Witness.lm24_copy_larger_field_ub
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact agreeUB_of_obs_path (N := 3) (by decide)
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _)))
    herr rfl

/-- `LM-2.4` union initialized prefix (`I-11`, block `1` of `lm24Body`):
`_1 = U { a: 5_u8 }` and `_2 = copy (_1.0: u8)` step both machines in lockstep to
`StateRelLM2_4`-related states with `_2 = 5_u8`: reading the initialized prefix
is defined in both machines (contrast `w2_union_uninit_bytes_ub`). This is a
lockstep segment on a reused block that never writes its `_0 : u32`, so
Anneal's whole program faults at the root return (last conjunct); the safe
whole program is `w2_union_init_prefix_returns`. -/
theorem w2_union_init_prefix_lockstep :
    ∃ m₂,
      AgreeReaches Witness.lm24Body
        (.ofHooks (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts)
          annealControlHooks)
        (Witness.lm24InitAnneal 1) Witness.lm24Bb1S2 (Witness.lm24InitMiri 1) m₂ ∧
      StateRelLM2_4 Witness.lm24Body Witness.lm24Bb1S2 m₂ ∧
      get? Witness.lm24Bb1S2.frame.locals 2 = some (.init (.scalar ⟨5, 1⟩)) ∧
      MirReachesUB (mirTree Witness.lm24Body (Witness.lm24InitAnneal 1)) := by
  obtain ⟨m₁, m₂, hm₁, _, hm₂, hrel₂, hget⟩ := Witness.lm24_write_read_same_field_steps
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact ⟨m₂, agreeReaches_of_paths
    (.step .silent Witness.lm24_bb1_anneal₁ (.step .silent Witness.lm24_bb1_anneal₂ (.refl _)))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))),
    hrel₂, hget, (anneal_ub_of_obs (body := Witness.lm24Body) (N := 4)
      (s := Witness.lm24InitAnneal 1) (by decide)).1⟩

/-- Whole-program safe union witness body (`pass_uninit_union_write_then_read`):
`bb0: _1 = U { a: 5_u8 }; _0 = copy (_1.0: u8); return` (`_0 : u8`, `_1 : union U { a: u8, b: u32 }`). -/
def unionRetBody : CapturedMir where
  defPath := "lm_4_3_witness::union_init_prefix_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.lm24Decl Witness.lm24U8Ty, Witness.lm24Decl Witness.lm24UTy]
  basicBlocks := [
    { statements := [
        Witness.lm24AggStmt 1 5,
        { kind := .assign ⟨0, .nil⟩ (.use (unionFieldReadOperand false 1 0 Witness.lm24U8Ty))
          span := "lm-4.3-witness" }]
      terminator := { kind := .return_, span := "lm-4.3-witness" }
      isCleanup := false }]
  fnAbi := { args := [], ret := { layout := Witness.lm24U8Layout, mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := Witness.lm24Layouts
  allocations := []

def unionRetInitAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := (initMachineState unionRetBody []).memory }

def unionRetInitMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody unionRetBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none
      (translateTy Witness.lm24U8Ty Witness.lm24Layouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def unionRetInitMiri : AnnealStepState :=
  { stack := ⟨#[unionRetInitMiriFrame]⟩, machine := AnnealMachine.empty }

theorem unionRet_init_stateRel : StateRel unionRetBody unionRetInitAnneal unionRetInitMiri := by
  refine StateRel.mk unionRetInitMiriFrame rfl rfl
    ⟨translateTy Witness.lm24U8Ty Witness.lm24Layouts, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      match i with | 0 | 1 | _ + 2 => simp [unionRetInitMiriFrame] at hi)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 =>
    have hs : slot = .uninit := by simpa [unionRetInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [unionRetInitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 2 => simp [unionRetBody, get?] at hdecl

theorem unionRet_init_imm (j : Nat) :
    ∀ tf, unionRetInitMiri.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
  intro tf h mls hmls mp hv
  have htf : unionRetInitMiriFrame = tf := by simpa [unionRetInitMiri] using h
  subst htf
  match j with
  | 0 | 1 => simp [unionRetInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 2 => simp [unionRetInitMiriFrame] at hmls

/-- **Whole-program `AgreeReturns` safe union witness**: `_1 = U { a: 5_u8 };
_0 = copy (_1.0: u8); return` runs from `StateRel`-related pre-states through
`annealStepHooksLM2_4` to an agreeing root return of `5_u8` (`ImmediateRel`) while
`_1` holds the partially initialized union (`IsUnionPrefixMask 4 1`). -/
theorem w2_union_init_prefix_returns :
    ∃ imm0,
      AgreeReturns unionRetBody
        (.ofHooks (annealStepHooksLM2_4 unionRetBody.localDecls unionRetBody.layouts)
          annealControlHooks)
        unionRetInitAnneal unionRetInitMiri (.scalar ⟨5, 1⟩) (.immediate imm0) ∧
      ImmediateRel Witness.lm24U8Ty Witness.lm24Layouts (.scalar ⟨5, 1⟩) imm0 := by
  let b := unionRetBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hc5 : ∀ tf, WellTypedScalarOperand b tf (.constant (Witness.lm24ConstU8 5)) Witness.lm24U8Ty :=
    fun tf => .constScalar (Witness.lm24ConstU8 5) ⟨5, 1⟩ rfl Witness.lm24_isPrim_u8 (Or.inl rfl)
      (by decide) rfl (fun h => nomatch h) (fun h => nomatch h)
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1,
                 locals := [.uninit, .init (.aggregate 0 [.scalar ⟨5, 1⟩])] }
      memory := (initMachineState b []).memory }
  let s₂ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2,
                 locals := [.init (.scalar ⟨5, 1⟩), .init (.aggregate 0 [.scalar ⟨5, 1⟩])] }
      memory := (initMachineState b []).memory }
  have hs₁ : stepMirFn b unionRetInitAnneal = .step s₁ := rfl
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hs₃ : stepMirFn b s₂ = .retNormal (.scalar ⟨5, 1⟩) s₂.memory := rfl
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation unionRet_init_stateRel.toLM2_4
    List.Pairwise.nil MemoryHighWater.empty.canReserveAllocId hphase
    (u := 1) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl rfl rfl
    (unionRet_init_imm 1) Witness.lm24_isPrim_u8 (fun tf _ => hc5 tf) (by decide)
  obtain ⟨sc, mp, m₁, tf₁, hm₁, hop_val, hstate₁, hu_slot₁, hframes₁, ⟨c₁, hmls_u₁⟩,
    hmem₁, hnodup₁, himm₁, _, _, _, hhw₁⟩ := hpost₁ s₁ hs₁
  have hsc : sc = ⟨5, 1⟩ := by injection hop_val with h _; injection h with h; exact h.symm
  subst hsc
  obtain ⟨hhw₁', hnext₁⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  have hu_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₁] at htf; have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls_u₁⟩
  have hr_imm₁ : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf htf; rw [hframes₁] at htf; have h : tf₁ = tf := by simpa using htf
    subst h; exact himm₁ _ rfl 0 (by decide) (unionRet_init_imm 0 _ rfl)
  obtain ⟨hrel₂, _, hmach₂⟩ := (step_union_field_read_simulation hstate₁ hnodup₁ hphase
    (r := 0) (u := 1) (j := 0) (fty := Witness.lm24U8Ty) (isMove := false)
    rfl rfl rfl rfl rfl Witness.lm24_isPrim_u8 (Or.inl rfl) rfl Witness.lm24_wt_U rfl (by decide)
    hu_slot₁ hu_mls₁ hmem₁ hr_imm₁).1 rfl rfl
  rw [hs₂] at hrel₂
  generalize hm₂_eq : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 b.localDecls b.layouts) () m₁ = mRes₂ at hrel₂ hmach₂
  cases hrel₂ with
  | step _ m₂ hstate₂ =>
    dsimp only at hmach₂
    have himm₂_0 : ∀ tf₂, m₂.stack.frames = #[tf₂] → IsImmediateFrameLocal tf₂ 0 := by
      intro tf₂ htf₂ mls₀ hmls₀ mp₀ hmp₀
      rcases hstate₂ with ⟨tf₂', htf₂', _, _, hfr₂, _, _, _, _, _, hdisj₂⟩
      rw [htf₂] at htf₂'; have h := Array.singleton_inj.1 htf₂'; subst h
      obtain ⟨sl₀, ml₀, _, _, hs₀, hm₀, _, hul₀⟩ :=
        hfr₂.lookup_local (i := 0) (decl := Witness.lm24Decl Witness.lm24U8Ty) rfl
      obtain ⟨sl₁, ml₁, _, _, hs₁, hm₁_l, _, hul₁⟩ :=
        hfr₂.lookup_local (i := 1) (decl := Witness.lm24Decl Witness.lm24UTy) rfl
      have hsl₁ : sl₁ = .init (.aggregate 0 [.scalar ⟨5, 1⟩]) := Option.some.inj hs₁.symm
      subst hsl₁
      rw [hmls₀] at hm₀; injection hm₀ with hm₀; subst hm₀
      rcases mls₀ with ⟨v₀, lay₀⟩; dsimp only at hmp₀; subst hmp₀
      have hc_init : unionRetInitMiri.machine.memory.nextAllocId.toNat = 1 := rfl
      dsimp only at hhw₁' hnext₁
      have hid_eq1 : ∀ (id : Miri.Memory.AllocId) la,
          (id, la) ∈ m₂.machine.memory.live.toList → id.value.toNat = 1 := by
        intro id la hmem
        rw [hmach₂] at hmem
        have hlt := hhw₁'.live_lt (id, la) (Array.mem_def.2 hmem)
        dsimp only at hlt
        have hpos : 0 < id.value.toNat :=
          Nat.pos_of_ne_zero fun h => id.nonzero (UInt64.toNat_inj.mp h)
        omega
      have hid₀ : ∃ id₀ : Miri.Memory.AllocId,
          mp₀.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id₀ ∧
          id₀.value.toNat = 1 := by
        cases hul₀ with
        | union _ _ _ _ _ _ _ hm =>
          rcases hm with ⟨id₀, _, _, la₀, _, hp₀, _, _, hlive₀, _⟩
          exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
        | base _ _ hl₀ =>
          cases hl₀ with
          | indirect _ _ _ _ _ hm =>
            rcases hm with ⟨id₀, _, _, _, la₀, hp₀, _, _, hlive₀, _⟩
            exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
      have hid₁ : ∃ (mp₁ : Miri.Interpreter.MemPlace AnnealProv)
          (lay₁ : Option Miri.Interpreter.LocalLayout) (id₁ : Miri.Memory.AllocId),
          tf₂.locals[1]? = some ⟨.live (.indirect mp₁), lay₁⟩ ∧
          mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id₁ ∧
          id₁.value.toNat = 1 := by
        cases hul₁ with
        | union _ _ _ mp₁ lay₁ _ _ hm =>
          rcases hm with ⟨id₁, _, _, la₁, _, hp₁, _, _, hlive₁, _⟩
          exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
        | base _ _ hl₁ =>
          cases hl₁ with
          | immediate _ _ _ _ hval =>
            rcases hval with ⟨h, _⟩ | ⟨v, hv, himm⟩
            · cases h
            · injection hv with hv; subst hv; cases himm
          | indirect _ mp₁ lay₁ _ _ hm =>
            rcases hm with ⟨id₁, _, _, _, la₁, hp₁, _, _, hlive₁, _⟩
            exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
      obtain ⟨id₀, hp₀, hv₀⟩ := hid₀
      obtain ⟨mp₁, lay₁, id₁, hm₁', hp₁, hv₁⟩ := hid₁
      have heq_id : id₀ = id₁ := by
        rcases id₀ with ⟨x₀, nz₀⟩; rcases id₁ with ⟨x₁, nz₁⟩
        have : x₀ = x₁ := UInt64.toNat_inj.mp (hv₀.trans hv₁.symm)
        subst this; rfl
      exact hdisj₂ 0 1 mp₀ mp₁ lay₀ lay₁ (by decide) hmls₀ hm₁' (by rw [hp₀, hp₁, heq_id])
    have hsim₃ := step_terminator_return_lm2_4_simulation hstate₂ hphase rfl rfl rfl rfl rfl
      (decl0 := Witness.lm24Decl Witness.lm24U8Ty) rfl (by decide) himm₂_0
    rw [hs₃] at hsim₃
    generalize hm₃_eq : Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 b.localDecls b.layouts) () m₂ = mRes₃ at hsim₃
    cases hsim₃ with
    | retRoot decl0 _ imm0 _ m₃ hdecl0 hop0 himm0 hm₃ =>
      subst hm₃
      have hd0 : decl0 = Witness.lm24Decl Witness.lm24U8Ty := Option.some.inj hdecl0.symm
      subst hd0
      refine ⟨imm0, ?_, himm0⟩
      exact agreeReturns_of_paths (p := 0) rfl rfl
        (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hs₃
        (.step hm₁ (frames_ne_of_step_ok_true hm₂_eq)
          (.step hm₂_eq (frames_ne_of_step_ok_true hm₃_eq) (.refl _)))
        hm₃_eq rfl (by change (annealControlHooks.returnOperand () m₂).2 = _; rw [hop0])

/-! ## 6. Intrinsics (memory) -/

/-- `CopyNonOverlapping` with overlapping source and destination
(`ub_copy_nonoverlapping_overlap`) is undefined behavior in both machines. -/
theorem w6_copy_nonoverlapping_overlap_ub :
    AgreeUB (WitnessLM4_2.copySingleMutBody 1) (annealMiriHooks (WitnessLM4_2.copySingleMutBody 1))
      (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.copySingleMutBody 1))
      (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.copySingleMutBody 1) WitnessLM4_2.unitK) := by
  obtain ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hfail, herr⟩ :=
    WitnessLM4_2.wit_lm4_2_copy_nonoverlapping_overlap_ub
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  exact agreeUB_of_paths (p := 0) rfl rfl (.step .silent hs₁ (.refl _)) hfail
    (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _)) herr rfl


/-- Valid `CopyNonOverlapping` between disjoint allocations
(`pass_copy_nonoverlapping_disjoint_locals`, `copyDistinctBody`): both machines
take the reborrow and copy steps in lockstep to `StateRelLM3_1`-related states,
and the destination `_2` holds `42_u64` in both (Anneal's local and
`lean-miri`'s allocation bytes). A lockstep segment: the reused body never
writes `_0`, so Anneal's whole program faults at the root return (last
conjunct). -/
theorem w6_copy_nonoverlapping_disjoint_lockstep :
    ∃ s₃ m₃,
      AgreeReaches WitnessLM4_2.copyDistinctBody (annealMiriHooks WitnessLM4_2.copyDistinctBody)
        (WitnessLM4_2.copy6AnnealPre WitnessLM4_2.copyDistinctBody true) s₃
        (WitnessLM4_2.copy6MiriPre WitnessLM4_2.copyDistinctBody true) m₃ ∧
      get? s₃.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩)) ∧
      (∃ la msc,
        m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
          some (Witness.lm31AllocId2, la) ∧
        ScalarRel ⟨42, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc)) ∧
      MirReachesUB (mirTree WitnessLM4_2.copyDistinctBody
        (WitnessLM4_2.copy6AnnealPre WitnessLM4_2.copyDistinctBody true)) := by
  obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, _, hs₂, hm₂, _, hs₃, hm₃, hrel₃, hget, hmem⟩ :=
    WitnessLM4_2.wit_lm4_2_copy_nonoverlapping_ok
  obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
  exact ⟨s₃, m₃, agreeReaches_of_paths
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.refl _))))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_eq_singleton htf₃) (.refl _)))),
    hget, hmem, (anneal_ub_of_obs (body := WitnessLM4_2.copyDistinctBody) (N := 5)
      (s := WitnessLM4_2.copy6AnnealPre WitnessLM4_2.copyDistinctBody true) (by decide)).1⟩

/-- `write_bytes::<u64>(ptr, 0xAB, 1)` (`LM-4.2`, `writeBytesMutBody 0xAB 1`): both
machines take the reborrow and the intrinsic call in lockstep to
`StateRelLM3_1`-related states, with `_1 = 0xABABABABABABABAB`. A lockstep
segment: Anneal's call leaves its `()` destination `_0` uninitialized, so
Anneal's whole program faults at the root return (last conjunct), while a
zero-sized root return is certified only for the `LM-4.1` interpreter. -/
theorem w6_write_bytes_lockstep :
    ∃ s₂ m₂,
      AgreeReaches (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 1))
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1)) s₂
        (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 1) WitnessLM4_2.unitK) m₂ ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) ∧
      MirReachesUB (mirTree (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1))) := by
  obtain ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, _, hs₂, hm₂, hrel₂, hget⟩ :=
    WitnessLM4_2.wit_lm4_2_write_bytes_ok
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact ⟨s₂, m₂, agreeReaches_of_paths (.step .silent hs₁ (.step .silent hs₂ (.refl _)))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))),
    hget, (anneal_ub_of_obs (body := WitnessLM4_2.writeBytesMutBody 0xAB 1) (N := 4)
      (s := WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1)) (by decide)).1⟩

/-- `write_bytes::<u64>(ptr, 0xAB, 2)` past the end of `_1` (`ub_write_bytes_oob`)
is undefined behavior in both machines. -/
theorem w6_write_bytes_oob_ub :
    AgreeUB (WitnessLM4_2.writeBytesMutBody 0xAB 2)
      (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 2))
      (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 2))
      (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 2) WitnessLM4_2.unitK) := by
  obtain ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hfail, herr⟩ := WitnessLM4_2.wit_lm4_2_write_bytes_oob_ub
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  exact agreeUB_of_paths (p := 0) rfl rfl (.step .silent hs₁ (.refl _)) hfail
    (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _)) herr rfl

/-- **Tree Borrows boundary witness** (`LM-3.2`,
`step_safeRef_deref_read_disabled_divergence`): in
`_2 = &mut _1; _1 = 77_u64; _0 = copy *_2` the direct write to `_1` disables the
reborrow `_2`, so Anneal's read through `_2` is undefined behavior, while
`lean-miri`'s run, whose memory accesses run no borrow-tracker hooks
(`annealMemoryCopyHooks_access_ok`), performs the read and continues with
`_0 = 77`. -/
theorem w4_disabled_read_divergence :
    ∃ (b : CapturedMir) (m₃ : AnnealStepState) (msc : Miri.Memory.ScalarInt)
      (tf₃ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      MirReachesUB (mirTree b (Witness.mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))) ∧
      ¬ TreeSafe (mirTree b (Witness.mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))) ∧
      (miriSystem (annealMiriHooks b)).Reaches
        (Witness.mkPre4MiriLM32 b Witness.u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy Witness.u64Ty) }) m₃ ∧
      ScalarRel ⟨77, 8⟩ msc ∧ m₃.stack.frames = #[tf₃] ∧
      (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) := by
  obtain ⟨b, s₁, s₂, m₁, m₂, m₃, tf₃, msc, hs₁, hm₁, hs₂, hm₂, _, hfail, hsc, hm₃, htf₃, hv⟩ :=
    Witness.wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps.2.2.2
  have hA := anneal_fault_of_path (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hfail
  exact ⟨b, m₃, msc, tf₃, hA.2 rfl, hA.1,
    (MiriPath.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_eq_singleton htf₃) (.refl _)))).reaches,
    hsc, htf₃, hv⟩

/-- `I-11` (`pass_tb_unsafe_cell_shared_mutation`): through `&UnsafeCell<u32>`
(a `Cell` tag), a foreign write through an unrelated raw pointer leaves the
shared reborrow usable and Anneal's whole program returns `7_u32`; through `&u32`
(a `Frozen` tag) the same foreign write disables the reborrow and the child read
is undefined behavior. At every step of both executions `lean-miri`'s Tree
Borrows tree (`basedNormalTree` of Anneal's borrow table) agrees through
`TreeBorrowsRel`: the foreign write is a `Completed` access in both trees, and
the child read is `Completed` under `Cell` but the transition error
`ChildAccessForbidden Disabled` under `Frozen`
(`WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps`). The agreement is
at the level of Tree Borrows accesses: `bodyD` uses `emptyLayoutTable`, under
which `lean-miri`'s layout of `UnsafeCell<u32>` is zero-sized, and
`lean-miri`'s whole-program runs do not check Tree Borrows permissions
(`w4_disabled_read_divergence`). -/
theorem w4_unsafe_cell_vs_freeze :
    ((TreeSafe (mirTree (WitnessLM3_3.bodyD SimLM3_3.unsafeCellU32T) WitnessLM3_3.initD) ∧
      ∃ tr mem, ReachesRet (mirTree (WitnessLM3_3.bodyD SimLM3_3.unsafeCellU32T) WitnessLM3_3.initD)
        tr (.normal (.scalar ⟨7, 4⟩, mem))) ∧
     ∃ s₂ s₃ : MachineState,
      AnnealPath (WitnessLM3_3.bodyD SimLM3_3.unsafeCellU32T) WitnessLM3_3.initD s₂ ∧
      stepMirFn (WitnessLM3_3.bodyD SimLM3_3.unsafeCellU32T) s₂ = .step s₃ ∧
      s₂.memory.borrows = [SimLM3_3.entry 2 .unique, SimLM3_3.entry 1 .cell] ∧
      s₃.memory.borrows = [SimLM3_3.entry 2 .unique, SimLM3_3.entry 1 .cell] ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status = .Completed) ∧
    ((MirReachesUB (mirTree (WitnessLM3_3.bodyD SimLM3_3.u32T) WitnessLM3_3.initD) ∧
      ¬ TreeSafe (mirTree (WitnessLM3_3.bodyD SimLM3_3.u32T) WitnessLM3_3.initD)) ∧
     ∃ s₂ s₃ : MachineState,
      AnnealPath (WitnessLM3_3.bodyD SimLM3_3.u32T) WitnessLM3_3.initD s₂ ∧
      stepMirFn (WitnessLM3_3.bodyD SimLM3_3.u32T) s₂ = .step s₃ ∧
      stepMirFn (WitnessLM3_3.bodyD SimLM3_3.u32T) s₃ = .fail .ub ∧
      s₂.memory.borrows = [SimLM3_3.entry 2 .unique, SimLM3_3.entry 1 .frozen] ∧
      s₃.memory.borrows = [SimLM3_3.entry 2 .unique, SimLM3_3.entry 1 .disabled] ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden .Disabled)) := by
  obtain ⟨⟨c₁, c₂, c₃, c₄, hc₁, _, hc₂, hcb₂, hc₃, hcb₃, hc₄, _, hcw, hcrel, hcr⟩,
    ⟨f₁, f₂, f₃, hf₁, _, hf₂, hfb₂, hf₃, hfb₃, hfail, hfw, hfrel, hfr⟩⟩ :=
    WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps
  refine ⟨⟨anneal_returns_of_bits (body := WitnessLM3_3.bodyD SimLM3_3.unsafeCellU32T) (N := 6)
      (s := WitnessLM3_3.initD) (sz := 4) (b := 7) (by decide),
      c₂, c₃, .step .silent hc₁ (.step .silent hc₂ (.refl _)), hc₃, hcb₂, hcb₃,
      hcw, hcrel, hcr⟩,
    ⟨anneal_ub_of_obs (body := WitnessLM3_3.bodyD SimLM3_3.u32T) (N := 6) (s := WitnessLM3_3.initD)
      (by decide),
      f₂, f₃, .step .silent hf₁ (.step .silent hf₂ (.refl _)), hf₃, hfail, hfb₂, hfb₃,
      hfw, hfrel, hfr⟩⟩

/-- Protected `ReservedFrz` conflict (`LM-3.3`): after a function-entry retag
protects a `ReservedFrz` child (`activeProtectors = [1]`), a foreign read sets
its `conflicted` latch and the protected child write is undefined behavior for
Anneal's whole program. `lean-miri`'s Tree Borrows tree agrees through
`TreeBorrowsRel`: the foreign read is a `Completed` access, and the write from
the protected node is the transition error `ChildAccessForbidden (ReservedFrz
true)` (`WitnessLM3_3.wit_lm3_3_protected_conflict_ub_real_steps`). -/
theorem w4_protected_reservedFrz_conflict_ub :
    (MirReachesUB (mirTree WitnessLM3_3.bodyB WitnessLM3_3.initBC) ∧
      ¬ TreeSafe (mirTree WitnessLM3_3.bodyB WitnessLM3_3.initBC)) ∧
    ∃ s₂ s₃ s₄ : MachineState,
      AnnealPath WitnessLM3_3.bodyB WitnessLM3_3.initBC s₂ ∧
      stepMirFn WitnessLM3_3.bodyB s₂ = .step s₃ ∧ stepMirFn WitnessLM3_3.bodyB s₃ = .step s₄ ∧
      stepMirFn WitnessLM3_3.bodyB s₄ = .fail .ub ∧
      s₂.memory.activeProtectors = [1] ∧
      s₄.memory.borrows =
        [SimLM3_3.entry 3 .frozen, SimLM3_3.entry 2 (.reservedFrz true) (some 1) (some 1),
          SimLM3_3.entry 1 .reserved] ∧
      TreeBorrowsRel s₃.memory.borrows [1] (basedNormalTree s₃.memory.borrows [1]) ∧
      ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows [1]
        ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree.performAccess 1 .Write
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden (.ReservedFrz true)) := by
  obtain ⟨s₁, s₂, s₃, s₄, h₁, _, h₂, _, hprot, _, h₃, _, h₄, hb₄, _, hfail, hrel₃, hread, hrel₄,
    hwrite⟩ := WitnessLM3_3.wit_lm3_3_protected_conflict_ub_real_steps
  exact ⟨anneal_ub_of_obs (body := WitnessLM3_3.bodyB) (N := 6) (s := WitnessLM3_3.initBC)
      (by decide),
    s₂, s₃, s₄, .step .silent h₁ (.step .silent h₂ (.refl _)), h₃, h₄,
    hfail, hprot, hb₄, hrel₃, hread, hrel₄, hwrite⟩

/-! ## 5. Multi-frame calls -/

/-- The body of the active `lean-miri` frame among `bodies` (by translation). -/
def frameBody (bodies : List CapturedMir) (fallback : CapturedMir) (m : AnnealStepState) :
    CapturedMir :=
  match m.stack.currentFrame? with
  | some f => (bodies.find? fun b => decide (translateBody b = f.body)).getD fallback
  | none => fallback

/-- The `LM-4.1` multi-frame interpreter: `annealStepHooksLM4_1` instantiated at the
body of the active frame, with `annealControlHooksLM4_1` reading the root's `_0`. -/
def callHooks (root : CapturedMir) (callees : List CapturedMir) : AnnealMiriHooks :=
  multiFrameHooks root fun c m =>
    Miri.Interpreter.Step.step (annealStepHooksLM4_1 (frameBody (root :: callees) root m) callees) c m

def fiveFnTy : Ty := { kind := .fnDef "crate::five" [], layoutIdx := 0 }

/-- Callee `crate::five`: `bb0: _0 = const 5_u8; return`. -/
def fiveBody : CapturedMir :=
  { mkBody "crate::five" [dcl tyU8] [blk [st (.assign (pl 0) (.use (cU8 5)))] .return_] with
    defPath := "crate::five" }

/-- Caller: `bb0: StorageLive(_1); _1 = crate::five() -> bb1; bb1: _0 = copy _1; StorageDead(_1); return`. -/
def callFiveBody : CapturedMir :=
  mkBody "crate::call_five" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
      (.call (.constant { ty := fiveFnTy, val := .zeroSized }) [] (pl 1) (some 1) .continue_),
     blk [st (.assign (pl 0) (.use (.copy (pl 1)))), st (.storageDead 1)] .return_]

/-- **Multi-frame call and return** (`Terminator.Call` + `Terminator.Return`,
`GlobalState.endCall` on the callee frame pop): the caller calls `crate::five`,
which returns `5_u8` into `_1`; the caller returns `5_u8`. Both machines run the
whole program from their entry states (Anneal with `crate::five` as a callee). -/
theorem w5_call_return :
    AgreeReturnsBits callFiveBody (callHooks callFiveBody [fiveBody])
      (initMachineStateWithCallees callFiveBody [] [fiveBody]) (miriEntryState callFiveBody) 1 5 :=
  agreeReturnsBits_of_obs (N := 8) (M := 8) (by decide) (by decide +kernel)

def protCallerBody : CapturedMir where
  defPath := "lm_4_3_witness::prot_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_1.u8Decl, WitnessLM4_1.u8Decl]
  basicBlocks :=
    [ { statements := []
        terminator := WitnessLM4_1.mkTerm (.call WitnessLM4_1.calleeFuncOp [] ⟨0, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := WitnessLM4_1.mkTerm .return_
        isCleanup := false } ]
  fnAbi := WitnessLM4_1.fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def protSavedCaller : SavedCallerFrame :=
  { callerBody := protCallerBody
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    destination := ⟨0, .nil⟩
    returnTarget := 1
    callerProtector := none
    calleeProtectors := [] }

def protReadyAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar WitnessLM4_1.sc1)] }
    memory :=
      { borrows :=
          [{ tag := 10
             targetLocal := 1
             targetProjection := []
             perm := .reservedFrz true
             protector := some 1
             parentTag := none }]
        callStack := [protSavedCaller]
        callees := [WitnessLM4_1.witCalleeBody]
        activeCallee := some WitnessLM4_1.witCalleeBody
        activeProtectors := [1]
        nextProtector := 2 } }

def protCallerMiriFrame (bbIdx : Nat)
    (ls0 ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody protCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none
      (translateTy WitnessLM4_1.u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[ls0, ls1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def protRetPlace0 : Miri.Interpreter.RuntimeStackPlace AnnealProv :=
  .frameLocal 0 0 none (translateTy WitnessLM4_1.u8Ty emptyLayoutTable) (.ofAllocationToken 0)

def protReadyMiri : AnnealStepState :=
  { stack :=
      ⟨#[protCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         WitnessLM4_1.mkWitCalleeMiriFrame
           ⟨.live (.immediate (.scalar (.fromScalarInt WitnessLM4_1.msc1))), none⟩ protRetPlace0]⟩
    machine := { AnnealMachine.empty with borrowTracker := some WitnessLM4_1.witCalleeBorrowTracker } }

/-- The `LM-4.1` interpreter of `protCallerBody`, selecting the hooks of the
active frame (`frameBody`) and the popped-frame state from the `lean-miri`
stack depth. -/
def protWholeHooks : AnnealMiriHooks :=
  multiFrameHooks protCallerBody fun c m =>
    Miri.Interpreter.Step.step
      (annealStepHooksLM4_1
        (frameBody [protCallerBody, WitnessLM4_1.witCalleeBody] protCallerBody m)
        [WitnessLM4_1.witCalleeBody]
        (if 1 < m.stack.frames.size then annealPoppedFrameState protReadyAnneal else {})) c m

theorem protReady_rel : MultiFrameStateRel protCallerBody protReadyAnneal protReadyMiri := by
  have hfr_caller : FrameRel protCallerBody protReadyMiri.machine
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
      (protCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd; injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd; injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · cases hdecl
  have hfr_callee := WitnessLM4_1.witCalleeFrame_rel (mach := protReadyMiri.machine)
    (.init (.scalar WitnessLM4_1.sc1))
    ⟨.live (.immediate (.scalar (.fromScalarInt WitnessLM4_1.msc1))), none⟩
    (.immediate _ _ none (fun _ h => nomatch h) (Or.inr ⟨_, rfl, WitnessLM4_1.val1_immRel⟩)) protRetPlace0
  have hlinks_root : CallerStackLinksRel protCallerBody protReadyMiri.machine protCallerBody
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] } [] []
      [protCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy WitnessLM4_1.u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hdest : CallerDestinationRel protReadyMiri.machine 0 protSavedCaller
      (protCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      (WitnessLM4_1.mkWitCalleeMiriFrame
        ⟨.live (.immediate (.scalar (.fromScalarInt WitnessLM4_1.msc1))), none⟩ protRetPlace0).returnPlace :=
    .immediate 0 WitnessLM4_1.u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks : CallerStackLinksRel protCallerBody protReadyMiri.machine
      (activeMirBody protCallerBody protReadyAnneal) protReadyAnneal.frame
      protReadyAnneal.memory.callStack protReadyAnneal.memory.activeProtectors
      protReadyMiri.stack.frames.toList.reverse :=
    .cons WitnessLM4_1.witCalleeBody protReadyAnneal.frame protSavedCaller [] [1] []
      (WitnessLM4_1.mkWitCalleeMiriFrame
        ⟨.live (.immediate (.scalar (.fromScalarInt WitnessLM4_1.msc1))), none⟩ protRetPlace0)
      (protCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      [] .Continue rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl
      (by intro _ _; rfl) hlinks_root
  have hdisj : MultiFrameAllocDisjoint protReadyMiri.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i j mp₁ mp₂ lay₁ lay₂ _ hi _
      dsimp only [protReadyMiri] at hmf
      rcases List.mem_cons.mp hmf with rfl | hmf1
      · dsimp only [protCallerMiriFrame] at hi
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · rcases List.mem_singleton.mp hmf1 with rfl
        dsimp only [WitnessLM4_1.mkWitCalleeMiriFrame] at hi
        rcases i with _ | i <;> cases hi
    · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ _ hf₁ _ hi _
      dsimp only [protReadyMiri] at hf₁
      rcases f₁ with _ | ⟨_ | f₁⟩
      · injection hf₁ with h; subst h; dsimp only [protCallerMiriFrame] at hi
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · injection hf₁ with h; subst h; dsimp only [WitnessLM4_1.mkWitCalleeMiriFrame] at hi
        rcases i with _ | i <;> cases hi
      · cases hf₁
  have hbt : BorrowTrackerStackRel protReadyAnneal.memory.borrows
      protReadyAnneal.memory.activeProtectors protReadyAnneal.memory.callStack
      protReadyMiri.machine.borrowTracker := by
    refine .cons [1] protSavedCaller [] (some WitnessLM4_1.witCalleeBorrowTracker) ?_ ?_
    · intro tracker hbt e he; injection hbt with htr; subst htr
      rcases List.mem_singleton.mp he with rfl; decide
    · refine .root [] _ ?_
      intro tracker hbt e he; injection hbt with htr; subst htr
      rcases List.mem_singleton.mp he with rfl; decide
  exact .mk _ rfl (fun h => nomatch h) (fun _ => rfl) hlinks.toFrameStackRel hlinks hdisj
    ⟨by decide, by decide, rfl, rfl, rfl⟩ (by decide) (by decide)
    (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; decide)
    (by intro e he cid hp; rcases List.mem_singleton.mp he with rfl; injection hp with h; subst h; decide)
    hbt

/-- **Protector release on return, whole program** (`Terminator.Return` with
`GlobalState.endCall`, `LM-4.1`): from the state where the callee of
`protCallerBody` (`bb0: _0 = crate::callee() -> bb1; bb1: return`) is about to
return with a live function-entry protector (`CallId 1`, a protected
`ReservedFrz` tag on the caller's `_1`), both machines run to an agreeing root
return of `1_u8` (`MultiFrameRetRel`); the callee pop's `GlobalState.endCall`
empties the borrow tracker's `protectedTags`, and Anneal's `activeProtectors`
and `callStack` become empty. `protWholeHooks` selects the `LM-4.1` hooks from
the `lean-miri` stack alone (`frameBody`). -/
theorem w5_protector_release_returns :
    (∃ v,
      AgreeReturns protCallerBody protWholeHooks protReadyAnneal protReadyMiri
        (.scalar WitnessLM4_1.sc1) v ∧
      MultiFrameRetRel protCallerBody (.scalar WitnessLM4_1.sc1) v) ∧
    ∃ s₁ m₁ tracker',
      AgreeReaches protCallerBody protWholeHooks protReadyAnneal s₁ protReadyMiri m₁ ∧
      MultiFrameStateRel protCallerBody s₁ m₁ ∧
      s₁.memory.activeProtectors = [] ∧
      s₁.memory.callStack = [] ∧
      m₁.machine.borrowTracker = some tracker' ∧
      tracker'.global.protectedTags.entries = #[] ∧
      tracker'.global.rootPointerTags = #[(⟨1, by decide⟩, ⟨5, by decide⟩)] := by
  have hsim₁ := step_terminator_return_callee_simulation protReady_rel rfl
    (by intro tf htf; injection htf with h; subst h; rfl)
    (fun _ h => nomatch h)
    (bb := { statements := [], terminator := WitnessLM4_1.mkTerm .return_, isCleanup := false })
    (decl0 := WitnessLM4_1.u8Decl)
    rfl rfl rfl rfl rfl rfl (fun h => nomatch h)
    (by intro destIdx destDecl hcf hdd v imm himm
        injection hcf with hd _; subst hd
        injection hdd with hdd'; subst hdd'; exact himm)
  let s₁ : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 0, locals := [.init (.scalar WitnessLM4_1.sc1), .uninit] }
      memory := { protReadyAnneal.memory with
                    callStack := [], activeCallee := some protCallerBody, activeProtectors := [] } }
  have hs₁ : stepMirFn protCallerBody protReadyAnneal = .step s₁ := rfl
  have hcore₁ : protWholeHooks.coreStep () protReadyMiri =
      Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody protCallerBody protReadyAnneal)
          protReadyAnneal.memory.callees (annealPoppedFrameState protReadyAnneal)) () protReadyMiri := by
    have hfb : frameBody [protCallerBody, WitnessLM4_1.witCalleeBody] protCallerBody protReadyMiri =
        WitnessLM4_1.witCalleeBody := by
      have hcur : protReadyMiri.stack.currentFrame? =
          some (WitnessLM4_1.mkWitCalleeMiriFrame
            ⟨.live (.immediate (.scalar (.fromScalarInt WitnessLM4_1.msc1))), none⟩ protRetPlace0) := rfl
      unfold frameBody
      rw [hcur]
      dsimp only [WitnessLM4_1.mkWitCalleeMiriFrame, List.find?]
      have hne : decide (translateBody protCallerBody = translateBody WitnessLM4_1.witCalleeBody) = false := by
        decide
      have heq : decide (translateBody WitnessLM4_1.witCalleeBody = translateBody WitnessLM4_1.witCalleeBody) = true :=
        decide_eq_true rfl
      rw [hne, heq]
      rfl
    dsimp only [protWholeHooks, multiFrameHooks]
    rw [hfb]
    rfl
  rw [hs₁, ← hcore₁] at hsim₁
  have hbt₁ : ∃ tracker',
      (protWholeHooks.coreStep () protReadyMiri).1.machine.borrowTracker = some tracker' ∧
      tracker'.global.protectedTags.entries = #[] ∧
      tracker'.global.rootPointerTags = #[(⟨1, by decide⟩, ⟨5, by decide⟩)] := by
    rw [hcore₁]
    exact ⟨_, rfl, rfl, rfl⟩
  generalize hm₁_eq : protWholeHooks.coreStep () protReadyMiri = mRes₁ at hsim₁ hbt₁
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
    obtain ⟨tracker', htr', hpt', hrt'⟩ := hbt₁
    have hsz₁ : m₁.stack.frames.size = 1 := by
      rcases hrel₁ with ⟨tf₁, _, _, _, _, hlinks₁, _⟩
      generalize hmfs : m₁.stack.frames.toList.reverse = mfs at hlinks₁
      change CallerStackLinksRel _ _ protCallerBody s₁.frame [] [] mfs at hlinks₁
      cases hlinks₁ with
      | root _ rootMf _ _ _ _ =>
        have hf := array_eq_of_toList_reverse_cons hmfs
        rw [show m₁.stack.frames = #[rootMf] by simpa using hf]
        rfl
    have hfb₁ : frameBody [protCallerBody, WitnessLM4_1.witCalleeBody] protCallerBody m₁ =
        protCallerBody := by
      rcases hrel₁ with ⟨tf₁, _, _, _, _, hlinks₁, _⟩
      generalize hmfs : m₁.stack.frames.toList.reverse = mfs at hlinks₁
      change CallerStackLinksRel _ _ protCallerBody s₁.frame [] [] mfs at hlinks₁
      cases hlinks₁ with
      | root _ rootMf _ _ _ hfr₁ =>
        have hf : m₁.stack.frames = #[rootMf] := by
          have h := array_eq_of_toList_reverse_cons hmfs; simpa using h
        have hcur : m₁.stack.currentFrame? = some rootMf := by
          unfold Miri.Interpreter.Stack.currentFrame?; rw [hf]; rfl
        unfold frameBody
        rw [hcur]
        dsimp only
        rw [hfr₁.body_eq]
        simp
    have hcore₂ : protWholeHooks.coreStep () m₁ =
        Miri.Interpreter.Step.step
          (annealStepHooksLM4_1 (activeMirBody protCallerBody s₁) s₁.memory.callees
            (annealPoppedFrameState s₁)) () m₁ := by
      dsimp only [protWholeHooks, multiFrameHooks]
      rw [hfb₁, hsz₁]
      rfl
    have hret_wf : ∀ tf, m₁.stack.frames.back? = some tf →
        RootIndirectRetWf m₁.machine protCallerBody s₁.frame tf := by
      intro tf htf
      apply RootIndirectRetWf.of_immediate
      intro mls hmls mp hmp
      rcases hrel₁ with ⟨tf₁, _, _, _, _, hlinks₁, _, _⟩
      generalize hmfs : m₁.stack.frames.toList.reverse = mfs at hlinks₁
      change CallerStackLinksRel _ _ protCallerBody s₁.frame [] [] mfs at hlinks₁
      cases hlinks₁ with
      | root _ rootMf _ _ _ hfr₁ =>
        have hf : m₁.stack.frames = #[rootMf] := by
          have h := array_eq_of_toList_reverse_cons hmfs; simpa using h
        have htf_eq : tf = rootMf := by
          rw [hf] at htf
          exact (Option.some.inj htf).symm
        subst htf_eq
        obtain ⟨sl₀, ml₀, _, _, hs₀, hm₀, _, hl₀⟩ :=
          hfr₁.lookup_local (i := 0) (decl := WitnessLM4_1.u8Decl) rfl
        rw [hmls] at hm₀; injection hm₀ with hm₀; subst hm₀
        rcases mls with ⟨v₀, lay₀⟩; dsimp only at hmp; subst hmp
        cases hl₀ with
        | indirect _ _ _ _ _ hm =>
          rcases hm with ⟨id₀, _, _, _, la₀, _, _, _, hlive₀, _⟩
          have hlive_emp : m₁.machine.memory.live = #[] := by
            have := congrArg (fun r => r.1.machine.memory.live) (hcore₁.symm.trans hm₁_eq)
            exact this.symm
          rw [hlive_emp] at hlive₀
          cases hlive₀
    have hsim₂ := step_terminator_return_root_simulation hrel₁ rfl (fun _ h => nomatch h)
      (bb := { statements := [], terminator := WitnessLM4_1.mkTerm .return_, isCleanup := false })
      (decl0 := WitnessLM4_1.u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h) hret_wf
    have hs₂ : stepMirFn protCallerBody s₁ = .retNormal (.scalar WitnessLM4_1.sc1) s₁.memory := rfl
    rw [hs₂, ← hcore₂] at hsim₂
    generalize hm₂_eq : protWholeHooks.coreStep () m₁ = mRes₂ at hsim₂
    cases hsim₂ with
    | retRoot decl0 _ v _ m₂ hdecl0 hop0 hvrel hm₂ =>
      subst hm₂
      have hvrel' : MultiFrameRetRel protCallerBody (.scalar WitnessLM4_1.sc1) v :=
        ⟨decl0, hdecl0, hvrel.imp id fun ⟨mp0, h1, h2⟩ => ⟨m₁.machine, mp0, h1, h2⟩⟩
      refine ⟨⟨v, ?_, hvrel'⟩, s₁, m₁, tracker',
        agreeReaches_of_paths (.step .silent hs₁ (.refl _))
          (.step hm₁_eq hrel₁.frames_ne_empty (.refl _)),
        hrel₁, rfl, rfl, htr', hpt', hrt'⟩
      exact agreeReturns_of_paths (p := 0) rfl rfl
        (.step .silent hs₁ (.refl _)) hs₂
        (.step hm₁_eq hrel₁.frames_ne_empty (.refl _))
        hm₂_eq rfl (by
          change ((annealControlHooksLM4_1 protCallerBody.localDecls
            protCallerBody.layouts).returnOperand () m₁).2 = _
          rw [hop0])

/-- Callee `crate::stuck`: `bb0: unreachable`. -/
def stuckBody : CapturedMir :=
  { mkBody "crate::stuck" [dcl tyU8] [blk [] .unreachable] with defPath := "crate::stuck" }

def stuckFnTy : Ty := { kind := .fnDef "crate::stuck" [], layoutIdx := 0 }

/-- Caller: `bb0: StorageLive(_1); _1 = crate::stuck() -> bb1; bb1: _0 = copy _1; return`. -/
def callStuckBody : CapturedMir :=
  mkBody "crate::call_stuck" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
      (.call (.constant { ty := stuckFnTy, val := .zeroSized }) [] (pl 1) (some 1) .continue_),
     blk [st (.assign (pl 0) (.use (.copy (pl 1))))] .return_]

/-- Reaching `Unreachable` inside a callee frame is undefined behavior in both machines. -/
theorem w5_callee_unreachable_ub :
    AgreeUB callStuckBody (callHooks callStuckBody [stuckBody])
      (initMachineStateWithCallees callStuckBody [] [stuckBody]) (miriEntryState callStuckBody) :=
  agreeUB_of_obs (N := 4) (M := 4) (by decide) (by decide +kernel)

/-- Callee `crate::noret`: `bb0: return` with `_0` never written. -/
def noRetBody : CapturedMir :=
  { mkBody "crate::noret" [dcl tyU8] [blk [] .return_] with defPath := "crate::noret" }

def noRetFnTy : Ty := { kind := .fnDef "crate::noret" [], layoutIdx := 0 }

/-- Caller of `crate::noret`. -/
def callNoRetBody : CapturedMir :=
  mkBody "crate::call_noret" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
      (.call (.constant { ty := noRetFnTy, val := .zeroSized }) [] (pl 1) (some 1) .continue_),
     blk [st (.assign (pl 0) (.use (.copy (pl 1))))] .return_]

/-- Returning from a callee whose `_0` is uninitialized is undefined behavior in both machines. -/
theorem w5_callee_uninit_return_ub :
    AgreeUB callNoRetBody (callHooks callNoRetBody [noRetBody])
      (initMachineStateWithCallees callNoRetBody [] [noRetBody]) (miriEntryState callNoRetBody) :=
  agreeUB_of_obs (N := 4) (M := 4) (by decide) (by decide +kernel)

/-! ## 7. Whole-program return traces for `LM-4.2` intrinsics and the
checked-addition closed simulation -/

/-! ### `arith_offset` and `write_bytes` return traces -/

/-- A real `lean-miri` step of an `arith_offset` / `wrapping_offset` call whose
pointer argument holds a raw pointer and whose count argument is initialized
keeps every immediate local immediate: the call writes its result into the
immediate destination local as an immediate and moves to the target block. -/
theorem retArithOffsetCall_preserves_imm
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {calleePath : DefPath} {k : AnnealIntrinsic} (hk : k = .arithOffset ∨ k = .wrappingOffset)
    {pointeeKind : RigidTy} {c : ConstOperand} {ptrIdx : Local} {countOp : MirAst.Operand}
    {dstIdx : Local} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef calleePath [pointeeKind])
    (hpath : AnnealIntrinsic.ofDefPath? calleePath = some k)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {p₀ : ProvenancePtr} (hptrSlot : get? s.frame.locals ptrIdx = some (.init (.ptr p₀ 8)))
    {countTy : Ty} (hcountInt : IsIntegralTy countTy .isize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {count₀ : MirAst.ScalarInt}
    (hcountEval : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.scalar count₀) s.frame.locals)
    {dstDecl : LocalDecl}
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstLive : get? s.frame.locals dstIdx ≠ some .dead)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    {elemBytes : Nat}
    (helem_miri :
      (scalarLayoutOfRigidTy pointeeKind).map (·.size.bytes.toNat) = some elemBytes)
    (helem_lt : elemBytes < 2 ^ 63)
    (hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j := by
  have helem_miri' :
      (layoutOfEncodedTyId (encodeTyId { kind := pointeeKind, layoutIdx := 0 })
        body.layouts).layout.size.bytes.toNat = elemBytes :=
    layoutOfEncodedTyId_size_of_scalarLayoutOfRigidTy body.layouts helem_miri
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hk_arity : k.arity = 2 := by rcases hk with rfl | rfl <;> rfl
  have hk_name : k.name = AnnealIntrinsic.arithOffset.name := by
    rcases hk with rfl | rfl <;> rfl
  have hptr_ne_move : ∀ p, translateOperand (.copy ⟨ptrIdx, []⟩) ≠ .Move p :=
    fun _ h => by cases h
  -- Destination place and callee.
  obtain ⟨dslot, dmls, _, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee_m := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := pointeeKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  have hvals₁ : ∀ j : Nat,
      ((cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)).locals[j]?).map
        Miri.Interpreter.LocalState.value =
      (tf.locals[j]?).map Miri.Interpreter.LocalState.value := by
    intro j
    simp only [cacheFrameLocalLayout]
    by_cases hj : dstIdx = j
    · subst hj
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · rw [Array.getElem?_set_ne _ hj]
  -- The destination holds an immediate.
  obtain ⟨oldImm, hdval⟩ : ∃ oldImm, dmls.value = .live (.immediate oldImm) := by
    have hd := hdstImm tf hframes dmls hdmls
    cases hdloc with
    | rawPtr _ mptr₀ _ _ _ _ _ _ =>
      exact ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr₀), rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (hd mp)
      | dead _ _ => exact absurd hdslot hdstLive
      | immediate _ imm _ _ _ => exact ⟨imm, rfl⟩
  let argTyId : Miri.MIR.TyId := encodeTyId { kind := pointeeKind, layoutIdx := 0 }
  let dstPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have helem_miri_lt : (layoutOfEncodedTyId argTyId body.layouts).layout.size.bytes.toNat <
      2 ^ 63 := by
    dsimp only [argTyId]; rw [helem_miri']; exact helem_lt
  -- Pointer operand.
  rcases annealEvalOperand_rawPtr_copy_lm3_1 hstate₁ rfl hptrDecl hptrTy
      (himm₁ ptrIdx (hptrImm tf hframes)) with
    ⟨_, _, ha₁, _⟩ | ⟨_, ha₁, _, _, _⟩ |
      ⟨_, _, _, hslot_ptr, _, _, _, _, _, _⟩ |
      ⟨p, mptr, tf₂, _, _, _, hm₁, hstate₂, hvals₂⟩
  · simp [evalOperand, readProjectedValue, hptrSlot] at ha₁
  · simp [evalOperand, readProjectedValue, hptrSlot] at ha₁
  · rw [hptrSlot] at hslot_ptr; cases hslot_ptr
  have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
  -- Count operand.
  rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl
      ((hcountOp tf hframes).mono_immediate himm₂) hcountInt.prim with
    ⟨_, _, ha₂, _⟩ | ⟨_, ha₂, _, _, _⟩ |
      ⟨countSc, mcount, tf₃, _, hm₂, _, hrel₂, hvals₃⟩
  · rw [hcountEval] at ha₂; cases ha₂
  · rw [hcountEval] at ha₂; cases ha₂
  have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
  cases hrel₂ with
  | scalar _ _ hrel_c hsz_c _ _ =>
  have hcount8 : countSc.sizeBytes = 8 :=
    translateSizeBytes_inj hrel_c.validBytes (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (hsz_c.symm.trans (hcountInt.size_eq body.layouts))
  let mptr' : Miri.Memory.Pointer AnnealProv :=
    { mptr with
      offset := Miri.ABI.Size.ofBytes
        (mptr.offset.bytes + UInt64.ofNat (countSc.bits * elemBytes)) }
  have hev : Miri.Interpreter.Intrinsics.eval
      (annealIntrinsicHooks body.localDecls body.layouts) ()
      AnnealIntrinsic.arithOffset.name #[argTyId]
      #[⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy ptrDecl.ty body.layouts⟩,
        ⟨.immediate (.scalar (.fromScalarInt mcount)), translateTy countTy body.layouts⟩]
      dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
      (do
        annealWritePointer mptr'.withOptionalProvenance dstPlace
        annealReturnToBlock (some targetBb)
        pure true) { m with stack := ⟨#[tf₃]⟩ } := by
    rw [intrinsics_eval_arithOffset,
      annealArithOffsetEval_ok body.layouts argTyId _ dstPlace (some targetBb) _
        (intrinsicPointer_fromPointer mptr _ _) hrel_c hcount8 helem_miri_lt]
    dsimp only [argTyId, Miri.Memory.Pointer.withOptionalProvenance, mptr']
    rw [helem_miri']
  -- The destination local of `tf₃`.
  have hv₃ := hvals₃ dstIdx
  rw [hvals₂ dstIdx, hvals₁ dstIdx, hdmls] at hv₃
  obtain ⟨mls₃, hmls₃, hmls₃_val⟩ : ∃ mls₃, tf₃.locals[dstIdx]? = some mls₃ ∧
      mls₃.value = .live (.immediate oldImm) := by
    cases h3 : tf₃.locals[dstIdx]? with
    | none => rw [h3] at hv₃; cases hv₃
    | some mls₃ =>
      rw [h3] at hv₃
      injection hv₃ with hv₃'
      exact ⟨mls₃, rfl, hv₃'.trans hdval⟩
  obtain ⟨hlt₃, _⟩ := Array.getElem?_eq_some_iff.mp hmls₃
  have hget₃ : tf₃.getLocal dstIdx = .ok ⟨.live (.immediate oldImm), mls₃.layout⟩ := by
    rw [frame_getLocal_of_getElem? tf₃ dstIdx mls₃ hmls₃]
    rcases mls₃ with ⟨v₃, l₃⟩
    dsimp only at hmls₃_val
    rw [hmls₃_val]
  let newImm : Miri.Interpreter.Immediate AnnealProv :=
    .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr')
  let tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { { tf₃ with
        locals := tf₃.locals.set dstIdx
          { tf₃.locals[dstIdx]'hlt₃ with value := .live (.immediate newImm) } hlt₃ } with
      location := .mir ⟨targetBb, 0⟩ }
  have hwm : (do
      annealWritePointer mptr'.withOptionalProvenance dstPlace
      annealReturnToBlock (some targetBb)
      pure true) { m with stack := ⟨#[tf₃]⟩ } = .ok true { m with stack := ⟨#[tf₄]⟩ } := by
    have hw : annealWritePointer mptr'.withOptionalProvenance dstPlace =
        annealWriteImmediate newImm dstPlace := rfl
    rw [hw, EStateM.bind_eq_ok (annealWriteImmediate_live (m := { m with stack := ⟨#[tf₃]⟩ })
      rfl hlt₃ hget₃)]
    rw [EStateM.bind_eq_ok (annealReturnToBlock_some rfl targetBb)]
    rfl
  have hcomp : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      ({ m with stack := ⟨#[tf₄]⟩ }, .ok true) := by
    rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
      translateTerminator_intrinsic_call_ofDefPath? hterm hc hpath]
    simp only [List.map_cons, List.map_nil]
    rw [controlFlow_evalTerminator_call _ _ _ rfl,
      evalCallTerminator_intrinsic_two _ _ k _ hk_arity _ _ hptr_ne_move
        ((hcountOp tf hframes).translate_ne_move),
      hk_name]
    rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
      EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
      EStateM.bind_eq_ok hcallee_m, EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂,
      EStateM.bind_eq_ok (hev.trans hwm)]
    simp only [↓reduceIte, Option.isSome_some]
    rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq
      (m := { m with stack := ⟨#[tf₄]⟩ }) (tf := tf₄) rfl)]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
      (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
    have hloc₄ : tf₄.location = .mir ⟨targetBb, 0⟩ := rfl
    rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
    simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
      stack_currentFrame?_singleton m.stack tf hframes, hframes,
      stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
        Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
      option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
  intro tf₀ tf' htf₀ htf' j hj
  rw [hframes] at htf₀
  injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
  rw [hcomp] at hstep
  injection hstep with hm' _
  subst hm'
  injection htf' with h₁; injection h₁ with h₁'; subst h₁'
  intro mls hmls mp hmp
  dsimp only [tf₄] at hmls
  rw [Array.getElem?_set] at hmls
  by_cases hdj : dstIdx = j
  · subst hdj
    simp only [↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hmp
    cases hmp
  · simp only [hdj, ↓reduceIte] at hmls
    exact himm₃ j hj mls hmls mp hmp

/-- **`retArithOffset_trace`**: whole-program run of
`WitnessLM4_2.arithOffsetPosBody`, from `ptr4AnnealPre` / `ptr4MiriPre`, to its
root return:

```text
bb0: _2 = &raw mut _1;
     _0 = arith_offset::<u64>(copy _2, 5_isize) -> bb1;
bb1: return
```

Both machines take the two steps of `wit_lm4_2_arith_offset_pos` in lockstep,
and then both return from the root frame. Anneal returns the raw pointer
`{ allocId := 1, offsetBytes := 40 }`, which points `40` bytes past the start of
the 8-byte stack allocation of `_1`, and `lean-miri` returns an immediate
related to it by `ImmediateRelLM3_1.rawPtr`. -/
theorem retArithOffset_trace :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := WitnessLM4_2.arithOffsetPosBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (WitnessLM4_2.ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      StepObsRelLM3_1 b m₂ [entry] (stepMirFn b s₂) (Miri.Interpreter.Step.step hooks () m₂) ∧
      stepMirFn b s₂ = .retNormal (.ptr { allocId := 1, offsetBytes := 40 } 8) s₂.memory ∧
      Miri.Interpreter.Step.step hooks () m₂ = ({ m₂ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₂ = (m₂, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_1 [entry] decl0.ty b.layouts
        (.ptr { allocId := 1, offsetBytes := 40 } 8) imm0 := by
  let b := WitnessLM4_2.arithOffsetPosBody
  have hrel₀ : StateRel b (WitnessLM4_2.ptr4AnnealPre b)
      (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K) :=
    WitnessLM4_2.ptr4_stateRel WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
      WitnessLM4_2.rawMutU64K
      [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
        (.rawPtr .mut (WitnessLM4_2.local42 1)))]
      (WitnessLM4_2.arithOffsetTerm 2 5)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨WitnessLM4_2.ptr4_all_immediate b _ tf htf 2,
       WitnessLM4_2.ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  -- Step 1: `_2 = &raw mut _1`.
  let s₁ := WitnessLM4_2.mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (WitnessLM4_2.ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (WitnessLM4_2.ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.rawMutU64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (WitnessLM4_2.ptr4_all_immediate b _ _ rfl k)
  -- Step 2: `_0 = arith_offset::<u64>(copy _2, 5_isize) -> bb1`.
  let s₂ := WitnessLM4_2.mkPtrState b 1 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hcountOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.isizeK 5 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.isizeK) :=
    fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.isize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₁
  have hsim₂ := call_intrinsic_offset_simulation hrel₁ hphase rfl rfl rfl (Or.inl rfl) rfl rfl rfl
    rfl (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    WitnessLM4_2.isize_integral hcountOp
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 0 (by decide)) rfl rfl (by decide)
    (fun p countSc hp hc _ => by
      have hp' : p = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, WitnessLM4_2.mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨5, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      subst hp' hc'
      decide)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  -- `_0` is still an immediate local of `lean-miri`'s frame after the call.
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → IsImmediateFrameLocal tf₂ 0 := by
    intro tf₂ htf₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact retArithOffsetCall_preserves_imm hrel₁ rfl rfl (Or.inl rfl) rfl rfl rfl
      (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide)) rfl
      WitnessLM4_2.isize_integral hcountOp rfl rfl (by intro h; cases h)
      (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 0 (by decide)) rfl (by decide) hm₂
      tf₁ tf₂ htf₁ htf₂ 0 (himm₁ tf₁ htf₁ 0 (by decide))
  -- Step 3: root-frame `return` of the raw pointer in `_0`.
  have hs₃ : stepMirFn b s₂ =
      .retNormal (.ptr { allocId := 1, offsetBytes := 40 } 8) s₂.memory := rfl
  have hobs₃ := step_terminator_return_rawPtr_lm3_1_simulation hrel₂ hphase rfl rfl rfl rfl rfl
    rfl rfl himm₂
  have hsim₃ := hobs₃
  rw [hs₃] at hsim₃
  obtain ⟨decl0, imm0, hdecl0, hop, himm, hmret⟩ := hsim₃.retNormal_rel
  exact ⟨s₁, s₂, m₁, m₂, decl0, imm0, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hobs₃, hs₃, hmret,
    hdecl0, hop, himm⟩

/-- A root-frame return under `StepRelLM3_1` returns a value related by
`ImmediateRel` to `lean-miri`'s return operand and pops the root frame. -/
theorem retStepRelLM3_1_retNormal_rel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap (.retNormal retVal mem') mRes) :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRel decl0.ty body.layouts retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  obtain ⟨decl0, imm0, hdecl, hop, himm, hm⟩ := h.toStepObsRelLM3_1.retNormal_rel
  generalize ha : MirStepNode.retNormal retVal mem' = aNode at h
  cases h with
  | step _ _ _ => cases ha
  | retRoot decl0' rv imm0' mm _ hdecl' hop' himm' _ =>
    injection ha with h1
    injection h1 with h2
    injection h2 with hrv _
    subst hrv
    exact ⟨decl0', imm0', hdecl', hop', himm', hm⟩
  | ub _ _ => cases ha

/-- `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb1` into the unit local
`_3`. -/
def retWriteBytesTerm : TerminatorKind :=
  .call (.constant (WitnessLM4_2.fnItem "core::intrinsics::write_bytes" WitnessLM4_2.u64K))
    [.copy (WitnessLM4_2.local42 2),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.u8K 0xAB 1),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8)]
    (WitnessLM4_2.local42 3) (some 1) .unreachable

/-! ### `write_bytes` return trace

`retWriteBytesCall_preserves_imm` keeps every immediate local of `lean-miri`'s
frame immediate across a `write_bytes` call. With it, `retWriteBytesRead_trace`
needs no `StorageLive(_0)`, and the program returns the bytes that
`write_bytes` wrote, read back through the raw pointer. -/

/-- `act` leaves `lean-miri`'s stack unchanged whenever it succeeds. -/
def retStackPreserving {α : Type} (act : Miri.Interpreter.RvalueM AnnealStepState α) : Prop :=
  ∀ st a st', act st = .ok a st' → st'.stack = st.stack

theorem retStackPreserving_pure {α : Type} (x : α) :
    retStackPreserving (pure x : Miri.Interpreter.RvalueM AnnealStepState α) := by
  intro st a st' h
  cases h
  rfl

theorem retStackPreserving_throw {α : Type} (e : Miri.Interpreter.StepError) :
    retStackPreserving (throw e : Miri.Interpreter.RvalueM AnnealStepState α) := by
  intro st a st' h
  cases h

theorem retStackPreserving_bind {α β : Type} {x : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    (hx : retStackPreserving x) (hf : ∀ a, retStackPreserving (f a)) :
    retStackPreserving (x >>= f) := by
  intro st b st' h
  cases hxs : x st with
  | error e s => rw [EStateM.bind_eq_error hxs] at h; cases h
  | ok a s => rw [EStateM.bind_eq_ok hxs] at h; exact (hf a s b st' h).trans (hx st a s hxs)

theorem retStackPreserving_liftScalarResult {α : Type} (r : Except Miri.Interpreter.StepError α) :
    retStackPreserving (liftScalarResult r : Miri.Interpreter.RvalueM AnnealStepState α) := by
  cases r with
  | ok v => exact retStackPreserving_pure v
  | error e => exact retStackPreserving_throw e

theorem retStackPreserving_readImmediate (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retStackPreserving (annealReadImmediate ⟨.immediate imm, lay⟩) := by
  cases imm with
  | scalar _ => exact retStackPreserving_pure _
  | scalarPair _ _ => exact retStackPreserving_pure _
  | uninit => exact retStackPreserving_throw _

theorem retStackPreserving_intrinsicScalar (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retStackPreserving (intrinsicScalar ⟨.immediate imm, lay⟩) :=
  retStackPreserving_bind (retStackPreserving_readImmediate imm lay)
    (fun _ => retStackPreserving_liftScalarResult _)

theorem retStackPreserving_intrinsicPointer (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retStackPreserving (intrinsicPointer ⟨.immediate imm, lay⟩) :=
  retStackPreserving_bind (retStackPreserving_intrinsicScalar imm lay)
    (fun _ => retStackPreserving_liftScalarResult _)

theorem retStackPreserving_intrinsicUsize (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retStackPreserving (intrinsicUsize ⟨.immediate imm, lay⟩) :=
  retStackPreserving_bind (retStackPreserving_intrinsicScalar imm lay)
    (fun _ => retStackPreserving_liftScalarResult _)

theorem retStackPreserving_pointeeTypeOf (t : Miri.MIR.TyId) :
    retStackPreserving (annealPointeeTypeOf t) := by
  unfold annealPointeeTypeOf
  split
  · exact retStackPreserving_pure _
  · exact retStackPreserving_throw _

theorem retStackPreserving_writeRepeatedBytes (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (byte : UInt8) (size : Miri.ABI.Size) :
    retStackPreserving (annealWriteRepeatedBytes ptr byte size) := by
  intro st a st' h
  unfold annealWriteRepeatedBytes at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- `write_bytes` on immediate operands only writes memory: when it succeeds,
`lean-miri`'s stack is unchanged. -/
theorem retStackPreserving_writeBytesEval (ly : LayoutTable)
    (i₁ i₂ i₃ : Miri.Interpreter.Immediate AnnealProv) (l₁ l₂ l₃ : Miri.Interpreter.LocalLayout) :
    retStackPreserving
      (annealWriteBytesEval ly ⟨.immediate i₁, l₁⟩ ⟨.immediate i₂, l₂⟩ ⟨.immediate i₃, l₃⟩) := by
  unfold annealWriteBytesEval
  refine retStackPreserving_bind (retStackPreserving_pointeeTypeOf _) (fun _ => ?_)
  refine retStackPreserving_bind (retStackPreserving_intrinsicPointer _ _) (fun _ => ?_)
  refine retStackPreserving_bind (retStackPreserving_intrinsicScalar _ _) (fun _ => ?_)
  refine retStackPreserving_bind (retStackPreserving_liftScalarResult _) (fun _ => ?_)
  refine retStackPreserving_bind (retStackPreserving_intrinsicUsize _ _) (fun _ => ?_)
  split
  all_goals first
    | exact retStackPreserving_throw _
    | exact retStackPreserving_writeRepeatedBytes _ _ _

/-- A real `lean-miri` step of a `write_bytes::<T>(copy ptr, val, count)` call
that succeeds keeps every immediate local immediate: the call only evaluates
its operands, writes memory, and moves to the target block. -/
theorem retWriteBytesCall_preserves_imm
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {c : ConstOperand} {ptrIdx dstIdx : Local} {valOp countOp : MirAst.Operand}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {pointeeTy : Ty}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, valOp, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.writeBytes.defPath [pointeeTy.kind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeTy.kind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {valTy countTy : Ty}
    (hvalInt : IsIntegralTy valTy .u8)
    (hvalOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf valOp valTy)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, dmls, _, hlt_mf, _, _, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hcache_dst : ∀ l, (tf.locals[dstIdx]'hlt_mf).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst hcache_dst
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  let tf₁ := cacheFrameLocalLayout tf dstIdx hlt_mf (translateTy dstDecl.ty body.layouts)
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts
    AnnealIntrinsic.writeBytes (encodeTyId { kind := pointeeTy.kind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[tf₁]⟩ }) rfl
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₁ j :=
    fun j hj => hj.cache_layout hlt_mf _
  have hptr_nm : ∀ p, translateOperand (.copy ⟨ptrIdx, []⟩) ≠ .Move p := by
    intro p hp; simp only [translateOperand, reduceCtorEq] at hp
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc] at hstep
  simp only [List.map_cons, List.map_nil] at hstep
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_three _ _ AnnealIntrinsic.writeBytes _ writeBytes_arity _ _ _
      hptr_nm ((hvalOp tf hframes).translate_ne_move)
      ((hcountOp tf hframes).translate_ne_move)] at hstep
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee] at hstep
  -- Pointer operand: an error stops the call; otherwise it is an immediate.
  obtain ⟨imm₁, tf₂, hm₁, hstate₂, hvals₂⟩ : ∃ imm₁ tf₂,
      annealEvalOperand body.localDecls body.layouts (translateOperand (.copy ⟨ptrIdx, []⟩)) none
        { m with stack := ⟨#[tf₁]⟩ } =
        .ok ⟨.immediate imm₁, translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tf₂]⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf₂]⟩ } allocMap ∧
      (∀ k : Nat, (tf₂.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf₁.locals[k]?).map Miri.Interpreter.LocalState.value) := by
    rcases annealEvalOperand_rawPtr_copy_lm3_1 hstate₁ rfl hptrDecl hptrTy
        (himm₁ ptrIdx (hptrImm tf hframes)) with
      ⟨_, _, _, hm₁⟩ | ⟨tf₂, _, hm₁, hst₂, hv₂⟩ | ⟨_, _, tf₂, _, _, _, _, hm₁, hst₂, hv₂⟩ |
        ⟨_, _, tf₂, _, _, _, hm₁, hst₂, hv₂⟩
    · exfalso
      rw [EStateM.bind_eq_error hm₁] at hstep
      simp [Except.map] at hstep
    · exact ⟨_, tf₂, hm₁, hst₂, hv₂⟩
    · exact ⟨_, tf₂, hm₁, hst₂, hv₂⟩
    · exact ⟨_, tf₂, hm₁, hst₂, hv₂⟩
  rw [EStateM.bind_eq_ok hm₁] at hstep
  have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
  -- Value operand.
  obtain ⟨imm₂, tf₃, hm₂, hstate₃, hvals₃⟩ : ∃ imm₂ tf₃,
      annealEvalOperand body.localDecls body.layouts (translateOperand valOp) none
        { m with stack := ⟨#[tf₂]⟩ } =
        .ok ⟨.immediate imm₂, translateTy valTy body.layouts⟩ { m with stack := ⟨#[tf₃]⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf₃]⟩ } allocMap ∧
      (∀ k : Nat, (tf₃.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf₂.locals[k]?).map Miri.Interpreter.LocalState.value) := by
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl
        ((hvalOp tf hframes).mono_immediate himm₂) hvalInt.prim with
      ⟨_, _, _, hm₂⟩ | ⟨tf₃, _, hm₂, hst₃, hv₃⟩ | ⟨_, _, tf₃, _, hm₂, hst₃, _, hv₃⟩
    · exfalso
      rw [EStateM.bind_eq_error hm₂] at hstep
      simp [Except.map] at hstep
    · exact ⟨_, tf₃, hm₂, hst₃, hv₃⟩
    · exact ⟨_, tf₃, hm₂, hst₃, hv₃⟩
  rw [EStateM.bind_eq_ok hm₂] at hstep
  have himm₃ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₃ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ j hj)
  -- Count operand.
  obtain ⟨imm₃, tf₄, hm₃, hvals₄⟩ : ∃ imm₃ tf₄,
      annealEvalOperand body.localDecls body.layouts (translateOperand countOp) none
        { m with stack := ⟨#[tf₃]⟩ } =
        .ok ⟨.immediate imm₃, translateTy countTy body.layouts⟩ { m with stack := ⟨#[tf₄]⟩ } ∧
      (∀ k : Nat, (tf₄.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf₃.locals[k]?).map Miri.Interpreter.LocalState.value) := by
    rcases annealEvalOperand_scalar_lm3_1 hstate₃ rfl
        ((hcountOp tf hframes).mono_immediate himm₃) hcountInt.prim with
      ⟨_, _, _, hm₃⟩ | ⟨tf₄, _, hm₃, _, hv₄⟩ | ⟨_, _, tf₄, _, hm₃, _, _, hv₄⟩
    · exfalso
      rw [EStateM.bind_eq_error hm₃] at hstep
      simp [Except.map] at hstep
    · exact ⟨_, tf₄, hm₃, hv₄⟩
    · exact ⟨_, tf₄, hm₃, hv₄⟩
  rw [EStateM.bind_eq_ok hm₃, intrinsics_eval_writeBytes] at hstep
  have himm₄ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₄ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hvals₄ (himm₃ j hj)
  -- The memory write itself leaves the frame alone.
  cases hwb : annealWriteBytesEval body.layouts
      ⟨.immediate imm₁, translateTy ptrDecl.ty body.layouts⟩
      ⟨.immediate imm₂, translateTy valTy body.layouts⟩
      ⟨.immediate imm₃, translateTy countTy body.layouts⟩ { m with stack := ⟨#[tf₄]⟩ } with
  | error e s' =>
    exfalso
    have hev : (do
        annealWriteBytesEval body.layouts
          ⟨.immediate imm₁, translateTy ptrDecl.ty body.layouts⟩
          ⟨.immediate imm₂, translateTy valTy body.layouts⟩
          ⟨.immediate imm₃, translateTy countTy body.layouts⟩
        annealReturnToBlock (some targetBb)
        pure true) { m with stack := ⟨#[tf₄]⟩ } = .error e s' :=
      EStateM.bind_eq_error hwb
    rw [EStateM.bind_eq_error hev] at hstep
    simp [Except.map] at hstep
  | ok u s₅ =>
    have hstk := retStackPreserving_writeBytesEval body.layouts imm₁ imm₂ imm₃ _ _ _ _ u s₅ hwb
    have hframes₅ : s₅.stack.frames = #[tf₄] := by rw [hstk]
    let tf₅ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { tf₄ with location := .mir ⟨targetBb, 0⟩ }
    have hret := annealReturnToBlock_some (m := s₅) (tf := tf₄) hframes₅ targetBb
    have hev : (do
        annealWriteBytesEval body.layouts
          ⟨.immediate imm₁, translateTy ptrDecl.ty body.layouts⟩
          ⟨.immediate imm₂, translateTy valTy body.layouts⟩
          ⟨.immediate imm₃, translateTy countTy body.layouts⟩
        annealReturnToBlock (some targetBb)
        pure true) { m with stack := ⟨#[tf₄]⟩ } =
        .ok true { stack := ⟨#[tf₅]⟩, machine := s₅.machine } := by
      rw [EStateM.bind_eq_ok hwb, EStateM.bind_eq_ok hret]
      rfl
    rw [EStateM.bind_eq_ok hev] at hstep
    simp only [↓reduceIte, Option.isSome_some] at hstep
    rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq
      (m := { stack := ⟨#[tf₅]⟩, machine := s₅.machine }) (tf := tf₅) rfl)] at hstep
    simp only [beq_self_eq_true, ↓reduceIte] at hstep
    rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
      (m := { stack := { frames := #[tf₅] }, machine := s₅.machine }) (tf := tf₅) rfl)] at hstep
    have hloc₅ : tf₅.location = .mir ⟨targetBb, 0⟩ := rfl
    rw [hloc₅, hfr.location_eq, frameLocation_beq_false hprog] at hstep
    simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
      stack_currentFrame?_singleton m.stack tf hframes, hframes,
      stack_currentFrame?_singleton (⟨#[tf₅]⟩ : Miri.Interpreter.Stack AnnealProv
        Miri.Interpreter.LocalLayout Unit) tf₅ rfl, Option.map_some, hloc₅, hfr.location_eq,
      option_frameLocation_beq_false hprog, Bool.and_false, Except.map] at hstep
    injection hstep with hm' _
    subst hm'
    intro tf₀ tf' htf₀ htf' j hj
    rw [hframes] at htf₀
    injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
    injection htf' with h₁; injection h₁ with h₁'; subst h₁'
    exact himm₄ j hj

/-- Whole-program `write_bytes` witness that returns the written bytes
(`_0 : u64`, `_1 : u64`, `_2 : *mut u64`, `_3 : ()`):

```text
bb0: _2 = &raw mut _1;
     _3 = write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb1;
bb1: _0 = copy (*_2);
     return
``` -/
def retWriteBytesReadBody : CapturedMir where
  defPath := "lm_4_3_witness::ret_write_bytes_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.u64K,
    WitnessLM4_2.declOf WitnessLM4_2.rawMutU64K, WitnessLM4_2.declOf WitnessLM4_2.unitK]
  basicBlocks := [
    { statements := [WitnessLM4_2.mkStmt42
        (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
      terminator := WitnessLM4_2.mkTerm42 retWriteBytesTerm
      isCleanup := false },
    { statements := [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
        (.use (.copy { local_ := 2, projection := [.deref] })))]
      terminator := WitnessLM4_2.mkTerm42 .return_
      isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- The `ptr4AnnealPre` / `ptr4MiriPre` pre-states of `retWriteBytesReadBody`
(`_1 = 42_u64`, all other locals uninitialized) are `StateRel`-related. -/
theorem retWriteBytesRead_stateRel :
    StateRel retWriteBytesReadBody (WitnessLM4_2.ptr4AnnealPre retWriteBytesReadBody)
      (WitnessLM4_2.ptr4MiriPre retWriteBytesReadBody WitnessLM4_2.u64K) := by
  let b := retWriteBytesReadBody
  refine StateRel.mk (WitnessLM4_2.ptr4MiriFramePre b WitnessLM4_2.u64K) rfl rfl
    ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K), rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [WitnessLM4_2.ptr4AnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [WitnessLM4_2.ptr4MiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
      simpa [b, retWriteBytesReadBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [WitnessLM4_2.ptr4AnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
          layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
      simpa [WitnessLM4_2.ptr4MiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
      (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 4 => simp [retWriteBytesReadBody, get?] at hdecl

/-- **`retWriteBytesRead_trace`**: whole-program run of `retWriteBytesReadBody`,
from `ptr4AnnealPre` / `ptr4MiriPre`, to its root return. Both machines take
four steps in lockstep:

1. `_2 = &raw mut _1`;
2. `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb1`, which fills all
   8 bytes of `_1` with `0xAB` (`0xABAB_ABAB_ABAB_ABAB = 12370169555311111083`);
3. `_0 = copy (*_2)`, which reads the written bytes back through the raw
   pointer;
4. the root-frame `return`, at which Anneal returns the scalar
   `0xABAB_ABAB_ABAB_ABAB` and `lean-miri` returns an immediate related to it
   by `ImmediateRel`.

`retWriteBytesCall_preserves_imm` keeps `_0` and `_2` immediate in
`lean-miri`'s frame across the `write_bytes` call. -/
theorem retWriteBytesRead_trace :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := retWriteBytesReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (WitnessLM4_2.ptr4AnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.u64K) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      StepObsRelLM3_1 b m₃ [entry] (stepMirFn b s₃) (Miri.Interpreter.Step.step hooks () m₃) ∧
      stepMirFn b s₃ = .retNormal (.scalar ⟨0xABABABABABABABAB, 8⟩) s₃.memory ∧
      Miri.Interpreter.Step.step hooks () m₃ = ({ m₃ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₃ = (m₃, .ok (.immediate imm0)) ∧
      ImmediateRel decl0.ty b.layouts (.scalar ⟨0xABABABABABABABAB, 8⟩) imm0 := by
  let b := retWriteBytesReadBody
  have hrel₀ : StateRel b (WitnessLM4_2.ptr4AnnealPre b)
      (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.u64K) := retWriteBytesRead_stateRel
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.u64K).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨WitnessLM4_2.ptr4_all_immediate b _ tf htf 2,
       WitnessLM4_2.ptr4_all_immediate b _ tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  -- Step 1: `_2 = &raw mut _1`.
  let s₁ := WitnessLM4_2.mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (WitnessLM4_2.ptr4AnnealPre b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (WitnessLM4_2.ptr4AnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(WitnessLM4_2.ptr4MiriPre b WitnessLM4_2.u64K).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (WitnessLM4_2.ptr4_all_immediate b _ _ rfl k)
  -- Step 2: `_3 = write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb1`.
  let s₂ := WitnessLM4_2.mkPtrState b 1 0
    [.uninit, .init (.scalar ⟨0xABABABABABABABAB, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hvalOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.u8K 0xAB 1))
        (WitnessLM4_2.tyOf WitnessLM4_2.u8K) :=
    fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.u8_integral WitnessLM4_2.valid1
      (by decide) rfl b rfl tf₁
  have hcountOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.usizeK) :=
    fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₁
  have hsim₂ := call_intrinsic_write_bytes_simulation
    (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u64K)
    hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    WitnessLM4_2.u8_integral hvalOp WitnessLM4_2.usize_integral hcountOp
    rfl WitnessLM4_2.u64_writeBytesPointee
    (fun _ e tgtDecl _ he _ htgt => by
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = WitnessLM4_2.declOf WitnessLM4_2.u64K := Option.some.inj htgt.symm
        subst hd; exact ⟨.u64, WitnessLM4_2.u64_integral⟩)
    (fun ptrVal countSc e tgtDecl tgtKind hp hc _ _ he _ htgt ht _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, WitnessLM4_2.mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨idx, hidx, _⟩
        · injection hcc with hcc'; subst hcc'
          simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = WitnessLM4_2.declOf WitnessLM4_2.u64K := Option.some.inj htgt.symm
        subst hp' hc' hd
        cases ht with
        | int _ hk => cases hk
        | uint ut hk =>
          cases ut <;> try cases hk
          refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
          intro x hx _
          cases hx with
          | tail _ h => cases h
          | head _ => exact Or.inl ⟨rfl, rfl⟩)
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact retWriteBytesCall_preserves_imm (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u64K)
      hrel₁ rfl rfl rfl rfl (Or.inl (by decide)) rfl rfl
      (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
      WitnessLM4_2.u8_integral hvalOp WitnessLM4_2.usize_integral hcountOp rfl hm₂
      tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_0 = copy (*_2)`.
  let s₃ := WitnessLM4_2.mkPtrState b 1 1
    [.init (.scalar ⟨0xABABABABABABABAB, 8⟩), .init (.scalar ⟨0xABABABABABABABAB, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hsim₃ := step_deref_read_simulation_explicit hrel₂ hphase (Or.inl rfl) rfl rfl
    (dstDecl := WitnessLM4_2.declOf WitnessLM4_2.u64K)
    (ptrDecl := WitnessLM4_2.declOf WitnessLM4_2.rawMutU64K) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 0 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
    (fun ptrVal hp e he _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, WitnessLM4_2.mkPtrState, get?] using hp.symm
      subst hp'
      cases he with
      | tail _ h => cases h
      | head _ =>
        refine ⟨rfl, ?_, ?_⟩
        · intro h
          cases h
        · intro decl hd
          have hd' : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := Option.some.inj hd.symm
          subst hd'
          rfl)
  have hnext₃ : derefReadNextAllocMap s₂.frame.locals [entry] 2 = [entry] := rfl
  rw [hs₃, hnext₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_use_preserves hrel₂
    (fun _ h => by simp only [translateOperand, reduceCtorEq] at h) rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → IsImmediateFrameLocal tf₃ 0 := by
    intro tf₃ htf₃
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ 0 (himm₂ tf₂ htf₂ 0 (by decide))
  -- Step 4: root-frame `return` of the scalar in `_0`.
  have hs₄ : stepMirFn b s₃ = .retNormal (.scalar ⟨0xABABABABABABABAB, 8⟩) s₃.memory := rfl
  have hsim₄ := step_terminator_goto_return_lm3_1_simulation hrel₃ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, WitnessLM4_2.declOf WitnessLM4_2.u64K, rfl,
      (fun _ _ h => nomatch h), (by decide), himm₃⟩))
  have hobs₄ := hsim₄.toStepObsRelLM3_1
  rw [hs₄] at hsim₄
  obtain ⟨decl0, imm0, hdecl0, hop, himm, hmret⟩ := retStepRelLM3_1_retNormal_rel hsim₄
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl,
    hs₃, hm₃, hrel₃, hobs₄, hs₄, hmret, hdecl0, hop, himm⟩

/-!
### Whole-program `copy_nonoverlapping` return trace

`retCopyBody` copies `42_u64` from `_1` into `_2` through raw pointers to the
two disjoint locals, reads the copied value back through the destination
pointer into `_0`, and returns it (modeled on
`pass_copy_nonoverlapping_disjoint_locals` of the `miri-diff` corpus):
```text
bb0: _3 = &raw const _1; _4 = &raw mut _2;
     copy_nonoverlapping(copy _3, copy _4, 1_usize); _0 = copy (*_4); return
```
`retCopy_trace` runs Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step` (`annealStepHooks`) in lockstep from the
`StateRel`-related pre-states (`_1 = 42_u64`, `_2 = 99_u64`) through the root
return of the copied `42_u64`.

The certified root return (`step_terminator_goto_return_lm3_1_simulation`)
needs `_0` to stay an immediate `lean-miri` local up to the `return`. The
`copy_nonoverlapping` simulation does not report this, so
`retCopy_copyStep_preserves_imm` proves that `lean-miri`'s
`copy_nonoverlapping` step only re-caches local layouts and writes memory:
every immediate local stays immediate.
-/

/-! ## 1. `lean-miri`'s `copy_nonoverlapping` step keeps immediate locals immediate -/

/-- `RvalueM` actions whose successful runs leave the `lean-miri` call stack
unchanged. -/
def retCopyStackPres {α : Type} (act : Miri.Interpreter.RvalueM AnnealStepState α) : Prop :=
  ∀ st a st', act st = .ok a st' → st'.stack = st.stack

theorem retCopyStackPres_pure {α : Type} (x : α) :
    retCopyStackPres (pure x : Miri.Interpreter.RvalueM AnnealStepState α) := by
  intro st a st' h
  cases h
  rfl

theorem retCopyStackPres_throw {α : Type} (err : Miri.Interpreter.StepError) :
    retCopyStackPres (throw err : Miri.Interpreter.RvalueM AnnealStepState α) := by
  intro _ _ _ h
  cases h

theorem retCopyStackPres_bind {α β : Type}
    {f : Miri.Interpreter.RvalueM AnnealStepState α}
    {g : α → Miri.Interpreter.RvalueM AnnealStepState β}
    (hf : retCopyStackPres f) (hg : ∀ x, retCopyStackPres (g x)) :
    retCopyStackPres (f >>= g) := by
  intro st b st' h
  change EStateM.bind f g st = .ok b st' at h
  unfold EStateM.bind at h
  cases hfm : f st with
  | error _ _ => rw [hfm] at h; cases h
  | ok x st₁ =>
    rw [hfm] at h
    exact (hg x st₁ b st' h).trans (hf st x st₁ hfm)

theorem retCopyStackPres_liftScalarResult {α : Type} (r : Except Miri.Interpreter.StepError α) :
    retCopyStackPres (liftScalarResult r : Miri.Interpreter.RvalueM AnnealStepState α) := by
  cases r with
  | error e => exact retCopyStackPres_throw e
  | ok v => exact retCopyStackPres_pure v

theorem retCopyStackPres_annealReadImmediate_imm (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retCopyStackPres (annealReadImmediate ⟨.immediate imm, lay⟩) := by
  intro st a st' h
  cases imm with
  | scalar sc =>
    have hr : annealReadImmediate ⟨.immediate (.scalar sc), lay⟩ st = .ok ⟨.scalar sc, lay⟩ st :=
      rfl
    rw [hr] at h
    cases h
    rfl
  | scalarPair sc₁ sc₂ =>
    have hr : annealReadImmediate ⟨.immediate (.scalarPair sc₁ sc₂), lay⟩ st =
        .ok ⟨.scalarPair sc₁ sc₂, lay⟩ st := rfl
    rw [hr] at h
    cases h
    rfl
  | uninit =>
    have hr : annealReadImmediate ⟨.immediate .uninit, lay⟩ st =
        .error (.undefinedBehavior "read of uninitialized local") st := rfl
    rw [hr] at h
    cases h

theorem retCopyStackPres_intrinsicScalar_imm (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retCopyStackPres (intrinsicScalar ⟨.immediate imm, lay⟩) := by
  unfold intrinsicScalar
  exact retCopyStackPres_bind (retCopyStackPres_annealReadImmediate_imm imm lay)
    (fun _ => retCopyStackPres_liftScalarResult _)

theorem retCopyStackPres_intrinsicPointer_imm (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retCopyStackPres (intrinsicPointer ⟨.immediate imm, lay⟩) := by
  unfold intrinsicPointer
  exact retCopyStackPres_bind (retCopyStackPres_intrinsicScalar_imm imm lay)
    (fun _ => retCopyStackPres_liftScalarResult _)

theorem retCopyStackPres_intrinsicUsize_imm (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    retCopyStackPres (intrinsicUsize ⟨.immediate imm, lay⟩) := by
  unfold intrinsicUsize
  exact retCopyStackPres_bind (retCopyStackPres_intrinsicScalar_imm imm lay)
    (fun _ => retCopyStackPres_liftScalarResult _)

theorem retCopyStackPres_annealPointeeTypeOf (tyId : Miri.MIR.TyId) :
    retCopyStackPres (annealPointeeTypeOf tyId) := by
  unfold annealPointeeTypeOf
  split
  · exact retCopyStackPres_pure _
  · exact retCopyStackPres_throw _

theorem retCopyStackPres_annealCheckPtrAlign (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (align : Miri.ABI.Align) :
    retCopyStackPres (annealCheckPtrAlign ptr align) := by
  intro st a st' h
  unfold annealCheckPtrAlign at h
  split at h
  · cases h
    rfl
  · cases h
  · cases h

theorem retCopyStackPres_annealMemCopy (source dest : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) (nonoverlapping : Bool) :
    retCopyStackPres (annealMemCopy source dest size nonoverlapping) := by
  intro st a st' h
  unfold annealMemCopy at h
  split at h
  · cases h
    rfl
  · cases h

/-- `annealCopyEval` on immediate operands only writes `lean-miri` memory. -/
theorem retCopyStackPres_annealCopyEval (ly : LayoutTable)
    (imm₁ imm₂ imm₃ : Miri.Interpreter.Immediate AnnealProv)
    (lay₁ lay₂ lay₃ : Miri.Interpreter.LocalLayout) :
    retCopyStackPres
      (annealCopyEval ly ⟨.immediate imm₁, lay₁⟩ ⟨.immediate imm₂, lay₂⟩ ⟨.immediate imm₃, lay₃⟩) := by
  rw [annealCopyEval_eq]
  refine retCopyStackPres_bind (retCopyStackPres_intrinsicUsize_imm _ _) (fun _ => ?_)
  refine retCopyStackPres_bind (retCopyStackPres_annealPointeeTypeOf _) (fun _ => ?_)
  dsimp only
  split
  · refine retCopyStackPres_bind (retCopyStackPres_intrinsicPointer_imm _ _) (fun _ => ?_)
    refine retCopyStackPres_bind (retCopyStackPres_intrinsicPointer_imm _ _) (fun _ => ?_)
    refine retCopyStackPres_bind (retCopyStackPres_annealCheckPtrAlign _ _) (fun _ => ?_)
    refine retCopyStackPres_bind (retCopyStackPres_annealCheckPtrAlign _ _) (fun _ => ?_)
    exact retCopyStackPres_annealMemCopy _ _ _ _
  · exact retCopyStackPres_throw _

/-- `lean-miri`'s action for `copy_nonoverlapping(copy _src, copy _dst, count)`
under `annealStepHooks` (`Intrinsics.evalNondiverging (.CopyNonOverlapping ...)`). -/
def retCopyCopyAction (body : CapturedMir) (srcIdx dstIdx : Local) (countOp : MirAst.Operand) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let source ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨srcIdx, #[]⟩) none
  let dest ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨dstIdx, #[]⟩) none
  let cnt ← annealEvalOperand body.localDecls body.layouts (translateOperand countOp) none
  annealCopyEval body.layouts source dest cnt

theorem retCopy_evalStatement_copy_eq (body : CapturedMir) (srcIdx dstIdx : Local)
    (countOp : MirAst.Operand) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
            span⟩) m =
      Miri.Interpreter.runRvalue (retCopyCopyAction body srcIdx dstIdx countOp) m := rfl

/-- Evaluating a copy of an immediate raw-pointer local either fails or yields an
immediate and changes only the layout cache of the frame. -/
theorem retCopy_rawPtrOperand_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {decl : LocalDecl} {mutability : Mutability} {pk : RigidTy}
    (hdecl : get? body.localDecls idx = some decl)
    (hty : decl.ty.kind = .rawPtr mutability pk)
    (himm : IsImmediateFrameLocal tf idx) :
    (∃ err m₁, annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
      .error err m₁) ∨
    (∃ imm lay tf₁,
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate imm, lay⟩ { m with stack := ⟨#[tf₁]⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf₁]⟩ } allocMap ∧
      ∀ k : Nat, (tf₁.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value) := by
  rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hdecl hty himm with
    ⟨_, m₁, _, h⟩ | ⟨tf₁, _, h, hst, hv⟩ | ⟨_, _, tf₁, _, _, _, h, hst, hv⟩ |
    ⟨_, _, tf₁, _, _, h, hst, hv⟩
  · exact Or.inl ⟨_, m₁, h⟩
  · exact Or.inr ⟨_, _, tf₁, h, hst, hv⟩
  · exact Or.inr ⟨_, _, tf₁, h, hst, hv⟩
  · exact Or.inr ⟨_, _, tf₁, h, hst, hv⟩

/-- Evaluating a well-typed scalar operand either fails or yields an immediate
and changes only the layout cache of the frame. -/
theorem retCopy_scalarOperand_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty) :
    (∃ err m₁, annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
      .error err m₁) ∨
    (∃ imm lay tf₁,
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok ⟨.immediate imm, lay⟩ { m with stack := ⟨#[tf₁]⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf₁]⟩ } allocMap ∧
      ∀ k : Nat, (tf₁.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value) := by
  rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop hprim with
    ⟨m₁, _, _, h⟩ | ⟨tf₁, _, h, hst, hv⟩ | ⟨_, _, tf₁, _, h, hst, _, hv⟩
  · exact Or.inl ⟨_, m₁, h⟩
  · exact Or.inr ⟨_, _, tf₁, h, hst, hv⟩
  · exact Or.inr ⟨_, _, tf₁, h, hst, hv⟩

/-- **`retCopy_copyStep_preserves_imm`**: a successful `lean-miri` step of
`copy_nonoverlapping(copy _src, copy _dst, count)` from a `StateRelLM3_1`-related
state keeps every immediate local of the root frame immediate: operand
evaluation only caches local layouts and `annealCopyEval` only writes memory. -/
theorem retCopy_copyStep_preserves_imm
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {srcPk dstPk : RigidTy}
    {countTy : Ty}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut srcPk)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut dstPk)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hcountPrim : IsPrimScalarTy countTy)
    (hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  intro tf tf' hframes hframes' k hk
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with h₀'
  subst h₀'
  have hact_err : ∀ err st,
      retCopyCopyAction body srcIdx dstIdx countOp m = .error err st → False := by
    intro err st h
    have hev : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
            span⟩) m = (st, .error err) := by
      rw [retCopy_evalStatement_copy_eq]
      unfold Miri.Interpreter.runRvalue
      rw [h]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hev] at hstep
    cases hstep
  rcases retCopy_rawPtrOperand_cases hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes) with
    ⟨err, m₁, h₁⟩ | ⟨imm₁, lay₁, tf₁, h₁, hst₁, hv₁⟩
  · exact (hact_err err m₁ (by unfold retCopyCopyAction; rw [EStateM.bind_eq_error h₁])).elim
  rcases retCopy_rawPtrOperand_cases hst₁ rfl hdstDecl hdstTy
      (IsImmediateFrameLocal.of_values_eq hv₁ (hdstImm tf hframes)) with
    ⟨err, m₂, h₂⟩ | ⟨imm₂, lay₂, tf₂, h₂, hst₂, hv₂⟩
  · exact (hact_err err m₂ (by
      unfold retCopyCopyAction; rw [EStateM.bind_eq_ok h₁, EStateM.bind_eq_error h₂])).elim
  have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
    fun j hj => IsImmediateFrameLocal.of_values_eq hv₂ (IsImmediateFrameLocal.of_values_eq hv₁ hj)
  rcases retCopy_scalarOperand_cases hst₂ rfl ((hcountOp tf hframes).mono_immediate himm₂)
      hcountPrim with
    ⟨err, m₃, h₃⟩ | ⟨imm₃, lay₃, tf₃, h₃, hst₃, hv₃⟩
  · exact (hact_err err m₃ (by
      unfold retCopyCopyAction
      rw [EStateM.bind_eq_ok h₁, EStateM.bind_eq_ok h₂, EStateM.bind_eq_error h₃])).elim
  have hact : retCopyCopyAction body srcIdx dstIdx countOp m =
      annealCopyEval body.layouts ⟨.immediate imm₁, lay₁⟩ ⟨.immediate imm₂, lay₂⟩
        ⟨.immediate imm₃, lay₃⟩ { m with stack := ⟨#[tf₃]⟩ } := by
    unfold retCopyCopyAction
    rw [EStateM.bind_eq_ok h₁, EStateM.bind_eq_ok h₂, EStateM.bind_eq_ok h₃]
  cases hce : annealCopyEval body.layouts ⟨.immediate imm₁, lay₁⟩ ⟨.immediate imm₂, lay₂⟩
      ⟨.immediate imm₃, lay₃⟩ { m with stack := ⟨#[tf₃]⟩ } with
  | error err st => exact (hact_err err st (hact.trans hce)).elim
  | ok u st =>
    cases u
    have hstk : st.stack = ⟨#[tf₃]⟩ :=
      retCopyStackPres_annealCopyEval _ _ _ _ _ _ _ _ () st hce
    obtain ⟨tf₃', hframes₃, _, _, hfr₃, _, _, _, _, _, _, _⟩ := id hst₃
    injection hframes₃ with h₃'
    injection h₃' with h₃''
    subst h₃''
    have hev : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
            span⟩) m = (st, .ok ()) := by
      rw [retCopy_evalStatement_copy_eq]
      unfold Miri.Interpreter.runRvalue
      rw [hact, hce]
    have hst_frames : st.stack.frames = #[tf₃] := by rw [hstk]
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hev hst_frames
      hfr₃.location_eq] at hstep
    injection hstep with hm' _
    subst hm'
    injection hframes' with h'
    injection h' with h''
    subst h''
    exact IsImmediateFrameLocal.of_values_eq hv₃ (himm₂ k hk)

/-! ## 2. Body and pre-states -/

/-- `_0 : u64`, `_1 : u64`, `_2 : u64`, `_3 : *const u64`, `_4 : *mut u64`:
```text
bb0: _3 = &raw const _1; _4 = &raw mut _2;
     copy_nonoverlapping(copy _3, copy _4, 1_usize); _0 = copy (*_4); return
``` -/
def retCopyBody : CapturedMir where
  defPath := "miri_diff_witness::ret_copy"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.u64K,
    WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.rawConstU64K,
    WitnessLM4_2.declOf WitnessLM4_2.rawMutU64K]
  basicBlocks := [
    { statements := [
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 3) (.rawPtr .not (WitnessLM4_2.local42 1))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 4) (.rawPtr .mut (WitnessLM4_2.local42 2))),
        WitnessLM4_2.copyStmt 3 4 1,
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
          (.use (.copy { local_ := 4, projection := [.deref] })))]
      terminator := WitnessLM4_2.mkTerm42 .return_
      isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state of `retCopyBody`: `_1 = 42_u64`, `_2 = 99_u64`, and all other
locals `.uninit`. -/
def retCopyAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .uninit, .uninit] }
    memory := (initMachineState retCopyBody []).memory }

/-- `lean-miri` root frame matching `retCopyAnnealPre`. -/
def retCopyMiriFramePre : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody retCopyBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K))
      (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` pre-state of `retCopyBody`. -/
def retCopyMiriPre : AnnealStepState :=
  { stack := ⟨#[retCopyMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem retCopy_all_immediate :
    ∀ tf, retCopyMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁
  injection h₁ with h₂
  subst h₂
  match k with
  | 0 | 1 | 2 | 3 | 4 => simp [retCopyMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 5 => simp [retCopyMiriFramePre] at hmls

theorem retCopy_stateRel : StateRel retCopyBody retCopyAnnealPre retCopyMiriPre := by
  refine StateRel.mk retCopyMiriFramePre rfl rfl
    ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K), rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 3 | 4 =>
    have hs : slot = .uninit := by simpa [retCopyAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [retCopyMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
      simpa [retCopyBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [retCopyAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
          layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
      simpa [retCopyMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
      (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
      simpa [retCopyBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨99, 8⟩) := by
      simpa [retCopyAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))),
          layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
      simpa [retCopyMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
      (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel99 rfl
        (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 5 => simp [retCopyBody, get?] at hdecl

/-! ## 3. The lockstep trace through the root return -/

/-- **`retCopy_trace`**: real 5-step lockstep execution of `retCopyBody` from the
`StateRel`-related pre-states (`_1 = 42_u64`, `_2 = 99_u64`):
1. `_3 = &raw const _1` promotes `_1` into `lm31AllocId1`;
2. `_4 = &raw mut _2` promotes `_2` into `lm31AllocId2`;
3. `copy_nonoverlapping(copy _3, copy _4, 1_usize)` copies `42_u64` into `_2`
   (Anneal's `_2` and `lm31AllocId2` in `lean-miri`'s live memory both hold
   `42_u64`);
4. `_0 = copy (*_4)` reads the copied `42_u64` back through the destination
   pointer;
5. `return` pops the root frame in both machines, returning `42_u64` with
   `ImmediateRel`-related return values. -/
theorem retCopy_trace :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := retCopyBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
      stepMirFn b retCopyAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () retCopyMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₂, e₁] ∧
      get? s₃.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩)) ∧
      (∃ la msc,
        m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
          some (Witness.lm31AllocId2, la) ∧
        ScalarRel ⟨42, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [e₂, e₁] ∧
      stepMirFn b s₄ = .retNormal (.scalar ⟨42, 8⟩) s₄.memory ∧
      Miri.Interpreter.Step.step hooks () m₄ = ({ m₄ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₄ = (m₄, .ok (.immediate imm0)) ∧
      ImmediateRel decl0.ty b.layouts (.scalar ⟨42, 8⟩) imm0 := by
  let b := retCopyBody
  have hrel₀ : StateRel b retCopyAnnealPre retCopyMiriPre := retCopy_stateRel
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  have himm₀ : ∀ tf, retCopyMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨retCopy_all_immediate tf htf 3, retCopy_all_immediate tf htf 1⟩
  -- Step 1: `_3 = &raw const _1`
  let s₁ := WitnessLM4_2.mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b retCopyAnnealPre = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : retCopyAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨retCopyMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (retCopy_all_immediate _ rfl k)
  -- Step 2: `_4 = &raw mut _2`
  let s₂ := WitnessLM4_2.mkPtrState b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  have hsim₂ := step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
  rw [hs₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := hsim₂.miri_step_of_anneal_step
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; decide) (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  -- Step 3: `copy_nonoverlapping(copy _3, copy _4, 1_usize)`
  let s₃ := WitnessLM4_2.mkPtrState b 0 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hcount₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      WellTypedScalarOperand b tf₂
        (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.usizeK) :=
    fun tf₂ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₂
  have hsim₃ := step_intrinsic_copyNonOverlapping_simulation_explicit
    (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u64K)
    hrel₂ hphase rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide) (by decide))
    rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 4 (by decide) (by decide))
    WitnessLM4_2.usize_integral hcount₂ WitnessLM4_2.u64_copyPointee
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d _
      have hs_ty : decl_s = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · exact Option.some.inj hd_s.symm
        · rcases List.mem_cons.mp he' with rfl | h
          · exact Option.some.inj hd_s.symm
          · cases h
      have hd_ty : decl_d = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · exact Option.some.inj hd_d.symm
        · rcases List.mem_cons.mp he' with rfl | h
          · exact Option.some.inj hd_d.symm
          · cases h
      subst hs_ty hd_ty; exact Or.inr ⟨rfl, rfl⟩)
    (by
      intro srcPtr dstPtr _ e_s e_d _ _ _ _ hsrc hdst _ _ _ he_s het_s he_d het_d _ _ _ _ _ _ _ _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, WitnessLM4_2.mkPtrState, ptr1, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₂, WitnessLM4_2.mkPtrState, ptr2, get?] using hdst.symm
      subst hpS hpD
      have hes : e_s = e₁ := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · cases het_s
        · rcases List.mem_cons.mp he' with rfl | h
          · rfl
          · cases h
      have hed : e_d = e₂ := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het_d
          · cases h
      subst hes hed
      exact ⟨by nofun, Or.inl rfl,
        by simp [s₂, WitnessLM4_2.mkPtrState, e₁, rawPtrAllocMapEntry, get?],
        Or.inr (by simp [s₂, WitnessLM4_2.mkPtrState, e₂, rawPtrAllocMapEntry, get?])⟩)
  rw [hs₃] at hsim₃
  have hmap_eq : copyNextAllocMap s₂.frame.locals [e₂, e₁] 4
      (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8)) 8 = [e₂, e₁] := rfl
  rw [hmap_eq] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  -- `readScalar = 42_u64` from `lm31AllocId2` in `m₃.machine.memory.live`.
  have hmem₂ : ∃ la msc,
      m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
        some (Witness.lm31AllocId2, la) ∧
      ScalarRel ⟨42, 8⟩ msc ∧
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
        .ok (.fromScalarInt msc) := by
    obtain ⟨tf₃, htf₃, _, _, hfr₃, _, _, _, _, _, halloc₃, _⟩ := id hrel₃
    obtain ⟨slot₂, mls₂, _, _, hslot₂, hmls₂, _, hloc₂⟩ :=
      hfr₃.lookup_local (idx := 2) (decl := WitnessLM4_2.declOf WitnessLM4_2.u64K) rfl
    have hsl₂ : slot₂ = .init (.scalar ⟨42, 8⟩) := by
      simpa [s₃, WitnessLM4_2.mkPtrState, get?] using hslot₂.symm
    subst hsl₂
    obtain ⟨⟨lay₂, hlay₂⟩, _, hshape_fn₂⟩ :=
      (halloc₃.local_alloc_sync tf₃ htf₃ e₂ (.head _)).1 _ hslot₂ (by nofun)
    obtain ⟨la₂, hfind₂, _, _, _⟩ := hshape_fn₂ (WitnessLM4_2.declOf WitnessLM4_2.u64K) rfl
    have hmls₂_eq : mls₂ = ⟨.live (.indirect (stackAllocPlace e₂.allocId)), lay₂⟩ := by
      change tf₃.locals[2]? = _ at hlay₂; rw [hlay₂] at hmls₂; exact Option.some.inj hmls₂.symm
    obtain ⟨_, hsc_spec⟩ := hloc₂.indirect_stackAllocPlace_spec hmls₂_eq
      (halloc₃.base_addr_valid e₂ (.head _)).2.2 hfind₂
      (halloc₃.live_key_unique e₂ (.head _)) (by decide)
    obtain ⟨_, _, _, msc, hrel_sc, hread⟩ := hsc_spec ⟨42, 8⟩ rfl
    exact ⟨la₂, msc, hfind₂, hrel_sc, hread⟩
  -- Every local other than the promoted `_1` and `_2` stays immediate across the copy.
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hk₁ hk₂
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact retCopy_copyStep_preserves_imm hrel₂ (srcIdx := 3) (dstIdx := 4) rfl rfl rfl rfl
      (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide) (by decide)) rfl rfl
      (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 4 (by decide) (by decide))
      hcount₂ WitnessLM4_2.usize_integral.prim hm₃ tf₂ tf₃ htf₂ htf₃ k
      (himm₂ tf₂ htf₂ k hk₁ hk₂)
  -- Step 4: `_0 = copy (*_4)`
  let s₄ := WitnessLM4_2.mkPtrState b 0 4
    [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr1,
      .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have hsim₄ := step_deref_read_simulation_explicit hrel₃ hphase
    (opKind := MirAst.Operand.copy) (Or.inl rfl) rfl (dstIdx := 0) (ptrIdx := 4) rfl rfl rfl rfl
    WitnessLM4_2.u64_integral.prim
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 0 (by decide) (by decide),
      himm₃ tf₃ htf₃ 4 (by decide) (by decide)⟩)
    (by
      intro ptrVal hptr e he het _
      have hp : ptrVal = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₃, WitnessLM4_2.mkPtrState, ptr2, get?] using hptr.symm
      subst hp
      have he₂ : e = e₂ := by
        rcases List.mem_cons.mp he with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het
          · cases h
      subst he₂
      refine ⟨rfl, by nofun, fun decl hdecl => ?_⟩
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := Option.some.inj hdecl.symm
      subst hd
      rfl)
  rw [hs₄] at hsim₄
  have hmap₄ : derefReadNextAllocMap s₃.frame.locals [e₂, e₁] 4 = [e₂, e₁] := rfl
  rw [hmap₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_use_preserves hrel₃ (by rintro _ ⟨⟩) rfl rfl hm₄
  have himm₄_0 : ∀ tf₄, m₄.stack.frames = #[tf₄] → IsImmediateFrameLocal tf₄ 0 := by
    intro tf₄ htf₄
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ 0 (himm₃ tf₃ htf₃ 0 (by decide) (by decide))
  -- Step 5: root `return` of `_0 = 42_u64`
  have hsim₅ := step_terminator_goto_return_lm3_1_simulation hrel₄ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, WitnessLM4_2.declOf WitnessLM4_2.u64K, rfl, (by rintro _ _ ⟨⟩),
      (by decide), himm₄_0⟩))
  have hret : stepMirFn b s₄ = .retNormal (.scalar ⟨42, 8⟩) s₄.memory := rfl
  rw [hret] at hsim₅
  generalize hm_res : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₄ =
    mRes at hsim₅
  cases hsim₅ with
  | retRoot decl0 _ imm0 _ m' hdecl0 hop0 himm0 hm' =>
    subst hm'
    exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂,
      hs₃, hm₃, hrel₃, rfl, hmem₂, hs₄, hm₄, hrel₄, hret, hm_res, hdecl0, hop0, himm0⟩

/-! ### Checked addition: whole-program safety equivalence for the checked-addition witness
`checkedAddBody rhs` (for every `rhs < 65536`) through a body-specific
`StepClosedSim`: the closed invariant `ScalarFragmentInv` is strengthened with
the shape of the `(u16, bool)` local `_1` at the two program points that read
its fields. -/

/-! ### Reading a field of an immediate scalar pair -/

/-- Reading field `0` or `1` of an immediate scalar-pair local (with any cached
layout consistent with its declaration): Anneal returns the component and leaves
the locals unchanged; `lean-miri` returns the matching scalar after caching the
local's layout. -/
theorem pairField_read_simulation
    {body : CapturedMir} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {idx : Local} {decl : LocalDecl}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine af topFrame)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl : get? body.localDecls idx = some decl)
    (sc0 sc1 : MirAst.ScalarInt) (msc0 msc1 : Miri.Memory.ScalarInt)
    (hls : get? af.locals idx = some (LocalSlot.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
    {cl : Option Miri.Interpreter.LocalLayout}
    (hloc : topFrame.locals[idx]? = some
      ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
         layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (hcl : ∀ l ∈ cl, l = translateTy decl.ty body.layouts)
    (fidx : Nat) (fty : Ty)
    (hfidx : (fidx = 0 ∧ sc0.sizeBytes ≠ 0) ∨ (fidx = 1 ∧ sc1.sizeBytes ≠ 0))
    (hfty : fty = if fidx = 0 then
      { kind := (match decl.ty.kind with | .tuple (t::_) => t | _ => .tuple []), layoutIdx := 0 }
      else { kind := .bool, layoutIdx := 0 }) :
    let op := Operand.copy ⟨idx, [ProjectionElem.field fidx fty]⟩
    evalOperand af.locals op [] globals body.layouts =
      .ok (.scalar (if fidx = 0 then sc0 else sc1)) af.locals ∧
    ∃ hlt : idx < topFrame.locals.size,
      let topFrame' := cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      FrameRel body m.machine af topFrame' ∧
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m) =
        EStateM.Result.ok
          { imm := .scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1)),
            layout := ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩ }
          { m with stack := ⟨#[topFrame']⟩ } := by
  intro op
  obtain ⟨hlt, h_get⟩ := array_get_some_exists _ _ _ hloc
  have hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    intro l' hl'
    rw [h_get] at hl'
    exact hcl l' hl'
  constructor
  · dsimp only [op, evalOperand]
    rw [hls]
    dsimp only [readProjectedValue, List.brecOn, List.below]
    rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rfl
    · rfl
  · refine ⟨hlt, ?_, ?_, ?_⟩
    · intro j hj
      exact hj.cache_layout hlt _
    · exact hframe.cache_local_layout hdecl hlt
    · have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache
      have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
      rw [h_get] at hget_c
      have hgop := frame_getLocalOperand_live _ hget_c
      have hm_op : annealEvalOperand body.localDecls body.layouts (translateOperand op) known m =
          .ok ⟨.immediate (.scalar (.fromScalarInt (if fidx = 0 then msc0 else msc1))),
            ⟨encodeTyId fty, (translateTy decl.ty body.layouts).layout⟩⟩
            { m with stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
              (translateTy decl.ty body.layouts)]⟩ } := by
        with_unfolding_all
          unfold annealEvalOperand
          rcases hfidx with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map,
              encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
              EStateM.get, Bind.bind, EStateM.bind, Pure.pure,
              stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres,
              hgop, beq_self_eq_true]
            rfl
          · simp only [op, translateOperand, translatePlace, translateProjectionElem, List.map,
              encodeTyId, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
              EStateM.get, Bind.bind, EStateM.bind, Pure.pure,
              stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some, hres,
              hgop]
            rfl
      rw [EStateM.bind_eq_ok hm_op]
      unfold annealReadImmediate
      rfl

/-- `readAssertCondition` on an operand whose immediate read yields a `bool`
scalar returns the scalar's truth value. -/
theorem readAssertCondition_of_read
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Miri.MIR.Operand} {m m' : AnnealStepState}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {lay : Miri.ABI.TyAndLayout Miri.MIR.TyId}
    (hread : (annealEvalOperand localDecls layouts op none >>= annealReadImmediate) m =
      .ok ⟨.scalar (.fromScalarInt msc), lay⟩ m')
    (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = 1) (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    (annealTerminatorHooks localDecls layouts).readAssertCondition () op m =
      (m', .ok (decide (sc.bits ≠ 0))) := by
  dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
  unfold Miri.Interpreter.runRvalue
  rw [EStateM.bind_assoc_apply]
  rw [EStateM.bind_eq_ok hread]
  have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
    rw [hrel.size_eq, hsz]
    rfl
  have hmsc_data_eq : msc.data = sc.bits := hrel.data_eq
  rcases msc with ⟨msc_data, msc_size⟩
  subst hmsc_sz
  rcases hbits with h0 | h1
  · rw [h0] at hmsc_data_eq ⊢
    subst hmsc_data_eq
    dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
      Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
      Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
      Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
      Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
    rfl
  · rw [h1] at hmsc_data_eq ⊢
    subst hmsc_data_eq
    dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
      Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
      Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
      Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
      Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
    rfl

/-- The `lean-miri` side of an immediate `(T, bool)` local whose Anneal slot holds
an initialized scalar pair: an immediate `.scalarPair` with `ScalarRel`-related
components (the flag a `bool` scalar). -/
theorem pairLocal_miri_shape
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframe : FrameRel body mach af topFrame)
    {p : Local} {decl : LocalDecl} {t0 : RigidTy}
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_p : IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? af.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) :
    ∃ (msc0 msc1 : Miri.Memory.ScalarInt) (cl : Option Miri.Interpreter.LocalLayout),
      topFrame.locals[p]? = some
        ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
           layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) ∧
      (∀ l ∈ cl, l = translateTy decl.ty body.layouts) ∧
      ScalarRel sc0 msc0 ∧ ScalarRel sc1 msc1 ∧
      sc1.sizeBytes = 1 ∧ (sc1.bits = 0 ∨ sc1.bits = 1) := by
  obtain ⟨slot, mls, _, _, hslot, hmls, _, hlocrel⟩ := hframe.lookup_local hdecl
  rw [hls] at hslot
  injection hslot with hslot
  subst hslot
  cases hlocrel with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_p _ hmls mp)
  | immediate _ imm cl hcl hval =>
    rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
    · cases h
    · injection hv with hv
      subst hv
      cases himmRel with
      | scalarPair _ _ msc0 msc1 hrel0 hrel1 _ hbool2 =>
        obtain ⟨hsz1, hbits1⟩ := hbool2 t0 hpair
        exact ⟨msc0, msc1, cl, hmls, hcl, hrel0, hrel1, hsz1, hbits1⟩

/-- `Assert (copy (_p.1)) expected target unreachable` on the `bool` flag of an
initialized immediate `(T, bool)` local: both machines report UB (a failed
assertion), or both continue at `target` in `StateRel`-related states whose
`lean-miri` frame keeps every immediate local immediate; Anneal's locals are
unchanged. -/
theorem assert_pairFlag_step_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {p : Local} {decl : LocalDecl} {t0 : RigidTy} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind =
      .assert (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩) expected target
        .unreachable)
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_p : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? s.frame.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) :
    (∃ m' msg, stepMirFn body s = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg))) ∨
    (∃ (topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      m.stack.frames = #[topFrame] ∧
      stepMirFn body s =
        .step { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } } ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        ({ m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ }, .ok true) ∧
      StateRel body { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } }
        { m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ } ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  have hA := stepMirFn_at_terminator (body := body) hcal hphase hbb hstmt_none hstmt_len
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
          expected
          (.BoundsCheck
            (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
            (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)))
          target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  obtain ⟨msc0, msc1, cl, hloc, hcl, hrel0, hrel1, hsz1, hbits1⟩ :=
    pairLocal_miri_shape hframe hdecl hpair (himm_p topFrame hframes) hls
  obtain ⟨h_a, hlt, hmono, hframe', hread⟩ :=
    pairField_read_simulation hframes hframe s.memory.globals none hdecl sc0 sc1 msc0 msc1 hls hloc
      hcl 1 { kind := .bool, layoutIdx := 0 } (Or.inr ⟨rfl, by omega⟩) rfl
  have h_a' : evalOperand s.frame.locals (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)
      [] s.memory.globals body.layouts = .ok (.scalar sc1) s.frame.locals := h_a
  have hread' : (annealEvalOperand body.localDecls body.layouts
      (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)) none >>=
        annealReadImmediate) m =
      .ok ⟨.scalar (.fromScalarInt msc1),
        ⟨encodeTyId { kind := .bool, layoutIdx := 0 }, (translateTy decl.ty body.layouts).layout⟩⟩
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame p hlt
          (translateTy decl.ty body.layouts)]⟩ } := hread
  have h_m := readAssertCondition_of_read hread' hrel1 hsz1 hbits1
  have hM := evalTerminator_assert_ok (annealTerminatorHooks body.localDecls body.layouts) ()
    defaultSourceInfo (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
    expected
    (.BoundsCheck (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩))
      (translateOperand (.copy ⟨p, [.field 1 { kind := .bool, layoutIdx := 0 }]⟩)))
    target .Unreachable m _ _ rfl h_m
  rw [← hm_term] at hM
  by_cases h_match : (expected == decide (sc1.bits ≠ 0)) = true
  · simp only [h_match, ↓reduceIte] at hM
    have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      (m' := { m with stack := ⟨#[{ cacheFrameLocalLayout topFrame p hlt
        (translateTy decl.ty body.layouts) with location := .mir ⟨target, 0⟩ }]⟩ })
      (r := .ok ())
      (by
        rw [hM]
        unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
        rw [stack_currentFrame?_singleton _
          (cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts)) rfl]
        rfl)
    have hA' : evalTerminator s bb.terminator (some body) =
        MirStepNode.step
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } } := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, h_a']
      dsimp only
      split
      · rfl
      · next h_contra =>
        rcases hbits1 with h0 | h1
        · revert h_match h_contra; simp only [h0]; intros; cases expected <;> contradiction
        · revert h_match h_contra; simp only [h1]; intros; cases expected <;> contradiction
    exact Or.inr ⟨topFrame, cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts),
      hframes, hA.trans hA', hM',
      StateRel.mk { cacheFrameLocalLayout topFrame p hlt (translateTy decl.ty body.layouts) with
          location := .mir ⟨target, 0⟩ } rfl hretCont ⟨retLay, hretPlace⟩
        ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
        hcal hstack hbor hprot hcaller (memoryAllocDisjoint_cache_layout hd_tf hlt _),
      hmono⟩
  · have h_if : (expected == decide (sc1.bits ≠ 0)) = false := by
      revert h_match; cases (expected == decide (sc1.bits ≠ 0)) <;> decide
    simp only [h_if, Bool.false_eq_true, ↓reduceIte] at hM
    have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      hM
    have hA' : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, h_a']
      dsimp only
      split
      · next h_contra =>
        rcases hbits1 with h0 | h1
        · revert h_if h_contra; simp only [h0]; intros; cases expected <;> contradiction
        · revert h_if h_contra; simp only [h1]; intros; cases expected <;> contradiction
      · rfl
    exact Or.inl ⟨_, "assert panic", hA.trans hA', hM'⟩

/-- `_d = copy (_p.0)` from an initialized immediate `(T, bool)` local `_p` into a
distinct immediate local `_d` whose layout fits the component: simulation
together with frame-immediacy preservation. -/
theorem step_assign_pairField0_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    {dstIdx p : Local} {dstDecl decl : LocalDecl} {t0 : RigidTy}
    (hkind : stmt.kind =
      .assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)))
    (hne : p ≠ dstIdx)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl : get? body.localDecls p = some decl)
    (hpair : decl.ty.kind = .tuple [t0, .bool])
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (himm_p : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame p)
    {sc0 sc1 : MirAst.ScalarInt}
    (hls : get? s.frame.locals p = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))
    (hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc0.sizeBytes)
    (hbool_dst : dstDecl.ty.kind = .bool → sc0.sizeBytes = 1 ∧ (sc0.bits = 0 ∨ sc0.bits = 1))
    (hchar_dst : dstDecl.ty.kind = .char → sc0.sizeBytes = 4 ∧ isValidCharCode sc0.bits = true) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
            .ok true →
          IsImmediateFrameLocal tf' j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  suffices StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ j, IsImmediateFrameLocal topFrame j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
          #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
          .ok true →
        IsImmediateFrameLocal tf' j) by
    refine ⟨this.1, fun tf₀ htf₀ j hj tf' htf' hok => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact this.2 j hj tf' htf' hok
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨msc0, msc1, cl, hloc, hcl, hrel0, _, _, _⟩ :=
    pairLocal_miri_shape hframe hdecl hpair (himm_p topFrame hframes) hls
  obtain ⟨_, mls_dst0, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := memoryAllocDisjoint_cache_layout hd_tf hlt_dst0 _
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_eq0]; exact hloc_dst0.layout_eq
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
  have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_dst hlt_dst0
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun _ hj => hj.cache_layout hlt_dst0 _
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  have hloc₀ : topFrame₀.locals[p]? = some
      ({ value := .live (.immediate (.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1))),
         layout := cl } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ (Ne.symm hne)]
    exact hloc
  obtain ⟨h_a, hlt_p, hmono₁, hframe₁, hread⟩ :=
    pairField_read_simulation (m := m₀) rfl hframe₀ s.memory.globals
      (some (translateTy dstDecl.ty body.layouts)) hdecl sc0 sc1 msc0 msc1 hls hloc₀ hcl
      0 { kind := t0, layoutIdx := 0 } (Or.inl ⟨rfl, hrel0.sizeBytes_ne_zero⟩)
      (by rw [hpair]; rfl)
  have h_a' : evalOperand s.frame.locals (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)
      [] s.memory.globals body.layouts = .ok (.scalar sc0) s.frame.locals := h_a
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ p hlt_p (translateTy decl.ty body.layouts)
  have hread' : (annealEvalOperand body.localDecls body.layouts
      (translateOperand (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩))
      (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
      .ok ⟨.scalar (.fromScalarInt msc0),
        ⟨encodeTyId { kind := t0, layoutIdx := 0 }, (translateTy decl.ty body.layouts).layout⟩⟩
        { m with stack := ⟨#[topFrame₁]⟩ } := hread
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperand body.localDecls body.layouts
            (translateOperand (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩))
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
          fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
    rw [EStateM.bind_eq_ok hevalPlace_dst]
    exact EStateM.bind_assoc_apply _ _ _ m₀
  have ha_ok : evalStmt s stmt body.localDecls body.layouts =
      match get? s.frame.locals dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals dstIdx (.init (.scalar sc0)) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub := by
    unfold evalStmt; rw [hkind]; dsimp only
    have huse : evalRvalue s.frame.locals
        (.use (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)) s.memory
        body.localDecls body.layouts = .ok (.scalar sc0) s.frame.locals s.memory := by
      unfold evalRvalue
      dsimp only
      rw [hbor, hcaller, h_a']
    rw [huse]
    dsimp only
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]; rfl
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc0)) destPlace)
        { m with stack := ⟨#[topFrame₁]⟩ } := by
    rw [hm_eval]
    apply runRvalue_eq_of_eq
    exact EStateM.bind_eq_ok hread'
  have himmRel' : ImmediateRel dstDecl.ty body.layouts (.scalar sc0) (.scalar (.fromScalarInt msc0)) :=
    .scalar sc0 msc0 hrel0 hsz_dst hbool_dst hchar_dst
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ := memoryAllocDisjoint_cache_layout hdisj₀ hlt_p _
  exact write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
    hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
    hframes hframe.body_eq hframe.location_eq (fun j hj => hmono₁ j (hmono₀ j hj))
    hbb hstmt hframe₁ hdisj₁ hdecl_dst
    (hmono₁ dstIdx (hmono₀ dstIdx (himm_dst topFrame hframes))) himmRel' ha_ok hm_write

/-! ### Body-specific closed invariant for `checkedAddBody` -/

/-- `bb0` of `checkedAddBody rhs`. -/
def checkedAddBb0 (rhs : Nat) : BasicBlockData :=
  blk [st (.storageLive 1),
      st (.assign (pl 1) (.binaryOp .addWithOverflow (.constant (Witness.constU16 65500))
        (.constant (Witness.constU16 rhs))))]
    (.assert (.copy { local_ := 1, projection := [.field 1 Witness.boolTy] }) false 1 .unreachable)

/-- `bb1` of `checkedAddBody rhs`. -/
def checkedAddBb1 : BasicBlockData :=
  blk [st (.assign (pl 0) (.use (.copy { local_ := 1, projection := [.field 0 Witness.u16Ty] }))),
      st (.storageDead 1)] .return_

theorem checkedAdd_blocks (rhs : Nat) :
    (checkedAddBody rhs).basicBlocks = [checkedAddBb0 rhs, checkedAddBb1] := rfl

/-- Shape of `_1` at the two program points of `checkedAddBody` that read its
fields (`bb0`'s `Assert` and `bb1[0]`): an initialized pair whose first
component is a 2-byte scalar. `ImmediateRel` alone does not pin that width. -/
def CheckedAddShape (s : MachineState) : Prop :=
  ((s.frame.blockIdx = 0 ∧ s.frame.stmtIdx = 2) ∨ (s.frame.blockIdx = 1 ∧ s.frame.stmtIdx = 0)) →
    ∃ sc0 sc1 : MirAst.ScalarInt,
      get? s.frame.locals 1 = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
      sc0.sizeBytes = 2

/-- The closed invariant for `checkedAddBody`: the `LM-1.1` invariant plus the
shape of `_1` where its fields are read. -/
def CheckedAddInv (rhs : Nat) (s : MachineState) (m : AnnealStepState) : Prop :=
  ScalarFragmentInv (checkedAddBody rhs) (fun _ => True) s m ∧ CheckedAddShape s

theorem checkedAdd_phase (rhs : Nat) : ∀ p, (checkedAddBody rhs).phase ≠ .other p := by
  intro p h
  simp [checkedAddBody, mkBody] at h

theorem get?_of_set?_eq_some {α : Type} {l l' : List α} {i : Nat} {v : α}
    (h : set? l i v = some l') : get? l' i = some v := by
  unfold set? at h
  split at h
  · next hlt =>
    injection h with h
    subst h
    rw [get?_eq_getElem?, List.getElem?_set_self hlt]
  · cases h

/-- After `_1 = AddWithOverflow(const 65500_u16, const rhs_u16)` the slot of
`_1` holds a pair whose first component is a 2-byte scalar. -/
theorem checkedAdd_add_shape {rhs : Nat} {s s' : MachineState}
    (hcal : s.memory.activeCallee = none) (hbor : s.memory.borrows = [])
    (hprot : s.memory.activeProtectors = []) (hcaller : s.memory.callerLocals = [])
    (hb : s.frame.blockIdx = 0) (hi : s.frame.stmtIdx = 1)
    (hstep : stepMirFn (checkedAddBody rhs) s = .step s') :
    ∃ sc0 sc1 : MirAst.ScalarInt,
      get? s'.frame.locals 1 = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
      sc0.sizeBytes = 2 := by
  rw [stepMirFn_eq_of_not_other _ s hcal (checkedAdd_phase rhs), hb, hi] at hstep
  obtain ⟨sc0, sc1, hrv, hsz⟩ : ∃ sc0 sc1 : MirAst.ScalarInt,
      evalRvalue s.frame.locals
        (.binaryOp .addWithOverflow (.constant (Witness.constU16 65500))
          (.constant (Witness.constU16 rhs))) s.memory
        (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts =
        .ok (.aggregate 0 [.scalar sc0, .scalar sc1]) s.frame.locals s.memory ∧
      sc0.sizeBytes = 2 := by
    apply Exists.intro
    apply Exists.intro
    constructor
    · unfold evalRvalue
      rw [hbor, hcaller]
      rfl
    · rfl
  change evalStmt s (st (.assign (pl 1) (.binaryOp .addWithOverflow
      (.constant (Witness.constU16 65500)) (.constant (Witness.constU16 rhs)))))
      (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts = .step s' at hstep
  unfold evalStmt at hstep
  dsimp only [st, pl] at hstep
  rw [hrv] at hstep
  dsimp only at hstep
  revert hstep
  rw [hprot]
  cases hget : get? s.frame.locals 1 with
  | none => intro h; exact absurd h MirStepNode_fail_ne_step
  | some slot =>
    cases slot with
    | dead => intro h; exact absurd h MirStepNode_fail_ne_step
    | uninit =>
      dsimp only
      cases hset : set? s.frame.locals 1 (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) with
      | none => intro h; exact absurd h MirStepNode_fail_ne_step
      | some locals₂ =>
        intro h
        have h' := MirStepNode_step_inj h
        subst h'
        exact ⟨sc0, sc1, get?_of_set?_eq_some hset, hsz⟩
    | init _ =>
      dsimp only
      cases hset : set? s.frame.locals 1 (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) with
      | none => intro h; exact absurd h MirStepNode_fail_ne_step
      | some locals₂ =>
        intro h
        have h' := MirStepNode_step_inj h
        subst h'
        exact ⟨sc0, sc1, get?_of_set?_eq_some hset, hsz⟩

/-- Statement steps of `checkedAddBody` advance the statement index. -/
theorem checkedAdd_stmt_location {rhs : Nat} {s s' : MachineState} {bb : BasicBlockData}
    {stmt : Statement}
    (hcal : s.memory.activeCallee = none)
    (hbb : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hk : stmt.kind = .nop ∨ (∃ l, stmt.kind = .storageLive l) ∨
      (∃ l, stmt.kind = .storageDead l) ∨ (∃ dstIdx rv, stmt.kind = .assign ⟨dstIdx, .nil⟩ rv))
    (hs : stepMirFn (checkedAddBody rhs) s = .step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  rw [stepMirFn_eq_of_not_other _ s hcal (checkedAdd_phase rhs)] at hs
  simp only [hbb, hstmt] at hs
  exact evalStmt_step_location hk hs

/-- `NonAddrTakenImmediate` after a continuing step, from frame-immediacy
preservation. -/
theorem nonAddrTakenImmediate_of_pres {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {m m' : AnnealStepState} {r : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hframes_ex : ∃ tf, m.stack.frames = #[tf])
    (himm : NonAddrTakenImmediate body nonAddrTaken m)
    (hpres : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf', r.1.stack.frames = #[tf'] → r.2 = .ok true → IsImmediateFrameLocal tf' j)
    (hr : r = (m', .ok true)) :
    NonAddrTakenImmediate body nonAddrTaken m' := by
  intro tf' htf' idx decl hdecl hna
  obtain ⟨tf, htf⟩ := hframes_ex
  subst hr
  exact hpres tf htf idx (himm tf htf idx decl hdecl hna) tf' htf' rfl

/-- Lift a `StepRel` of `checkedAddBody` to `Lockstep` for `CheckedAddInv`. -/
theorem checkedAdd_lockstep_of_stepRel {rhs : Nat} {s : MachineState} {m : AnnealStepState}
    (hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
      (Miri.Interpreter.Step.step
        (annealStepHooks (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts) () m))
    (hnext : ∀ s' m', stepMirFn (checkedAddBody rhs) s = .step s' →
      Miri.Interpreter.Step.step
        (annealStepHooks (checkedAddBody rhs).localDecls (checkedAddBody rhs).layouts) () m =
          (m', .ok true) →
      ValidFrameLocation (checkedAddBody rhs) s'.frame ∧ CheckedAddShape s' ∧
        NonAddrTakenImmediate (checkedAddBody rhs) (fun _ => True) m') :
    Lockstep (annealMiriHooks (checkedAddBody rhs)) (CheckedAddInv rhs)
      (ImmediateRetRel (checkedAddBody rhs)) m (stepMirFn (checkedAddBody rhs) s)
      ((annealMiriHooks (checkedAddBody rhs)).coreStep () m) :=
  StepRel.toLockstep hsim fun s' m' ha hm hrel =>
    ⟨⟨hrel, (hnext s' m' ha hm).1, (hnext s' m' ha hm).2.2⟩, (hnext s' m' ha hm).2.1⟩

/-- **Body-specific closed simulation** for `checkedAddBody rhs`: `CheckedAddInv`
is step-closed for every `rhs < 65536`. -/
theorem checkedAdd_stepClosedSim (rhs : Nat) (hrhs : rhs < 65536) :
    StepClosedSim (checkedAddBody rhs) (annealMiriHooks (checkedAddBody rhs))
      (CheckedAddInv rhs) (ImmediateRetRel (checkedAddBody rhs)) := by
  refine ⟨fun s m ⟨⟨hstate, hloc, himm⟩, hshape⟩ => ?_⟩
  have hphase := checkedAdd_phase rhs
  have hstate' := hstate
  rcases hstate' with ⟨topFrame, hframes, _, _, _, hcal, hstack, hbor, hprot, hcaller, _⟩
  have himmF : ∀ idx decl, get? (checkedAddBody rhs).localDecls idx = some decl →
      ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf idx :=
    fun idx decl hdecl tf htf => himm tf htf idx decl hdecl trivial
  have hu16 : IsPrimScalarTy Witness.u16Ty := Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hb : s.frame.blockIdx = 0 ∨ s.frame.blockIdx = 1 := by
    rcases h : s.frame.blockIdx with _ | _ | k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [h, checkedAdd_blocks] at hbb
      cases hbb
  rcases hb with hb | hb
  · -- `bb0`
    have hbb0 : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx =
        some (checkedAddBb0 rhs) := by rw [hb]; rfl
    rw [hbb0] at hbb
    injection hbb with hbb
    subst hbb
    have hi : s.frame.stmtIdx = 0 ∨ s.frame.stmtIdx = 1 ∨ s.frame.stmtIdx = 2 := by
      have : (checkedAddBb0 rhs).statements.length = 2 := rfl
      omega
    rcases hi with hi | hi | hi
    · -- `StorageLive(_1)`
      have hstmt : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx =
          some (st (.storageLive 1)) := by rw [hi]; rfl
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb0 hstmt
        (fun tf htf => .storageLive _ 1 Witness.u16BoolDecl rfl rfl (himmF 1 _ rfl tf htf))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb0 hstmt (Or.inr (Or.inl ⟨1, rfl⟩)) hs'
      refine ⟨⟨checkedAddBb0 rhs, by rw [hblk]; exact hbb0,
        by rw [hidx, hi]; show 0 + 1 ≤ 2; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `_1 = AddWithOverflow(const 65500_u16, const rhs_u16)`
      have hstmt : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx =
          some (st (.assign (pl 1) (.binaryOp .addWithOverflow
            (.constant (Witness.constU16 65500)) (.constant (Witness.constU16 rhs))))) := by
        rw [hi]; rfl
      have hc : ∀ n, n < 65536 → ∀ tf, WellTypedScalarOperand (checkedAddBody rhs) tf
          (.constant (Witness.constU16 n)) Witness.u16Ty :=
        fun n hn tf => .constScalar _ ⟨n, 2⟩ rfl hu16 (Or.inr (Or.inl rfl))
          (by rw [scalarModulus_eq_two_pow]; simpa using hn) rfl (fun h => by cases h)
          (fun h => by cases h)
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb0 hstmt
        (fun tf htf => .assign _ 1 Witness.u16BoolDecl _ rfl rfl (himmF 1 _ rfl tf htf)
          (.binaryOp _ _ _ Witness.u16Ty Witness.u16Ty _ (hc 65500 (by decide) tf) (hc rhs hrhs tf)
            (.intWithOverflow _ _ _ _ _ (Or.inl rfl) (.uint .u16 rfl) (.uint .u16 rfl)
              (Or.inl ⟨_, rfl⟩) rfl)))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb0 hstmt (Or.inr (Or.inr (Or.inr ⟨1, _, rfl⟩))) hs'
      obtain ⟨sc0, sc1, hls, hsz⟩ := checkedAdd_add_shape hcal hbor hprot hcaller hb hi hs'
      refine ⟨⟨checkedAddBb0 rhs, by rw [hblk]; exact hbb0,
        by rw [hidx, hi]; show 1 + 1 ≤ 2; decide⟩,
        fun _ => ⟨sc0, sc1, hls, hsz⟩,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
    · -- `assert(copy (_1.1) == false) -> bb1` (unwind: unreachable)
      have hstmt_none : get? (checkedAddBb0 rhs).statements s.frame.stmtIdx = none := by
        rw [hi]; rfl
      have hstmt_len : s.frame.stmtIdx = length (checkedAddBb0 rhs).statements := by
        rw [hi]; rfl
      obtain ⟨sc0, sc1, hls, hsz0⟩ := hshape (Or.inl ⟨hb, hi⟩)
      rcases assert_pairFlag_step_cases hstate hphase hbb0 hstmt_none hstmt_len
          (p := 1) (decl := Witness.u16BoolDecl) (t0 := .uint .u16) rfl rfl rfl
          (fun tf htf => himmF 1 _ rfl tf htf) hls with
        ⟨m', msg, hA, hM⟩ | ⟨tf, tf', hframes', hA, hM, hrel, hmono⟩
      · have hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
            (Miri.Interpreter.Step.step (annealStepHooks (checkedAddBody rhs).localDecls
              (checkedAddBody rhs).layouts) () m) := by
          rw [hA, hM]; exact StepRel.ub m' msg
        refine checkedAdd_lockstep_of_stepRel hsim fun s' m'' hs' _ => ?_
        rw [hA] at hs'
        exact absurd hs' MirStepNode_fail_ne_step
      · have hsim : StepRel (checkedAddBody rhs) m (stepMirFn (checkedAddBody rhs) s)
            (Miri.Interpreter.Step.step (annealStepHooks (checkedAddBody rhs).localDecls
              (checkedAddBody rhs).layouts) () m) := by
          rw [hA, hM]; exact StepRel.step _ _ hrel
        refine checkedAdd_lockstep_of_stepRel hsim fun s' m'' hs' hm' => ?_
        rw [hA] at hs'
        have hs'' := MirStepNode_step_inj hs'
        subst hs''
        refine ⟨⟨checkedAddBb1, rfl, Nat.zero_le _⟩, fun _ => ⟨sc0, sc1, hls, hsz0⟩, ?_⟩
        intro tf₂ htf₂ idx decl hdecl _
        rw [hM] at hm'
        injection hm' with hm'
        subst hm'
        dsimp only at htf₂
        rw [hframes] at hframes'
        injection hframes' with h0
        injection h0 with h0 _
        subst h0
        injection htf₂ with h1
        injection h1 with h1 _
        subst h1
        exact hmono idx (himmF idx decl hdecl topFrame hframes)
  · -- `bb1`
    have hbb1 : get? (checkedAddBody rhs).basicBlocks s.frame.blockIdx = some checkedAddBb1 := by
      rw [hb]; rfl
    rw [hbb1] at hbb
    injection hbb with hbb
    subst hbb
    have hi : s.frame.stmtIdx = 0 ∨ s.frame.stmtIdx = 1 ∨ s.frame.stmtIdx = 2 := by
      have : checkedAddBb1.statements.length = 2 := rfl
      omega
    rcases hi with hi | hi | hi
    · -- `_0 = copy (_1.0)`
      have hstmt : get? checkedAddBb1.statements s.frame.stmtIdx =
          some (st (.assign (pl 0)
            (.use (.copy { local_ := 1, projection := [.field 0 Witness.u16Ty] })))) := by
        rw [hi]; rfl
      obtain ⟨sc0, sc1, hls, hsz0⟩ := hshape (Or.inr ⟨hb, hi⟩)
      have hsim := step_assign_pairField0_simulation_ext hstate hphase hbb1 hstmt
        (dstIdx := 0) (p := 1) (dstDecl := Witness.u16Decl) (decl := Witness.u16BoolDecl)
        (t0 := .uint .u16) rfl (by decide) rfl rfl rfl
        (fun tf htf => himmF 0 _ rfl tf htf) (fun tf htf => himmF 1 _ rfl tf htf) hls
        (by rw [hsz0]; rfl) (fun h => by cases h) (fun h => by cases h)
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb1 hstmt (Or.inr (Or.inr (Or.inr ⟨0, _, rfl⟩))) hs'
      refine ⟨⟨checkedAddBb1, by rw [hblk]; exact hbb1, by rw [hidx, hi]; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `StorageDead(_1)`
      have hstmt : get? checkedAddBb1.statements s.frame.stmtIdx = some (st (.storageDead 1)) := by
        rw [hi]; rfl
      have hsim := step_assign_scalar_simulation_ext hstate hphase hbb1 hstmt
        (fun tf htf => .storageDead _ 1 Witness.u16BoolDecl rfl rfl (by decide)
          (himmF 1 _ rfl tf htf))
      refine checkedAdd_lockstep_of_stepRel hsim.1 fun s' m' hs' hm' => ?_
      obtain ⟨hblk, hidx⟩ :=
        checkedAdd_stmt_location hcal hbb1 hstmt (Or.inr (Or.inr (Or.inl ⟨1, rfl⟩))) hs'
      refine ⟨⟨checkedAddBb1, by rw [hblk]; exact hbb1, by rw [hidx, hi]; decide⟩, ?_,
        nonAddrTakenImmediate_of_pres ⟨topFrame, hframes⟩ himm hsim.2 hm'⟩
      intro h
      exfalso
      rw [hblk, hidx, hb, hi] at h
      revert h
      decide
    · -- `return`
      have hstmt_none : get? checkedAddBb1.statements s.frame.stmtIdx = none := by
        rw [hi]; rfl
      have hstmt_len : s.frame.stmtIdx = length checkedAddBb1.statements := by
        rw [hi]; rfl
      have hsim := step_terminator_goto_return_simulation hstate hphase hbb1 hstmt_none hstmt_len
        rfl (Or.inr (Or.inl ⟨rfl, Witness.u16Decl, rfl, IsPrimScalarTy.size_ne_zero hu16,
          fun tf htf => himmF 0 _ rfl tf htf⟩))
      refine checkedAdd_lockstep_of_stepRel hsim fun s' m' hs' _ => ?_
      rw [stepMirFn_at_terminator hcal hphase hbb1 hstmt_none hstmt_len] at hs'
      unfold evalTerminator at hs'
      rw [show checkedAddBb1.terminator.kind = .return_ from rfl, hstack] at hs'
      dsimp only at hs'
      revert hs'
      cases get? s.frame.locals 0 with
      | none => exact fun h => absurd h MirStepNode_fail_ne_step
      | some slot =>
        cases slot with
        | dead => exact fun h => absurd h MirStepNode_fail_ne_step
        | uninit => exact fun h => absurd h MirStepNode_fail_ne_step
        | init _ => exact fun h => absurd h MirStepNode_retNormal_ne_step

/-- The entry states satisfy `CheckedAddInv`. -/
theorem checkedAdd_entry (rhs : Nat) :
    CheckedAddInv rhs (initMachineState (checkedAddBody rhs) [])
      (miriEntryState (checkedAddBody rhs)) := by
  refine ⟨⟨stateRel_entry _, ⟨checkedAddBb0 rhs, rfl, Nat.zero_le _⟩, entry_immediate _ _⟩, ?_⟩
  intro h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact absurd h (by show ¬ (0 = 2); decide)
  · exact absurd h (by show ¬ (0 = 1); decide)

/-- **Whole-program `TreeSafe ↔ System.Safe`** for the checked-addition witness,
for every `rhs < 65536`. -/
theorem checkedAdd_treeSafe_iff_miriSafe (rhs : Nat) (hrhs : rhs < 65536) :
    TreeSafe (mirCallTree (checkedAddBody rhs) []) ↔
      (miriSystem (annealMiriHooks (checkedAddBody rhs))).Safe
        (miriEntryState (checkedAddBody rhs)) :=
  treeSafe_iff_miriSafe (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)

/-- Bidirectional finite-step UB reachability for the checked-addition witness. -/
theorem checkedAdd_reachesUB_iff (rhs : Nat) (hrhs : rhs < 65536) :
    MirReachesUB (mirCallTree (checkedAddBody rhs) []) ↔
      ∃ e, (miriSystem (annealMiriHooks (checkedAddBody rhs))).ReachesOutcome
        (miriEntryState (checkedAddBody rhs)) (.undefinedBehavior e) :=
  reachesUB_iff_miriReachesUB (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)

/-- Partial-correctness equivalence for the checked-addition witness. -/
theorem checkedAdd_partialCorrect_iff (rhs : Nat) (hrhs : rhs < 65536) (postA : Value → Prop)
    (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, ImmediateRetRel (checkedAddBody rhs) retVal v → (postA retVal ↔ postM v)) :
    (miriSystem (annealMiriHooks (checkedAddBody rhs))).PartialCorrect
        (miriEntryState (checkedAddBody rhs)) postM ↔
      ∀ tr retVal mem, ReachesRet (mirCallTree (checkedAddBody rhs) []) tr (.normal (retVal, mem)) →
        postA retVal :=
  partialCorrect_iff_annealPostcondition (checkedAdd_stepClosedSim rhs hrhs) (checkedAdd_entry rhs)
    postA postM hpost

/-! ### Whole-program return witnesses -/

/-- **`arith_offset` returns** (`LM-4.2`, `arithOffsetPosBody`):
`_2 = &raw mut _1; _0 = arith_offset(copy _2, 5_isize) -> bb1; bb1: return` runs
in both machines from the pre-state to a normal root return of the raw pointer
`40` bytes past `_1` (`step_terminator_return_rawPtr_lm3_1_simulation`), with
`ImmediateRelLM3_1`-related return values. -/
theorem w3_arith_offset_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns WitnessLM4_2.arithOffsetPosBody (annealMiriHooks WitnessLM4_2.arithOffsetPosBody)
        (WitnessLM4_2.ptr4AnnealPre WitnessLM4_2.arithOffsetPosBody)
        (WitnessLM4_2.ptr4MiriPre WitnessLM4_2.arithOffsetPosBody WitnessLM4_2.rawMutU64K)
        (.ptr { allocId := 1, offsetBytes := 40 } 8) (.immediate imm0) ∧
      get? WitnessLM4_2.arithOffsetPosBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_1
        [rawPtrAllocMapEntry WitnessLM4_2.arithOffsetPosBody.localDecls
          WitnessLM4_2.arithOffsetPosBody.layouts .mut 1 1 Witness.lm31AllocId1]
        decl0.ty WitnessLM4_2.arithOffsetPosBody.layouts
        (.ptr { allocId := 1, offsetBytes := 40 } 8) imm0 := by
  obtain ⟨s₁, s₂, m₁, m₂, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, _, hret, hmret, hdecl0, hop,
    himm⟩ := retArithOffset_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hmret)
      (.refl _)))
    hmret rfl (by change (annealControlHooks.returnOperand () m₂).2 = _; rw [hop])

/-- **`write_bytes` returns** (`LM-4.2`, `retWriteBytesReadBody`):
`_2 = &raw mut _1; _3 = write_bytes::<u64>(copy _2, 0xAB, 1) -> bb1;
bb1: _0 = copy (*_2); return` fills `_1` with `0xAB` bytes through the raw
pointer, reads them back through it, and runs in both machines to a normal root
return of `0xABABABABABABABAB_u64`. -/
theorem w6_write_bytes_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns retWriteBytesReadBody (annealMiriHooks retWriteBytesReadBody)
        (WitnessLM4_2.ptr4AnnealPre retWriteBytesReadBody)
        (WitnessLM4_2.ptr4MiriPre retWriteBytesReadBody WitnessLM4_2.u64K)
        (.scalar ⟨0xABABABABABABABAB, 8⟩) (.immediate imm0) ∧
      get? retWriteBytesReadBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retWriteBytesReadBody.layouts (.scalar ⟨0xABABABABABABABAB, 8⟩) imm0 := by
  obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, _, hs₃, hm₃, _, _,
    hret, hmret, hdecl0, hop, himm⟩ := retWriteBytesRead_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.refl _)))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hmret) (.refl _))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₃).2 = _; rw [hop])

/-- **Valid `CopyNonOverlapping` returns** (`pass_copy_nonoverlapping_disjoint_locals`,
`retCopyBody`): `_3 = &raw const _1; _4 = &raw mut _2;
copy_nonoverlapping(copy _3, copy _4, 1); _0 = copy (*_4); return` copies
`42_u64` between disjoint allocations and runs in both machines to a normal
root return of the copied `42_u64`. -/
theorem w6_copy_nonoverlapping_disjoint_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns retCopyBody (annealMiriHooks retCopyBody) retCopyAnnealPre retCopyMiriPre
        (.scalar ⟨42, 8⟩) (.immediate imm0) ∧
      get? retCopyBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retCopyBody.layouts (.scalar ⟨42, 8⟩) imm0 := by
  obtain ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, hs₃, hm₃, _,
    _, _, hs₄, hm₄, _, hret, hmret, hdecl0, hop, himm⟩ := retCopy_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hmret)
        (.refl _)))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₄).2 = _; rw [hop])

/-- **Checked addition, unconditionally**: for every `rhs`, the body-specific
closed simulation `checkedAdd_stepClosedSim` gives the whole-program safety
equivalence and UB-reachability equivalence of `checkedAddBody rhs` (which the
syntactic fragment excludes because it projects the `(u16, bool)` pair). -/
theorem w1_checked_add_treeSafe_iff_miriSafe (rhs : Nat) (hrhs : rhs < 65536) :
    (TreeSafe (mirCallTree (checkedAddBody rhs) []) ↔
      (miriSystem (annealMiriHooks (checkedAddBody rhs))).Safe (miriEntryState (checkedAddBody rhs))) ∧
    (MirReachesUB (mirCallTree (checkedAddBody rhs) []) ↔
      ∃ e, (miriSystem (annealMiriHooks (checkedAddBody rhs))).ReachesOutcome
        (miriEntryState (checkedAddBody rhs)) (.undefinedBehavior e)) :=
  ⟨checkedAdd_treeSafe_iff_miriSafe rhs hrhs, checkedAdd_reachesUB_iff rhs hrhs⟩


end LeanMiriSpec.Correspondence.MiriDiffWitnesses
