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
   `w1_checked_add_no_overflow`, `w1_checked_add_overflow_ub`, the terminating
   conditional loop `w1_count_loop_returns` (`SwitchInt` exit, in the
   unconditional fragment), the diverging safe loop `w1_loop_diverges_safely`
   (`InfiniteRun`, `System.Safe`, `TreeSafe`), and the divergence
   `w1_assert_continue_divergence`.
2. Aggregates: `w2_array_index_returns` (safe `Index` and `ConstantIndex`, from
   entry), `w2_array_index_oob_ub`, `w2_padded_struct_returns`,
   `w2_enum_downcast_switch_returns`, `w2_union_init_prefix_read`, and
   `w2_union_uninit_bytes_ub`.
3. Raw pointers: `w3_rawPtr_write_read_returns`, `w3_use_after_storageDead_ub`,
   `w3_arith_offset_steps`, and `w3_arith_offset_uninit_ub`.
4. Tree Borrows: `w4_child_write_then_parent_read_returns` (`I-10`),
   `w4_safe_ref_return` (a returned `&u64`), `w4_unsafe_cell_vs_freeze`
   (`I-11`), and `w4_protected_reservedFrz_conflict_ub`, the last two with the
   agreeing `lean-miri` Tree Borrows accesses (`TreeBorrowsRel`,
   `Tree.NormalTreeState.performAccess`).
5. Multi-frame calls: `w5_call_return`, `w5_protector_release_step`
   (`GlobalState.endCall` releasing a live protector), `w5_callee_unreachable_ub`,
   and `w5_callee_uninit_return_ub`.
6. Intrinsics: `w6_assume_true`, `w6_assume_false_ub`, `w6_exact_div_valid`,
   `w6_exact_div_non_multiple_ub`, `w6_write_bytes_steps`,
   `w6_write_bytes_oob_ub`, `w6_copy_nonoverlapping_disjoint_steps`, and
   `w6_copy_nonoverlapping_overlap_ub`.

`AgreeReturns` / `AgreeReturnsBits` (both machines `TreeSafe` / `System.Safe`
and returning the same value), `AgreeUB` (both reach undefined behavior and
neither is safe), and `AgreeReaches` (both run in lockstep to related states)
bundle the agreeing whole-program facts. Executions without memory allocation
are checked by kernel evaluation (`decide`, `decide +kernel`) of `runLoopFuel`
and `runAnnealBounded`; executions that allocate reuse the step-by-step traces
of the `LM-2` … `LM-4.2` witness modules through `MiriPath` / `AnnealPath`.
Runs ending in a root return of `()` or of a raw pointer are certified up to
that return (`AgreeReaches`), since the certified return steps require a sized,
non-pointer `_0`.
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

/-- `arith_offset` (`LM-4.2`, `arithOffsetPosBody`): `_2 = &raw mut _1` and
`_0 = arith_offset(copy _2, 5)` step both machines in lockstep from the
pre-state to `StateRelLM3_1`-related states, with `_0` pointing `40` bytes
past `_1`. (The root return of the raw pointer `_0` is outside the certified
return correspondence: `step_terminator_goto_return_lm3_1_simulation` requires
a non-pointer `_0`.) -/
theorem w3_arith_offset_steps :
    ∃ s₂ m₂,
      AgreeReaches WitnessLM4_2.arithOffsetPosBody (annealMiriHooks WitnessLM4_2.arithOffsetPosBody)
        (WitnessLM4_2.ptr4AnnealPre WitnessLM4_2.arithOffsetPosBody) s₂
        (WitnessLM4_2.ptr4MiriPre WitnessLM4_2.arithOffsetPosBody WitnessLM4_2.rawMutU64K) m₂ ∧
      StateRelLM3_1 WitnessLM4_2.arithOffsetPosBody s₂ m₂
        [rawPtrAllocMapEntry WitnessLM4_2.arithOffsetPosBody.localDecls
          WitnessLM4_2.arithOffsetPosBody.layouts .mut 1 1 Witness.lm31AllocId1] ∧
      get? s₂.frame.locals 0 = some (.init (.ptr { allocId := 1, offsetBytes := 40 } 8)) := by
  obtain ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, _, hs₂, hm₂, hrel₂, hget⟩ :=
    WitnessLM4_2.wit_lm4_2_arith_offset_pos
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact ⟨s₂, m₂, agreeReaches_of_paths (.step .silent hs₁ (.step .silent hs₂ (.refl _)))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))),
    hrel₂, hget⟩

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
      (annealStepHooksLM2_2 body.localDecls body.layouts))) n m = .returned m' (.ok v) := by
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
        rw [h₁, h₂]

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
    runLoopFuel (annealMiriHooks body) n m = .returned m' (.ok v) := by
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
        rw [h₁, h₂]

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
`StateRelLM2_4`-related states with `_2 = 5_u8`: reading the initialized
prefix is defined in both machines (contrast `w2_union_uninit_bytes_ub`). -/
theorem w2_union_init_prefix_read :
    ∃ m₂,
      AgreeReaches Witness.lm24Body
        (.ofHooks (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts)
          annealControlHooks)
        (Witness.lm24InitAnneal 1) Witness.lm24Bb1S2 (Witness.lm24InitMiri 1) m₂ ∧
      StateRelLM2_4 Witness.lm24Body Witness.lm24Bb1S2 m₂ ∧
      get? Witness.lm24Bb1S2.frame.locals 2 = some (.init (.scalar ⟨5, 1⟩)) := by
  obtain ⟨m₁, m₂, hm₁, _, hm₂, hrel₂, hget⟩ := Witness.lm24_write_read_same_field_steps
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact ⟨m₂, agreeReaches_of_paths
    (.step .silent Witness.lm24_bb1_anneal₁ (.step .silent Witness.lm24_bb1_anneal₂ (.refl _)))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))),
    hrel₂, hget⟩

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
`lean-miri`'s allocation bytes). -/
theorem w6_copy_nonoverlapping_disjoint_steps :
    ∃ s₃ m₃,
      AgreeReaches WitnessLM4_2.copyDistinctBody (annealMiriHooks WitnessLM4_2.copyDistinctBody)
        (WitnessLM4_2.copy6AnnealPre WitnessLM4_2.copyDistinctBody true) s₃
        (WitnessLM4_2.copy6MiriPre WitnessLM4_2.copyDistinctBody true) m₃ ∧
      get? s₃.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩)) ∧
      ∃ la msc,
        m₃.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId2) =
          some (Witness.lm31AllocId2, la) ∧
        ScalarRel ⟨42, 8⟩ msc ∧
        la.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 8)) false =
          .ok (.fromScalarInt msc) := by
  obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, _, hs₂, hm₂, _, hs₃, hm₃, hrel₃, hget, hmem⟩ :=
    WitnessLM4_2.wit_lm4_2_copy_nonoverlapping_ok
  obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
  exact ⟨s₃, m₃, agreeReaches_of_paths
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.refl _))))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_eq_singleton htf₃) (.refl _)))),
    hget, hmem⟩

/-- `write_bytes::<u64>(ptr, 0xAB, 1)` (`LM-4.2`, `writeBytesMutBody 0xAB 1`): both
machines take the reborrow and the intrinsic call in lockstep to
`StateRelLM3_1`-related states, with `_1 = 0xABABABABABABABAB`. (The call's
`()` result in `_0` is a zero-sized return, outside the certified return
correspondence, `H1`.) -/
theorem w6_write_bytes_steps :
    ∃ s₂ m₂,
      AgreeReaches (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 1))
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1)) s₂
        (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 1) WitnessLM4_2.unitK) m₂ ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) := by
  obtain ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, _, hs₂, hm₂, hrel₂, hget⟩ :=
    WitnessLM4_2.wit_lm4_2_write_bytes_ok
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  exact ⟨s₂, m₂, agreeReaches_of_paths (.step .silent hs₁ (.step .silent hs₂ (.refl _)))
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))),
    hget⟩

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

/-- `I-11` (`pass_tb_unsafe_cell_shared_mutation`): through `&UnsafeCell<u32>`
(a `Cell` tag), a foreign write through an unrelated raw pointer leaves the
shared reborrow usable and Anneal's whole program returns `7_u32`; through `&u32`
(a `Frozen` tag) the same foreign write disables the reborrow and the child read
is undefined behavior. At every step of both executions `lean-miri`'s Tree
Borrows tree (`basedNormalTree` of Anneal's borrow table) agrees through
`TreeBorrowsRel`: the foreign write is a `Completed` access in both trees, and
the child read is `Completed` under `Cell` but the transition error
`ChildAccessForbidden Disabled` under `Frozen`
(`WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps`). -/
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

/-- The `LM-4.1` interpreter at the callee-return state of `witCallerBody`,
whose callee frame holds the function-entry protector `CallId 1`. -/
def protReturnHooks : AnnealMiriHooks :=
  multiFrameHooks WitnessLM4_1.witCallerBody fun c m =>
    Miri.Interpreter.Step.step
      (annealStepHooksLM4_1
        (activeMirBody WitnessLM4_1.witCallerBody WitnessLM4_1.witCalleeReadyToReturnAnneal)
        WitnessLM4_1.witCalleeReadyToReturnAnneal.memory.callees
        (annealPoppedFrameState WitnessLM4_1.witCalleeReadyToReturnAnneal)) c m

/-- **Protector release on return** (`Terminator.Return` with
`GlobalState.endCall`, `LM-4.1`): from the callee-return state, whose callee
frame is protected by `CallId 1`, one Anneal transition and one `miriSystem`
transition (`RunLoop.iteration`) pop the callee frame into
`MultiFrameStateRel`-related caller states; `GlobalState.endCall` empties the
borrow tracker's `protectedTags`, and Anneal's `activeProtectors` and
`callStack` become empty. -/
theorem w5_protector_release_step :
    ∃ s' m',
      CoStep (stepMirState WitnessLM4_1.witCallerBody)
        (.running WitnessLM4_1.witCalleeReadyToReturnAnneal) (.running s') ∧
      (miriSystem protReturnHooks).step WitnessLM4_1.witCalleeReadyToReturnMiri m' ∧
      MultiFrameStateRel WitnessLM4_1.witCallerBody s' m' ∧
      s'.memory.activeProtectors = [] ∧ s'.memory.callStack = [] ∧
      ∃ tracker', m'.machine.borrowTracker = some tracker' ∧
        tracker'.global.protectedTags.entries = #[] := by
  obtain ⟨hrel, ⟨s', hs', hcs, hprot, _, _⟩, _, ⟨tracker', htr, hpt, _, _⟩⟩ :=
    WitnessLM4_1.wit_lm4_1_callee_return_simulation
  generalize hmr : Miri.Interpreter.Step.step
    (annealStepHooksLM4_1
      (activeMirBody WitnessLM4_1.witCallerBody WitnessLM4_1.witCalleeReadyToReturnAnneal)
      WitnessLM4_1.witCalleeReadyToReturnAnneal.memory.callees
      (annealPoppedFrameState WitnessLM4_1.witCalleeReadyToReturnAnneal))
    () WitnessLM4_1.witCalleeReadyToReturnMiri = mRes at hrel htr
  rw [hs'] at hrel
  cases hrel with
  | step _ m' hmf =>
    exact ⟨s', m', coStep_of_emitStep (obs := .silent) hs',
      miriSystem_step_of_coreStep (H := protReturnHooks) hmr hmf.frames_ne_empty, hmf, hprot, hcs,
      tracker', htr, hpt⟩

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

end LeanMiriSpec.Correspondence.MiriDiffWitnesses
