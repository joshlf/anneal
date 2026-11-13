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
whole-program semantics of `Safety.lean`: Anneal's Stage-1 `mirTree` (`TreeSafe`,
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
   (`InfiniteRun`, `System.Safe`, `TreeSafe`), and the divergences
   `w1_assert_continue_divergence`, `w1_storageDead_returnPlace_class_divergence`
   (`.blocked` in `lean-miri`, undefined behavior in Anneal),
   `w1_tail_call_class_divergence` (Stage-1 evaluates the tail call and rejects
   its non-function callee with undefined behavior; `.unsupported` in
   `lean-miri`), and `w1_transmute_bool_divergence` (`.unsupported` transmutes in
   `lean-miri`).
2. Aggregates: `w2_array_index_returns` (safe `Index` and `ConstantIndex`, from
   entry), `w2_array_index_oob_ub`, `w2_padded_struct_returns`,
   `w2_enum_downcast_switch_returns`, `w2_union_init_prefix_returns` (a safe
   union write-then-read, from entry, through Stage-1's two-field union value),
   `w2_union_return` (from-entry union-valued root return via
   `step_terminator_return_wellTypedUnion_lm2_4_simulation`),
   `w2_union_overlay_type_punning_returns` (`pass_union_overlay_word_bytes`:
   from-entry narrower projected union write attaching a Stage-1 `D13a` raw-byte
   overlay followed by sibling type-punning `u32` read returning `67305993`),
   `w2_union_init_prefix_lockstep`, and `w2_union_uninit_bytes_ub`.
3. Raw pointers: `w3_rawPtr_write_read_returns`, `w3_rawPtr_return` (a returned
   raw pointer), `w3_use_after_storageDead_ub`, `w3_arith_offset_returns` (a
   returned Stage-1 `arith_offset` pointer), `w3_arith_offset_uninit_ub`, and the
   from-entry Stage-1 upgrades `w3_deref_oob_ub` (`ub_ptr_offset_oob_read` with
   `BinOp.Offset` stride `8`), `w3_deref_oob_write_ub` (`ub_ptr_offset_oob_write`),
   `w3_deref_misaligned_ub` (`ub_unaligned_ptr_read_u32`),
   `w3_ptr_offset_neg_before_start_ub` (`ub_ptr_offset_negative_before_start`),
   `w3_invalid_bool_ptr_deref_ub` (`ub_transmute_invalid_bool_through_ptr`),
   `w3_ptr_offset_stride_read_returns` (`pass_ptr_offset_within_array`),
   `w3_deref_type_pun_returns`, and `w3_storage_revive_stale_deref_ub`.
4. Tree Borrows and references: `w4_child_write_then_parent_read_returns`
   (`I-10`), `w4_safe_ref_return` (a returned `&u64`, from entry),
   `w4_unsafe_cell_vs_freeze` (`I-11`), `w4_protected_reservedFrz_conflict_ub`,
   and `w4_storage_dead_protected_ub` (`StorageDead` with an active `CallId`
   protector vs. unprotected disable and residual `Cell` characterization),
   with the agreeing `lean-miri` Tree Borrows accesses (`TreeBorrowsRel`), the
   from-entry Stage-1 upgrade `w4_invalid_bool_ref_read_ub` (an invalid `bool`
   read through `&bool` is undefined behavior in both machines), and the boundary
   witness `w4_disabled_read_divergence` (from entry, a read through a `Disabled`
   reference is undefined behavior in Anneal, while `lean-miri`'s whole program,
   which does not check Tree Borrows permissions, is `System.Safe` and returns
   the read value).
5. Multi-frame calls and stack unwinding: `w5_call_return`,
   `w5_protector_release_returns` (`GlobalState.endCall` releasing a live
   protector on the way to an agreeing root return), `w5_callee_unreachable_ub`,
   `w5_callee_uninit_return_ub`, and the from-entry Stage-1 upgrades
   `w5_unwind_cleanup_returns` (3-frame `UnwindResume` caught at a caller
   cleanup pad), `w5_unwind_unreachable_ub` (multi-frame `UnwindResume` hitting
   `UnwindAction::Unreachable` UB), `w5_unwind_root_panic_vs_ub_divergence`
   (multi-frame `UnwindResume` unwinding past the root frame: `TreeSafe` `.panic`
   in Anneal vs. undefined behavior in `lean-miri`), and
   `w5_indirect_fnPtr_call_returns` (`ReifyFnPointer` coercion and indirect
   `FnPtr` call).
6. Intrinsics: `w6_assume_true`, `w6_assume_false_ub`, `w6_exact_div_valid`,
   `w6_exact_div_non_multiple_ub`, `w6_ctlz_returns`,
   `w6_saturating_add_returns`, `w6_copy_nonoverlapping_disjoint_returns`,
   `w6_copy_nonoverlapping_full_bytes_returns` (from-entry multi-element
   Stage-1 `copyViaBytes` `8`-byte `u8` copy between `u64` locals),
   `w6_copy_nonoverlapping_rawPtr_tyId80_boundary` (Stage-1 provenance-preserving
   pointer `copy_nonoverlapping` vs. `lean-miri`'s `TyId 80` `.unsupported`
   boundary), `w6_copy_nonoverlapping_disjoint_lockstep`, and
   `w6_copy_nonoverlapping_overlap_ub` (Stage-1 `copy_nonoverlapping`), and the
   Stage-1 external-call boundary, where Stage-1 hands the intrinsic to the
   environment (`anneal_extCall_boundary`): `w6_rotate_left_extCall_boundary`
   (from entry; `.unsupported` in `lean-miri`), `w6_write_bytes_extCall_boundary`
   (lockstep prefix from `WitnessLM4_2.ptr4AnnealPre` / `ptr4MiriPre`), and, from
   program entry, `w6_write_bytes_read_extCall_divergence` (`lean-miri` is
   `System.Safe` and returns the written bytes, while Anneal returns the unchanged
   value and is not `TreeSafe`) and `w6_write_bytes_oob_extCall_divergence`
   (undefined behavior in `lean-miri`, a normal return of the unchanged value in
   Anneal).

`AgreeReturns` / `AgreeReturnsBits` (both machines `TreeSafe` / `System.Safe`
and returning the same value), `AgreeUB` (both reach undefined behavior and
neither is safe), and `AgreeReaches` (both run in lockstep to related states)
bundle the agreeing whole-program facts. Executions without memory allocation
are checked by kernel evaluation (`decide`, `decide +kernel`) of `runLoopFuel`
and `runAnnealBounded`; executions that allocate reuse the step-by-step traces
of the `LM-2` … `LM-4.2` witness modules through `MiriPath` / `AnnealPath`.
The `*_lockstep` witnesses reuse upstream bodies that never write `_0`; they
certify the lockstep segment (`AgreeReaches`) and state that Anneal's whole
program then faults at the root return. Stage-1 external calls are followed
through `coStep_of_extCall` for an explicit environment response
(`MirCallAns`), after a running prefix from program entry
(`anneal_extCall_boundary_of_prefix`). The `write_bytes` runs of `lean-miri` are
certified against the pre-Stage-1 reference model `stepMirFnLM4_2`
(`retWriteBytesRead_ref_trace`, `w6_write_bytes_oob_extCall_divergence`), which
executes the intrinsic inline like `lean-miri`. Witnesses without a corpus program
of that name (the out-of-bounds `write_bytes` and overlapping
`copy_nonoverlapping` bodies) are marked as such.
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

/-! ### Stage-1 external calls (`MirStepNode.extCall`)

Stage-1 `stepMirFn` hands calls without a linked body (and the intrinsics it does
not evaluate inline, such as `write_bytes`, `rotate_left`, and `rotate_right`) to
the environment as a `MirCallE` request, whose response `MirCallAns` (`returned`,
`panicked`, or `aborted`) `TreeSafe` and `ReachesRet` quantify over. The lemmas
below follow Anneal's coalgebra across such a request for a chosen response. -/

/-- Anneal's coalgebra crosses a Stage-1 external call `MirStepNode.extCall req k`
with every environment response `ans` (`MirCallE` is not a fault effect). -/
theorem coStep_of_extCall {body : CapturedMir} {s : MachineState} {req : MirCallReq}
    {k : MirCallAns → MirExecState} (hs : stepMirFn body s = MirStepNode.extCall req k)
    (ans : MirCallAns) : CoStep (stepMirState body) (.running s) (k ans) := by
  have h : stepMirState body (.running s) = .vis (.inr (.inr (.call req))) k := hs
  exact .vis h (mir_not_isFault_inr _) ans

/-- A `CoReach`-reachable state whose next node is the undefined-behavior fault:
Anneal's whole program reaches undefined behavior and is not `TreeSafe`. -/
theorem anneal_ub_of_coReach {body : CapturedMir} {s : MachineState} {y : MirExecState}
    (hy : CoReach (stepMirState body) (.running s) y)
    (hf : stepMirState body y = MirStepNode.fail .ub) :
    MirReachesUB (mirTree body s) ∧ ¬ TreeSafe (mirTree body s) := by
  rw [mirTree_eq_cofix]
  refine ⟨?_, fun hsafe => treeSafe_cofix_iff.1 hsafe y hy (by rw [hf]; exact isFaultNode_fail _)⟩
  obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
  exact ⟨tr, _, _, htr, by rw [observe_cofix_eq, hf]; rfl⟩

/-- A `CoReach`-reachable normal root return of Anneal's whole program. -/
theorem anneal_reachesRet_of_coReach {body : CapturedMir} {s : MachineState} {y : MirExecState}
    (hy : CoReach (stepMirState body) (.running s) y) {v : Value} {mem : Memory}
    (hr : stepMirState body y = MirStepNode.retNormal v mem) :
    ∃ tr, ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rw [mirTree_eq_cofix]
  exact reachesRet_cofix_iff.2 ⟨y, hy, hr⟩

/-- **Stage-1 external-call boundary, whole program.** Along an Anneal path from
`s` to `sₙ`, Stage-1 `stepMirFn body sₙ` hands `req` to the environment and resumes
with `resumeExternalCall sₙ locals dest targetBb .unreachable`. Then:

* when the environment returns `retVal` with memory `mem` and Anneal's resumed
  state `sᵣ` runs (`AnnealPath`) to a root return of `v`, Anneal's tree can
  return `v`;
* when the environment unwinds (`MirCallAns.panicked`), the call's
  `UnwindAction::Unreachable` is undefined behavior, so Anneal's tree reaches
  undefined behavior and is not `TreeSafe`. -/
theorem anneal_extCall_boundary {body : CapturedMir} {s sₙ sᵣ sₖ : MachineState}
    {req : MirCallReq} {locals : List LocalSlot} {dest : Place} {targetBb : BasicBlockIdx}
    (hA : AnnealPath body s sₙ)
    (hs : stepMirFn body sₙ =
      MirStepNode.extCall req (resumeExternalCall sₙ locals dest targetBb .unreachable))
    {retVal v : Value} {mem memR : Memory}
    (hres : resumeExternalCall sₙ locals dest targetBb .unreachable (.returned retVal mem) =
      .running sᵣ)
    (hAr : AnnealPath body sᵣ sₖ)
    (hret : stepMirFn body sₖ = MirStepNode.retNormal v memR) (memP : Memory) :
    (∃ tr, ReachesRet (mirTree body s) tr (.normal (v, memR))) ∧
    MirReachesUB (mirTree body s) ∧ ¬ TreeSafe (mirTree body s) := by
  have hr : CoReach (stepMirState body) (.running s) (.running sₖ) := by
    have h := hA.coReach.tail (coStep_of_extCall hs (.returned retVal mem))
    rw [hres] at h
    exact h.trans hAr.coReach
  have hp := hA.coReach.tail (coStep_of_extCall hs (.panicked memP))
  exact ⟨anneal_reachesRet_of_coReach hr hret, anneal_ub_of_coReach hp rfl⟩

/-- A running `runAnnealBounded` prefix is a `CoReach` path of Anneal's
coalgebra (used to start the Stage-1 external-call witnesses at program entry). -/
theorem coReach_of_runAnnealBounded_running {body : CapturedMir} {n : Nat} {s s' : MachineState}
    (h : runAnnealBounded body n s = .running s') :
    CoReach (stepMirState body) (.running s) (.running s') := by
  induction n generalizing s with
  | zero => cases h; exact .refl _
  | succ n ih =>
    rcases anneal_step_classify body s with
      ⟨s₁, hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, _⟩ | hrun
    · rw [hrun] at h
      exact .head ((hsucc _).2 rfl) (ih h)
    · rw [hrun] at h
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases h
    · rw [hrun] at h; cases h
    · rw [hrun] at h; cases h

/-- `anneal_extCall_boundary` after a running `runAnnealBounded` prefix from `s₀`
(e.g. `initMachineState body []`) to the start `s` of the Anneal path. -/
theorem anneal_extCall_boundary_of_prefix {body : CapturedMir} {s₀ s sₙ sᵣ sₖ : MachineState}
    {p : Nat} {req : MirCallReq} {locals : List LocalSlot} {dest : Place}
    {targetBb : BasicBlockIdx}
    (hpa : runAnnealBounded body p s₀ = .running s)
    (hA : AnnealPath body s sₙ)
    (hs : stepMirFn body sₙ =
      MirStepNode.extCall req (resumeExternalCall sₙ locals dest targetBb .unreachable))
    {retVal v : Value} {mem memR : Memory}
    (hres : resumeExternalCall sₙ locals dest targetBb .unreachable (.returned retVal mem) =
      .running sᵣ)
    (hAr : AnnealPath body sᵣ sₖ)
    (hret : stepMirFn body sₖ = MirStepNode.retNormal v memR) (memP : Memory) :
    (∃ tr, ReachesRet (mirTree body s₀) tr (.normal (v, memR))) ∧
    MirReachesUB (mirTree body s₀) ∧ ¬ TreeSafe (mirTree body s₀) := by
  have hpre := coReach_of_runAnnealBounded_running hpa
  have hr : CoReach (stepMirState body) (.running s₀) (.running sₖ) := by
    have h := (hpre.trans hA.coReach).tail (coStep_of_extCall hs (.returned retVal mem))
    rw [hres] at h
    exact h.trans hAr.coReach
  have hp := (hpre.trans hA.coReach).tail (coStep_of_extCall hs (.panicked memP))
  exact ⟨anneal_reachesRet_of_coReach hr hret, anneal_ub_of_coReach hp rfl⟩

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

/-- A tail call to a non-function callee (`bb0: tailcall const 0_u8()`):
Stage-1 Anneal evaluates `TerminatorKind.tailCall` (`evalTailCallTerminator`), and
`resolveCallTarget` rejects the `u8` callee with undefined behavior, whereas
`annealTerminatorHooks` does not lower tail calls and `lean-miri` reaches an
`.unsupported` outcome. Neither machine is safe, but their failure classes
differ (a post-Stage-1 class divergence; before Stage-1 both were
unsupported). -/
def tailCallBody : CapturedMir :=
  mkBody "lm_4_3_witness::tail_call" [dcl tyU8] [blk [] (.tailCall (cU8 0) [])]

theorem w1_tail_call_class_divergence :
    (∃ e, (miriSystem (annealMiriHooks tailCallBody)).ReachesOutcome
      (miriEntryState tailCallBody) (.unsupported e)) ∧
    ¬ (miriSystem (annealMiriHooks tailCallBody)).Safe (miriEntryState tailCallBody) ∧
    MirReachesUB (mirCallTree tailCallBody []) ∧
    ¬ TreeSafe (mirCallTree tailCallBody []) := by
  have ha : runAnnealBounded tailCallBody 1 (initMachineState tailCallBody []) =
      .faulted .ub := rfl
  obtain ⟨e, he⟩ : ∃ e, runLoopFuel (annealMiriHooks tailCallBody) 1 (miriEntryState tailCallBody) =
      .stopped (miriEntryState tailCallBody) e ∧ isUnsupportedError e = true ∧
      Miri.Interpreter.RunLoop.reportsUB e = false :=
    ⟨_, rfl, rfl, rfl⟩
  have hm := miri_outcome_of_runLoopFuel_stopped he.1
  have hc : classifyError e = .unsupported e := by
    unfold classifyError; rw [he.2.2, he.2.1]; rfl
  rw [hc] at hm
  have hA := anneal_fault_of_runAnnealBounded_faulted ha
  exact ⟨⟨e, hm.1⟩, hm.2, hA.2 rfl, hA.1⟩

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

/-- **Stage-1 external-call boundary** (`rotate_left`):
`rotate_left::<u32>(0x80000001, 1)` (`rotateLeftBody`). Stage-1 `stepMirFn` does not
rotate but hands the call to the environment (`MirStepNode.extCall`,
`WitnessLM4_2.wit_lm4_2_rotate_left_boundary`): when the environment returns the
rotated value `3_u32`, Anneal's whole program returns `3`; when it unwinds, the
call's `UnwindAction::Unreachable` is undefined behavior, so Anneal's whole program
is not `TreeSafe`. `lean-miri`'s pinned dispatcher leaves `rotate_left` to its MIR
fallback body and the step fails closed with an `.unsupported` outcome. (Before
Stage-1, Anneal rotated inline and was `TreeSafe`.) -/
def rotateLeftBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::rotate_left" WitnessLM4_2.u32K
    (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K

theorem w6_rotate_left_extCall_boundary :
    (∃ tr mem, ReachesRet (mirCallTree rotateLeftBody []) tr (.normal (.scalar ⟨3, 4⟩, mem))) ∧
    MirReachesUB (mirCallTree rotateLeftBody []) ∧
    ¬ TreeSafe (mirCallTree rotateLeftBody []) ∧
    (∃ msg, (miriSystem (annealMiriHooks rotateLeftBody)).ReachesOutcome
      (miriEntryState rotateLeftBody) (.unsupported (.unsupported msg))) ∧
    ¬ (miriSystem (annealMiriHooks rotateLeftBody)).Safe (miriEntryState rotateLeftBody) := by
  obtain ⟨hext, m', msg, herr⟩ := WitnessLM4_2.wit_lm4_2_rotate_left_boundary
  have hpre : initMachineState rotateLeftBody [] =
      WitnessLM4_2.callAnnealPre "core::intrinsics::rotate_left" WitnessLM4_2.u32K
        (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K := rfl
  obtain ⟨⟨tr, hrr⟩, hub, hns⟩ := anneal_extCall_boundary (body := rotateLeftBody)
    (sᵣ := WitnessLM4_2.callAnnealPost "core::intrinsics::rotate_left" WitnessLM4_2.u32K
      (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K (.scalar ⟨3, 4⟩))
    (retVal := .scalar ⟨3, 4⟩) (v := .scalar ⟨3, 4⟩)
    (mem := (initMachineState rotateLeftBody []).memory)
    (memR := (initMachineState rotateLeftBody []).memory)
    (.refl _) hext rfl (.refl _) rfl (initMachineState rotateLeftBody []).memory
  have heq : miriEntryState rotateLeftBody =
      WitnessLM4_2.callMiriPre "core::intrinsics::rotate_left" WitnessLM4_2.u32K
        (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K := rfl
  have hout := miri_outcome_of_path_error (H := annealMiriHooks rotateLeftBody)
    (.refl (miriEntryState rotateLeftBody)) (by rw [heq]; exact herr)
  rw [mirCallTree, hpre]
  exact ⟨⟨tr, _, hrr⟩, hub, hns, ⟨msg, hout.1⟩, hout.2⟩

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

/-! ### Stage-1 upgrades: from-entry raw-pointer and `BinOp.Offset` lockstep witnesses

Before Stage-1, Anneal accepted out-of-bounds and misaligned raw-pointer reads and
writes, negative `BinOp.Offset` before the start of an allocation, invalid `bool`
loads through cast raw pointers, and failed non-byte `BinOp.Offset` strides
(`miri-diff` ratchets `ub_ptr_offset_oob_read`, `ub_ptr_offset_oob_write`,
`ub_unaligned_ptr_read_u32`, `ub_ptr_offset_negative_before_start`,
`ub_transmute_invalid_bool_through_ptr`, and `pass_ptr_offset_within_array`).
Stage-1 `stepMirFn` steps in lockstep with `lean-miri` on all of them, and every
witness below runs **from program entry** (`initMachineState body []` and
`miriEntryState body`). -/

private theorem stepRelLM3_1_ub_of_anneal_ub
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes) (ha : aRes = .fail .ub) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  generalize ha_eq : aRes = aNode at hsim
  cases hsim with
  | step => rw [ha] at ha_eq; cases ha_eq
  | retRoot => rw [ha] at ha_eq; cases ha_eq
  | ub m' msg => exact ⟨m', msg, rfl⟩

theorem _root_.LeanMiriSpec.Correspondence.StepRelLM3_1.step_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes) (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  rw [ha] at hsim; exact hsim.miri_step_of_anneal_step

private theorem constUsize_wt_mdw (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand body tf (.constant (Witness.constUsizeLM31 n)) Witness.usizeTyLM31 :=
  .constScalar (Witness.constUsizeLM31 n) ⟨n, 8⟩ rfl
    (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn rfl
    (fun h => nomatch h) (fun h => nomatch h)

private theorem constNegOneIsize_wt_mdw (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand body tf (.constant Witness.constNegOneIsizeLM31) Witness.isizeTyLM31 :=
  .constScalar Witness.constNegOneIsizeLM31 ⟨2 ^ 64 - 1, 8⟩ rfl
    (Or.inr (Or.inr (Or.inl ⟨.isize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
    (fun h => nomatch h) (fun h => nomatch h)

private theorem constU64_wt_mdw (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand body tf (.constant (Witness.constU64 n)) Witness.u64Ty :=
  .constScalar (Witness.constU64 n) ⟨n, 8⟩ rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn rfl
    (fun h => nomatch h) (fun h => nomatch h)

private theorem slot_ptr_ne_scalar_mdw {p : ProvenancePtr} {sz : Nat} {sc : MirAst.ScalarInt} :
    (some (LocalSlot.init (.ptr p sz)) : Option LocalSlot) ≠ some (.init (.scalar sc)) := by nofun

private theorem scalarInt_eq_of_scalarRel_mdw
    {sc : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (h₁ : ScalarRel sc msc₁) (h₂ : ScalarRel sc msc₂) : msc₁ = msc₂ := by
  rcases msc₁ with ⟨d₁, sz₁⟩
  rcases msc₂ with ⟨d₂, sz₂⟩
  have hd : d₁ = d₂ := h₁.data_eq.trans h₂.data_eq.symm
  have hsz : sz₁ = sz₂ := h₁.size_eq.trans h₂.size_eq.symm
  subst hd hsz
  rfl

private theorem ptrVal_of_some_init_mdw {p q : ProvenancePtr} {sz₁ sz₂ : Nat}
    (h : (some (LocalSlot.init (.ptr p sz₁)) : Option LocalSlot) = some (.init (.ptr q sz₂))) :
    q = p := by
  injection h with h₁; injection h₁ with h₁'; injection h₁' with h₂ _
  exact h₂.symm

private def mkWitState (body : CapturedMir) (stmtIdx : Nat) (locals : List LocalSlot)
    (borrows : List BorrowEntry) (nextTag : Nat) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState body []).memory with
                  borrows := borrows, nextTag := nextTag } }

/-- **Stage-1 lockstep from entry** (`ub_ptr_offset_oob_read`,
`Witness.lm31OffsetDerefBody`):
`StorageLive(_1.._3); _1 = const 42_u64; _2 = &raw const _1;
_3 = Offset(copy _2, const 1_usize); _0 = copy (*_3); return`.
From `initMachineState` / `miriEntryState`, both machines scale `1_usize` by
`sizeof::<u64>() = 8` (`step_binOp_offset_stride_simulation`) to the
one-past-the-end pointer and reject the out-of-bounds read `*_3` with undefined
behavior (`Witness.wit_lm3_1_anneal_offset_deref_simulation`). -/
theorem w3_deref_oob_ub :
    AgreeUB Witness.lm31OffsetDerefBody (annealMiriHooks Witness.lm31OffsetDerefBody)
      (initMachineState Witness.lm31OffsetDerefBody [])
      (miriEntryState Witness.lm31OffsetDerefBody) := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, m₁, m₂, m₃, m₄, m₅, m₆, m₇, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, _, hs₅, hm₅, _, hs₆, hm₆, hrel₆, _, hfail, herr⟩ :=
    Witness.wit_lm3_1_anneal_offset_deref_simulation
  obtain ⟨tf₆, htf₆, _⟩ := id hrel₆
  have hentry :
      Witness.mkZeroArgEntryMiri Witness.lm31OffsetDerefBody Witness.u64Ty =
        miriEntryState Witness.lm31OffsetDerefBody := rfl
  rw [hentry] at hm₁
  exact agreeUB_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
      (.step .silent hs₅ (.step .silent hs₆ (.refl _))))))) hfail
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_step_ok_true hm₅)
            (.step hm₅ (frames_ne_of_step_ok_true hm₆)
              (.step hm₆ (frames_ne_of_eq_singleton htf₆) (.refl _)))))))
    herr rfl

/-- **Stage-1 lockstep from entry** (`Witness.lm31TypePunBody`): narrowing
raw-pointer cast `*const u64 -> *const u32` and dereference read extracting the
low-order `u32` word `5_u32` of `(2^32 + 5)_u64` from program entry
(`Witness.wit_lm3_1_anneal_deref_type_pun_simulation`). -/
theorem w3_deref_type_pun_returns :
    AgreeReturns Witness.lm31TypePunBody (annealMiriHooks Witness.lm31TypePunBody)
      (initMachineState Witness.lm31TypePunBody [])
      (miriEntryState Witness.lm31TypePunBody)
      (.scalar ⟨5, 4⟩)
      (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 5)))) := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, m₁, m₂, m₃, m₄, m₅, m₆, m₇,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, _, hs₅, hm₅, _, hs₆, hm₆, _, hs₇, hm₇, _,
    hret, hmret, hop⟩ := Witness.wit_lm3_1_anneal_deref_type_pun_simulation
  have hentry :
      Witness.mkZeroArgEntryMiri Witness.lm31TypePunBody Witness.u32TyLM31 =
        miriEntryState Witness.lm31TypePunBody := rfl
  rw [hentry] at hm₁
  exact agreeReturns_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
      (.step .silent hs₅ (.step .silent hs₆ (.step .silent hs₇ (.refl _)))))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_step_ok_true hm₅)
            (.step hm₅ (frames_ne_of_step_ok_true hm₆)
              (.step hm₆ (frames_ne_of_step_ok_true hm₇)
                (.step hm₇ (frames_ne_of_step_ok_true hmret) (.refl _))))))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₇).2 = _; rw [hop])

/-- **Stage-1 lockstep from entry** (`Witness.lm31ReviveBody`): after
`StorageDead(_1); StorageLive(_1)` revives `_1` at a fresh stack allocation,
writing through the stale raw pointer `_2` is undefined behavior in both
machines from program entry (`Witness.wit_lm3_1_anneal_storage_revive_simulation`). -/
theorem w3_storage_revive_stale_deref_ub :
    AgreeUB Witness.lm31ReviveBody (annealMiriHooks Witness.lm31ReviveBody)
      (initMachineState Witness.lm31ReviveBody [])
      (miriEntryState Witness.lm31ReviveBody) := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, m₁, m₂, m₃, m₄, m₅, m₆, m₇, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, _, hs₄, hm₄, _, hs₅, hm₅, hs₆, hm₆, _, hfail, herr⟩ :=
    Witness.wit_lm3_1_anneal_storage_revive_simulation
  have hentry :
      Witness.mkZeroArgEntryMiri Witness.lm31ReviveBody Witness.u64Ty =
        miriEntryState Witness.lm31ReviveBody := rfl
  rw [hentry] at hm₁
  have hne₆ : m₆.stack.frames ≠ #[] := by
    intro hemp
    have hstep := step_of_frames_empty (annealStepHooks Witness.lm31ReviveBody.localDecls
      Witness.lm31ReviveBody.layouts) hemp
    rw [herr] at hstep; cases hstep
  exact agreeUB_of_paths (p := 0) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
      (.step .silent hs₅ (.step .silent hs₆ (.refl _))))))) hfail
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_step_ok_true hm₅)
            (.step hm₅ (frames_ne_of_step_ok_true hm₆)
              (.step hm₆ hne₆ (.refl _)))))))
    herr rfl

/-- Entry-to-return MIR body for `ub_unaligned_ptr_read_u32`:
`StorageLive(_1.._5); _1 = const 42_u64; _2 = &raw const _1; _3 = _2 as *const u8;
_4 = Offset(_3, 2_usize); _5 = _4 as *const u32; _0 = copy (*_5); return`. -/
def derefMisalignedEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::deref_misaligned_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u32DeclLM31, Witness.u64Decl, Witness.rawPtrConstU64Decl,
    Witness.rawPtrConstU8Decl, Witness.rawPtrConstU8Decl, Witness.rawPtrConstU32Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1), Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.storageLive 3), Witness.mkStmt (.storageLive 4),
      Witness.mkStmt (.storageLive 5),
      Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 42)))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.rawPtr .not (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 3)
        (.cast .ptrToPtr (.copy (Witness.local_ 2)) Witness.rawPtrConstU8Ty)),
      Witness.mkStmt (.assign (Witness.local_ 4)
        (.binaryOp .offset (.copy (Witness.local_ 3)) (.constant (Witness.constUsizeLM31 2)))),
      Witness.mkStmt (.assign (Witness.local_ 5)
        (.cast .ptrToPtr (.copy (Witness.local_ 4)) Witness.rawPtrConstU32Ty)),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 5))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def derefMisalignedPreAnneal : MachineState :=
  mkWitState derefMisalignedEntryBody 6
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit, .uninit] [] 1

def derefMisalignedPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame derefMisalignedEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy Witness.u64Ty emptyLayoutTable) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 6⟩ }

def derefMisalignedPreMiri : AnnealStepState :=
  { stack := ⟨#[derefMisalignedPreMiriFrame]⟩, machine := AnnealMachine.empty }

private theorem derefMisaligned_pre_stateRel_and_imm :
    StateRel derefMisalignedEntryBody derefMisalignedPreAnneal derefMisalignedPreMiri ∧
    ∀ tf, derefMisalignedPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk derefMisalignedPreMiriFrame rfl rfl
      ⟨translateTy Witness.u32TyLM31 emptyLayoutTable, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => simp [derefMisalignedPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 | 4 | 5 =>
      have hs : slot = .uninit := by
        simpa [derefMisalignedPreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [derefMisalignedPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = Witness.u64Decl := by
        simpa [derefMisalignedEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by
        simpa [derefMisalignedPreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy Witness.u64Ty emptyLayoutTable) } := by
        simpa [derefMisalignedPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy Witness.u64Ty emptyLayoutTable))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 6 => simp [derefMisalignedEntryBody, get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : derefMisalignedPreMiriFrame = tf := by simpa [derefMisalignedPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 => simp [derefMisalignedPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 6 => simp [derefMisalignedPreMiriFrame] at hmls

private theorem derefMisaligned_prefix_anneal :
    runAnnealBounded derefMisalignedEntryBody 6
      (initMachineState derefMisalignedEntryBody []) =
      .running derefMisalignedPreAnneal := rfl

private theorem derefMisaligned_prefix_miri :
    runLoopFuel (annealMiriHooks derefMisalignedEntryBody) 6
      (miriEntryState derefMisalignedEntryBody) =
      .running derefMisalignedPreMiri := rfl

/-- **Stage-1 lockstep from entry** (`ub_unaligned_ptr_read_u32`,
`derefMisalignedEntryBody`): from `initMachineState` / `miriEntryState`, both
machines run the 6-step `StorageLive` + `_1 = 42_u64` prefix and 4 raw-pointer /
`Offset(_, 2_usize)` / cast steps in lockstep, then reject the misaligned in-bounds
`u32` read at byte offset `2` with undefined behavior (`step_deref_misaligned_miri_ub`). -/
theorem w3_deref_misaligned_ub :
    AgreeUB derefMisalignedEntryBody (annealMiriHooks derefMisalignedEntryBody)
      (initMachineState derefMisalignedEntryBody [])
      (miriEntryState derefMisalignedEntryBody) := by
  let b := derefMisalignedEntryBody
  have hpa := derefMisaligned_prefix_anneal
  have hpm := derefMisaligned_prefix_miri
  obtain ⟨hrel₀, himm₀⟩ := derefMisaligned_pre_stateRel_and_imm
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let bor := [entry.toBorrowEntry]
  let s₁ := mkWitState b 7
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b derefMisalignedPreAnneal = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : derefMisalignedPreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨derefMisalignedPreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 8
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₂
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := Witness.rawPtrConstU8Decl) (ptrDecl := Witness.rawPtrConstU8Decl)
      (tgtDecl := Witness.u64Decl) (rhsTy := Witness.usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
      (fun tf₂ _ => .of_wt (constUsize_wt_mdw b tf₂ 2 (by decide)))
      (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 2)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 9
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := hsim₃.step_of_anneal_step hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkWitState b 10
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .init ptr2] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₄
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  obtain ⟨tf₄, htf₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
  obtain ⟨_, _, hsh₄⟩ :=
    (halloc₄.local_alloc_sync tf₄ htf₄ _ (.head _)).1 (.init (.scalar ⟨42, 8⟩)) rfl nofun
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh₄ Witness.u64Decl rfl
  have hinb : 2 +
      (translateTy Witness.u32DeclLM31.ty b.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hshape_la.byteSize_eq]; decide
  obtain ⟨m₅, msg, hm₅⟩ :=
    step_deref_misaligned_miri_ub hrel₄ (Or.inl rfl) rfl rfl
      (dstDecl := Witness.u32DeclLM31) (ptrDecl := Witness.rawPtrConstU32Decl) rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
      (fun tf htf => himm₄ tf htf 5 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 2 })
      rfl (.head _) rfl hfind_la hinb (by decide)
  have hs₅ : stepMirFn b s₄ = .fail .ub := rfl
  exact agreeUB_of_paths hpa hpm
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))) hs₅
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_eq_singleton htf₄) (.refl _)))))
    hm₅ rfl

/-- Entry-to-return MIR body for `ub_ptr_offset_oob_write`:
`StorageLive(_1.._3); _1 = const 42_u64; _2 = &raw mut _1;
_3 = Offset(move _2, const 1_usize); (*_3) = const 99_u64; return`. -/
def derefOobWriteEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::deref_oob_write_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u64Decl, Witness.u64Decl, Witness.rawPtrMutU64Decl,
    Witness.rawPtrMutU64Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1), Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.storageLive 3),
      Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 42)))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.rawPtr .mut (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 3)
        (.binaryOp .offset (.move (Witness.local_ 2)) (.constant (Witness.constUsizeLM31 1)))),
      Witness.mkStmt (.assign (Witness.derefLocal 3) (.use (.constant (Witness.constU64 99))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Entry-to-return MIR body for `ub_ptr_offset_negative_before_start`:
`StorageLive(_1.._3); _1 = const 42_u64; _2 = &raw const _1;
_3 = Offset(copy _2, const -1_isize); return`. -/
def ptrOffsetNegOobEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::ptr_offset_neg_oob_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u64Decl, Witness.u64Decl, Witness.rawPtrConstU64Decl,
    Witness.rawPtrConstU64Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1), Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.storageLive 3),
      Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 42)))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.rawPtr .not (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 3)
        (.binaryOp .offset (.copy (Witness.local_ 2)) (.constant Witness.constNegOneIsizeLM31)))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Entry-to-return MIR body for `ub_transmute_invalid_bool_through_ptr`:
`StorageLive(_1.._3); _1 = const 2_u8; _2 = &raw const _1;
_3 = copy _2 as *const bool; _0 = copy (*_3); return`. -/
def invalidBoolPtrDerefEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::invalid_bool_ptr_deref_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.boolDeclLM31, Witness.u8DeclLM31, Witness.rawPtrConstU8Decl,
    Witness.rawPtrConstBoolDecl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1), Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.storageLive 3),
      Witness.mkStmt (.assign (Witness.local_ 1) (.use (cU8 2))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.rawPtr .not (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 3)
        (.cast .ptrToPtr (.copy (Witness.local_ 2)) Witness.rawPtrConstBoolTy)),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 3))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private def fourLocalEntryPreAnneal (b : CapturedMir) (sc : MirAst.ScalarInt) : MachineState :=
  mkWitState b 4 [.uninit, .init (.scalar sc), .uninit, .uninit] [] 1

private def fourLocalEntryPreMiriFrame (b : CapturedMir) (t1 : Ty)
    (msc : Miri.Memory.ScalarInt) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame b) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt msc))),
        layout := some (translateTy t1 emptyLayoutTable) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 4⟩ }

private def fourLocalEntryPreMiri (b : CapturedMir) (t1 : Ty)
    (msc : Miri.Memory.ScalarInt) : AnnealStepState :=
  { stack := ⟨#[fourLocalEntryPreMiriFrame b t1 msc]⟩, machine := AnnealMachine.empty }

private theorem fourLocalEntry_pre_stateRel_and_imm (b : CapturedMir)
    (d0 d1 d2 d3 : LocalDecl) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
    (hlds : b.localDecls = [d0, d1, d2, d3]) (hlay : b.layouts = emptyLayoutTable)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy d1.ty emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes)
    (hbool : d1.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : d1.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    StateRel b (fourLocalEntryPreAnneal b sc) (fourLocalEntryPreMiri b d1.ty msc) ∧
    ∀ tf, (fourLocalEntryPreMiri b d1.ty msc).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk (fourLocalEntryPreMiriFrame b d1.ty msc) rfl rfl
      ⟨entryReturnLayout b, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | _ + 4 => simp [fourLocalEntryPreMiriFrame] at hi)
    refine ⟨rfl, rfl, by simp [fourLocalEntryPreAnneal, mkWitState, hlds],
      by simp [fourLocalEntryPreMiriFrame, hlds], ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rw [hlds] at hdecl
    match i with
    | 0 | 2 | 3 =>
      have hs : slot = .uninit := by
        simpa [fourLocalEntryPreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [fourLocalEntryPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = d1 := by simpa [get?] using hdecl.symm
      have hs : slot = .init (.scalar sc) := by
        simpa [fourLocalEntryPreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt msc))),
            layout := some (translateTy d1.ty emptyLayoutTable) } := by
        simpa [fourLocalEntryPreMiriFrame] using hmls.symm
      subst hd hs hm; rw [hlay]
      exact .immediate _ _ (some (translateTy decl.ty emptyLayoutTable))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel hsz hbool hchar⟩)
    | _ + 4 => simp [get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : fourLocalEntryPreMiriFrame b d1.ty msc = tf := by
      simpa [fourLocalEntryPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 => simp [fourLocalEntryPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 4 => simp [fourLocalEntryPreMiriFrame] at hmls

private theorem derefOobWrite_prefix_anneal :
    runAnnealBounded derefOobWriteEntryBody 4
      (initMachineState derefOobWriteEntryBody []) =
      .running (fourLocalEntryPreAnneal derefOobWriteEntryBody ⟨42, 8⟩) := rfl

private theorem derefOobWrite_prefix_miri :
    runLoopFuel (annealMiriHooks derefOobWriteEntryBody) 4
      (miriEntryState derefOobWriteEntryBody) =
      .running (fourLocalEntryPreMiri derefOobWriteEntryBody Witness.u64Ty Witness.lm31Scalar42) := rfl

/-- **Stage-1 lockstep from entry** (`ub_ptr_offset_oob_write`,
`derefOobWriteEntryBody`): from `initMachineState` / `miriEntryState`, both
machines execute `StorageLive(_1.._3); _1 = 42_u64; _2 = &raw mut _1;
_3 = Offset(move _2, 1_usize)` (`sizeof::<u64>() = 8` stride) in lockstep and
reject the out-of-bounds write `(*_3) = 99_u64` with undefined behavior
(`step_deref_write_oob_simulation`). -/
theorem w3_deref_oob_write_ub :
    AgreeUB derefOobWriteEntryBody (annealMiriHooks derefOobWriteEntryBody)
      (initMachineState derefOobWriteEntryBody [])
      (miriEntryState derefOobWriteEntryBody) := by
  let b := derefOobWriteEntryBody
  have hpa := derefOobWrite_prefix_anneal
  have hpm := derefOobWrite_prefix_miri
  obtain ⟨hrel₀, himm₀⟩ := fourLocalEntry_pre_stateRel_and_imm b
    Witness.u64Decl Witness.u64Decl Witness.rawPtrMutU64Decl Witness.rawPtrMutU64Decl
    ⟨42, 8⟩ Witness.lm31Scalar42 rfl rfl Witness.lm31_scalarRel42 rfl
    (fun h => nomatch h) (fun h => nomatch h)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let bor := [entry.toBorrowEntry]
  let s₁ := mkWitState b 5 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨42, 8⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : (fourLocalEntryPreAnneal b ⟨42, 8⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(fourLocalEntryPreMiri b Witness.u64Decl.ty Witness.lm31Scalar42).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  obtain ⟨hsim₂, hs₂_eq, m₂, tf₂, _, hm₂, htf₂, hval₂⟩ :=
    step_binOp_offset_stride_simulation hrel₁ hphase (Or.inr rfl) rfl rfl
      (dstDecl := Witness.rawPtrMutU64Decl) (ptrDecl := Witness.rawPtrMutU64Decl)
      (tgtDecl := Witness.u64Decl) (rhsTy := Witness.usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wt_mdw b tf 1 (by decide)))
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₂ := mkWitState b 6 [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr8] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := hs₂_eq
  obtain ⟨m₂', hm₂_eq, hrel₂⟩ := hsim₂.step_of_anneal_step hs₂
  have hm₂_inj : m₂' = m₂ := (Prod.mk.inj (hm₂_eq.symm.trans hm₂)).1; subst m₂'
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf htf mls hmls mp hmp
    rw [htf₂] at htf; injection htf with h1; injection h1 with h2; subst h2
    rw [hmls] at hval₂; injection hval₂ with hv; rw [hv] at hmp; cases hmp
  obtain ⟨tf₂', htf₂', _, _, _, _, _, _, _, _, halloc₂, _⟩ := id hrel₂
  obtain ⟨_, _, hsh₂⟩ := (halloc₂.local_alloc_sync tf₂' htf₂' _ (.head _)).1
    (.init (.scalar ⟨42, 8⟩)) rfl (by rintro ⟨⟩)
  obtain ⟨la₂, hfind₂, _, _, hshape₂⟩ := hsh₂ Witness.u64Decl rfl
  obtain ⟨hsim₃, hs₃⟩ := step_deref_write_oob_simulation hrel₂ hphase rfl rfl
    (ptrDecl := Witness.rawPtrMutU64Decl) (valTy := Witness.u64Ty) rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => .of_wt (constU64_wt_mdw b tf 99 (by decide)))
    himm₂_3 (ptrVal := { allocId := 1, offsetBytes := 8 }) rfl (.head _) rfl hfind₂
    (by rw [hshape₂.byteSize_eq]; decide)
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM3_1_ub_of_anneal_ub hsim₃ hs₃
  exact agreeUB_of_paths hpa hpm
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hs₃
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_eq_singleton htf₂') (.refl _)))
    hm₃ rfl

private theorem ptrOffsetNegOob_prefix_anneal :
    runAnnealBounded ptrOffsetNegOobEntryBody 4
      (initMachineState ptrOffsetNegOobEntryBody []) =
      .running (fourLocalEntryPreAnneal ptrOffsetNegOobEntryBody ⟨42, 8⟩) := rfl

private theorem ptrOffsetNegOob_prefix_miri :
    runLoopFuel (annealMiriHooks ptrOffsetNegOobEntryBody) 4
      (miriEntryState ptrOffsetNegOobEntryBody) =
      .running (fourLocalEntryPreMiri ptrOffsetNegOobEntryBody Witness.u64Ty Witness.lm31Scalar42) := rfl

/-- **Stage-1 lockstep from entry** (`ub_ptr_offset_negative_before_start`,
`ptrOffsetNegOobEntryBody`): from `initMachineState` / `miriEntryState`, both
machines promote `_1` via `&raw const _1` and reject `Offset(copy _2, -1_isize)`
before byte offset `0` with undefined behavior
(`step_binOp_offset_neg_oob_ub_simulation`). -/
theorem w3_ptr_offset_neg_before_start_ub :
    AgreeUB ptrOffsetNegOobEntryBody (annealMiriHooks ptrOffsetNegOobEntryBody)
      (initMachineState ptrOffsetNegOobEntryBody [])
      (miriEntryState ptrOffsetNegOobEntryBody) := by
  let b := ptrOffsetNegOobEntryBody
  have hpa := ptrOffsetNegOob_prefix_anneal
  have hpm := ptrOffsetNegOob_prefix_miri
  obtain ⟨hrel₀, himm₀⟩ := fourLocalEntry_pre_stateRel_and_imm b
    Witness.u64Decl Witness.u64Decl Witness.rawPtrConstU64Decl Witness.rawPtrConstU64Decl
    ⟨42, 8⟩ Witness.lm31Scalar42 rfl rfl Witness.lm31_scalarRel42 rfl
    (fun h => nomatch h) (fun h => nomatch h)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let bor := [entry.toBorrowEntry]
  let s₁ := mkWitState b 5 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨42, 8⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : (fourLocalEntryPreAnneal b ⟨42, 8⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(fourLocalEntryPreMiri b Witness.u64Decl.ty Witness.lm31Scalar42).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  obtain ⟨_, hs₂, m₂, msg, hm₂⟩ :=
    step_binOp_offset_neg_oob_ub_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
      (dstDecl := Witness.rawPtrConstU64Decl) (ptrDecl := Witness.rawPtrConstU64Decl)
      (rhsTy := Witness.isizeTyLM31)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inr rfl)
      (fun tf _ => .of_wt (constNegOneIsize_wt_mdw b tf))
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar_mdw)
      (by
        intro ptrVal sc _ _ _ hptr hsc _ _ _
        have hp : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init_mdw hptr
        have hs : sc = ⟨2 ^ 64 - 1, 8⟩ := by
          dsimp [evalOperand, Witness.constNegOneIsizeLM31] at hsc
          injection hsc with h1 _; injection h1 with h2; exact h2.symm
        subst hp hs
        exact Or.inl ⟨by decide, Or.inr (Or.inl (by decide))⟩)
  exact agreeUB_of_paths hpa hpm
    (.step .silent hs₁ (.refl _)) hs₂
    (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _))
    hm₂ rfl

private theorem invalidBoolPtrDeref_prefix_anneal :
    runAnnealBounded invalidBoolPtrDerefEntryBody 4
      (initMachineState invalidBoolPtrDerefEntryBody []) =
      .running (fourLocalEntryPreAnneal invalidBoolPtrDerefEntryBody ⟨2, 1⟩) := rfl

private theorem invalidBoolPtrDeref_prefix_miri :
    runLoopFuel (annealMiriHooks invalidBoolPtrDerefEntryBody) 4
      (miriEntryState invalidBoolPtrDerefEntryBody) =
      .running (fourLocalEntryPreMiri invalidBoolPtrDerefEntryBody Witness.u8TyLM31
        (Miri.Memory.ScalarInt.ofUInt8 2)) := rfl

/-- **Stage-1 lockstep from entry** (`ub_transmute_invalid_bool_through_ptr`,
`invalidBoolPtrDerefEntryBody`): from `initMachineState` / `miriEntryState`,
`_1 = 2_u8; _2 = &raw const _1; _3 = _2 as *const bool; _0 = copy (*_3)` runs in
lockstep and raises undefined behavior at the invalid `bool` load in both
machines (`step_deref_invalid_bool_simulation`). -/
theorem w3_invalid_bool_ptr_deref_ub :
    AgreeUB invalidBoolPtrDerefEntryBody (annealMiriHooks invalidBoolPtrDerefEntryBody)
      (initMachineState invalidBoolPtrDerefEntryBody [])
      (miriEntryState invalidBoolPtrDerefEntryBody) := by
  let b := invalidBoolPtrDerefEntryBody
  have hrel2 : ScalarRel ⟨2, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 2) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hpa := invalidBoolPtrDeref_prefix_anneal
  have hpm := invalidBoolPtrDeref_prefix_miri
  obtain ⟨hrel₀, himm₀⟩ := fourLocalEntry_pre_stateRel_and_imm b
    Witness.boolDeclLM31 Witness.u8DeclLM31 Witness.rawPtrConstU8Decl Witness.rawPtrConstBoolDecl
    ⟨2, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 2) rfl rfl hrel2 rfl
    (fun h => nomatch h) (fun h => nomatch h)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let bor := [entry.toBorrowEntry]
  let s₁ := mkWitState b 5 [.uninit, .init (.scalar ⟨2, 1⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨2, 1⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : (fourLocalEntryPreAnneal b ⟨2, 1⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(fourLocalEntryPreMiri b Witness.u8DeclLM31.ty
      (Miri.Memory.ScalarInt.ofUInt8 2)).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 6 [.uninit, .init (.scalar ⟨2, 1⟩), .init ptr0, .init ptr0] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₂
  obtain ⟨_, himm₂_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  obtain ⟨hsim₃, hs₃⟩ := step_deref_invalid_bool_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
    (dstDecl := Witness.boolDeclLM31) (ptrDecl := Witness.rawPtrConstBoolDecl)
    (tgtDecl := Witness.u8DeclLM31)
    rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    rfl rfl (.head _) rfl rfl (Or.inl rfl) rfl (by decide)
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM3_1_ub_of_anneal_ub hsim₃ hs₃
  exact agreeUB_of_paths hpa hpm
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hs₃
    (.step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _)))
    hm₃ rfl

/-- Entry-to-return MIR body for `pass_ptr_offset_within_array` (Stage-1 positive
non-byte `BinOp.Offset` stride):
`StorageLive(_1.._4); _1 = const (300 * 2^32 + 10)_u64; _2 = &raw const _1;
_3 = copy _2 as *const u32; _4 = Offset(copy _3, const 1_usize);
_0 = copy (*_4); return` returning `300_u32`. -/
def ptrOffsetStrideEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::ptr_offset_stride_read_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u32DeclLM31, Witness.u64Decl, Witness.rawPtrConstU64Decl,
    Witness.rawPtrConstU32Decl, Witness.rawPtrConstU32Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1), Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.storageLive 3), Witness.mkStmt (.storageLive 4),
      Witness.mkStmt (.assign (Witness.local_ 1)
        (.use (.constant (Witness.constU64 1288490188810)))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.rawPtr .not (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 3)
        (.cast .ptrToPtr (.copy (Witness.local_ 2)) Witness.rawPtrConstU32Ty)),
      Witness.mkStmt (.assign (Witness.local_ 4)
        (.binaryOp .offset (.copy (Witness.local_ 3)) (.constant (Witness.constUsizeLM31 1)))),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 4))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private def ptrOffsetStridePreAnneal : MachineState :=
  mkWitState ptrOffsetStrideEntryBody 5
    [.uninit, .init (.scalar ⟨1288490188810, 8⟩), .uninit, .uninit, .uninit] [] 1

private def ptrOffsetStridePreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame ptrOffsetStrideEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar
          (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1288490188810)))),
        layout := some (translateTy Witness.u64Ty emptyLayoutTable) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 5⟩ }

private def ptrOffsetStridePreMiri : AnnealStepState :=
  { stack := ⟨#[ptrOffsetStridePreMiriFrame]⟩, machine := AnnealMachine.empty }

private theorem ptrOffsetStride_prefix_anneal :
    runAnnealBounded ptrOffsetStrideEntryBody 5
      (initMachineState ptrOffsetStrideEntryBody []) =
      .running ptrOffsetStridePreAnneal := rfl

private theorem ptrOffsetStride_prefix_miri :
    runLoopFuel (annealMiriHooks ptrOffsetStrideEntryBody) 5
      (miriEntryState ptrOffsetStrideEntryBody) =
      .running ptrOffsetStridePreMiri := rfl

/-- **Stage-1 positive `BinOp.Offset` stride lockstep from entry**
(`pass_ptr_offset_within_array`, `ptrOffsetStrideEntryBody`): from
`initMachineState` / `miriEntryState`, both machines scale `Offset(*const u32, 1_usize)`
by `sizeof::<u32>() = 4` bytes (`step_binOp_offset_stride_simulation`), read the
aligned second `u32` word `300_u32` (`1288490188810 = 300 * 2^32 + 10`) via
`step_deref_read_narrower_simulation`, and return `300_u32` (`AgreeReturns`). -/
theorem w3_ptr_offset_stride_read_returns :
    AgreeReturns ptrOffsetStrideEntryBody (annealMiriHooks ptrOffsetStrideEntryBody)
      (initMachineState ptrOffsetStrideEntryBody [])
      (miriEntryState ptrOffsetStrideEntryBody)
      (.scalar ⟨300, 4⟩)
      (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 300)))) := by
  let b := ptrOffsetStrideEntryBody
  let scInit : MirAst.ScalarInt := ⟨1288490188810, 8⟩
  let mscInit := Miri.Memory.ScalarInt.ofUInt64 1288490188810
  have hscRel : ScalarRel scInit mscInit :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hpa := ptrOffsetStride_prefix_anneal
  have hpm := ptrOffsetStride_prefix_miri
  have hrel₀ : StateRel b ptrOffsetStridePreAnneal ptrOffsetStridePreMiri := by
    refine StateRel.mk ptrOffsetStridePreMiriFrame rfl rfl
      ⟨translateTy Witness.u32TyLM31 emptyLayoutTable, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => simp [ptrOffsetStridePreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 | 4 =>
      have hs : slot = .uninit := by
        simpa [ptrOffsetStridePreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [ptrOffsetStridePreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = Witness.u64Decl := by
        simpa [b, ptrOffsetStrideEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar scInit) := by
        simpa [ptrOffsetStridePreAnneal, mkWitState, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt mscInit))),
            layout := some (translateTy Witness.u64Ty emptyLayoutTable) } := by
        simpa [ptrOffsetStridePreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy Witness.u64Ty emptyLayoutTable))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hscRel rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 5 => simp [b, ptrOffsetStrideEntryBody, get?] at hdecl
  have himm₀ : ∀ tf, ptrOffsetStridePreMiri.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hv
    have htf : ptrOffsetStridePreMiriFrame = tf := by simpa [ptrOffsetStridePreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 | 4 => simp [ptrOffsetStridePreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 5 => simp [ptrOffsetStridePreMiriFrame] at hmls
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr4 := Value.ptr { allocId := 1, offsetBytes := 4 } 8
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let bor := [entry.toBorrowEntry]
  let s₁ := mkWitState b 6
    [.uninit, .init (.scalar scInit), .init ptr0, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b ptrOffsetStridePreAnneal = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : ptrOffsetStridePreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨ptrOffsetStridePreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 7
    [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₂
  obtain ⟨_, himm_s₂⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := Witness.rawPtrConstU32Decl) (ptrDecl := Witness.rawPtrConstU32Decl)
      (tgtDecl := Witness.u64Decl) (rhsTy := Witness.usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wt_mdw b tf 1 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 8
    [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := hsim₃.step_of_anneal_step hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := Witness.step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
  obtain ⟨hsim₄, hs₄_fn⟩ := step_deref_read_narrower_simulation hrel₃ hphase (Or.inl rfl) rfl rfl
    (dstDecl := Witness.u32DeclLM31) (ptrDecl := Witness.rawPtrConstU32Decl)
    (tgtDecl := Witness.u64Decl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩)))
    (fun tf htf => ⟨himm₃ tf htf 0 (by decide), himm₃ tf htf 4 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
    rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (by decide) (by decide) (fun h => by cases h) (fun h => by cases h)
  have hs₄ := hs₄_fn (by rintro ⟨⟩); dsimp only [] at hs₄
  have hacc4 : (translateTy Witness.u32DeclLM31.ty b.layouts).layout.size.bytes.toNat = 4 := rfl
  have hbits4 : scInit.bits / 2 ^ (8 * ({ allocId := 1, offsetBytes := 4 } : ProvenancePtr).offsetBytes) %
      scalarModulus 4 = 300 := by decide
  rw [hacc4, hbits4] at hs₄
  let map₄ := derefReadNextAllocMap s₃.frame.locals [entry] 4
  let s₄ := advanceStmt s₃ (s₃.frame.locals.set 0 (.init (.scalar ⟨300, 4⟩)))
    ({ s₃.memory with borrows := List.map AllocMapEntry.toBorrowEntry map₄ })
  have hs₄_eq : stepMirFn b s₃ = .step s₄ := hs₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.step_of_anneal_step hs₄_eq
  obtain ⟨_, himm_s₄⟩ := Witness.step_assign_use_preserves hrel₃ (by rintro _ ⟨⟩) rfl rfl hm₄
  have himm₄_0 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm_s₄ tf₃ tf htf₃ htf 0 (himm₃ tf₃ htf₃ 0 (by decide))
  have hsim₅ := step_terminator_goto_return_lm3_1_simulation hrel₄ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, Witness.u32DeclLM31, rfl, (by rintro _ _ ⟨⟩), (by decide), himm₄_0⟩))
  have ha₅ : stepMirFn b s₄ = .retNormal (.scalar ⟨300, 4⟩) s₄.memory := rfl
  rw [ha₅] at hsim₅
  generalize hm_res : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₄ = mRes at hsim₅
  cases hsim₅ with
  | retRoot decl₀ _ imm₀ _ m' hdecl₀ hop₀ himmRel₀ hm₅ =>
    subst hm₅
    have hd₀ : decl₀ = Witness.u32DeclLM31 := Option.some.inj hdecl₀.symm; subst hd₀
    cases himmRel₀ with
    | scalar _ msc hsc _ _ _ =>
      have hrel300 : ScalarRel ⟨300, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 300) :=
        ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
      have hmsc : msc = Miri.Memory.ScalarInt.ofUInt32 300 :=
        scalarInt_eq_of_scalarRel_mdw hsc hrel300
      subst hmsc
      exact agreeReturns_of_paths hpa hpm
        (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄_eq (.refl _)))))
        ha₅
        (.step hm₁ (frames_ne_of_step_ok_true hm₂)
          (.step hm₂ (frames_ne_of_step_ok_true hm₃)
            (.step hm₃ (frames_ne_of_step_ok_true hm₄)
              (.step hm₄ (frames_ne_of_step_ok_true hm_res) (.refl _)))))
        hm_res rfl (by change (annealControlHooks.returnOperand () m₄).2 = _; rw [hop₀])

/-- Entry-prefixed 4-local MIR body (`bb0: StorageLive(_1.._3); _1 = 42_u64; goto bb1;
bb1: stmts; term1; bb2: return`). -/
def ptr4EntryBody (defPath : String) (d₀ d₂ d₃ : RigidTy)
    (stmts : List MirAst.Statement) (term1 : TerminatorKind) : CapturedMir where
  defPath := defPath
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf d₀, WitnessLM4_2.declOf WitnessLM4_2.u64K,
    WitnessLM4_2.declOf d₂, WitnessLM4_2.declOf d₃]
  basicBlocks := [
    { statements := [
        WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
        WitnessLM4_2.mkStmt42 (.storageLive 3),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 42 8))))]
      terminator := WitnessLM4_2.mkTerm42 (.goto 1), isCleanup := false },
    { statements := stmts, terminator := WitnessLM4_2.mkTerm42 term1, isCleanup := false },
    { statements := [], terminator := WitnessLM4_2.mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def ptr4EntryPreAnneal (b : CapturedMir) : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState b []).memory }

def ptr4EntryPreMiriFrame (b : CapturedMir) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame b) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨1, 0⟩ }

def ptr4EntryPreMiri (b : CapturedMir) : AnnealStepState :=
  { stack := ⟨#[ptr4EntryPreMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem ptr4Entry_stateRel_and_imm (b : CapturedMir) (defPath : String) (d₀ d₂ d₃ : RigidTy)
    (stmts : List MirAst.Statement) (term1 : TerminatorKind)
    (hb : b = ptr4EntryBody defPath d₀ d₂ d₃ stmts term1) :
    StateRel b (ptr4EntryPreAnneal b) (ptr4EntryPreMiri b) ∧
    ∀ tf, (ptr4EntryPreMiri b).stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  subst hb
  let b := ptr4EntryBody defPath d₀ d₂ d₃ stmts term1
  refine ⟨?_, ?_⟩
  · refine StateRel.mk (ptr4EntryPreMiriFrame b) rfl rfl ⟨entryReturnLayout b, rfl⟩ ?_
      rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | _ + 4 => simp [ptr4EntryPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 =>
      have hs : slot = .uninit := by simpa [ptr4EntryPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [ptr4EntryPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [ptr4EntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by
        simpa [ptr4EntryPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [ptr4EntryPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 4 => simp [ptr4EntryBody, get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : ptr4EntryPreMiriFrame b = tf := by simpa [ptr4EntryPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 => simp [ptr4EntryPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 4 => simp [ptr4EntryPreMiriFrame] at hmls

/-- `StorageLive(_1.._3); _1 = 42_u64; goto bb1; bb1: _0 = &raw mut _1; return`:
both machines return the raw pointer to `_1` from program entry
(`step_terminator_return_rawPtr_lm3_1_simulation`), with `ImmediateRelLM3_1`-related
return values. -/
def rawPtrReturnBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::raw_ptr_return"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    .return_

theorem w3_rawPtr_return :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns rawPtrReturnBody (annealMiriHooks rawPtrReturnBody)
        (initMachineState rawPtrReturnBody [])
        (miriEntryState rawPtrReturnBody)
        (.ptr { allocId := 1, offsetBytes := 0 } 8) (.immediate imm0) ∧
      get? rawPtrReturnBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_1
        [rawPtrAllocMapEntry rawPtrReturnBody.localDecls rawPtrReturnBody.layouts .mut 1 1
          Witness.lm31AllocId1]
        decl0.ty rawPtrReturnBody.layouts (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0 := by
  let b := rawPtrReturnBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b "lm_4_3_witness::raw_ptr_return"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
      (.rawPtr .mut (WitnessLM4_2.local42 1)))] .return_ rfl
  have himm₀ : ∀ tf, (ptr4EntryPreMiri b).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 0, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init (.scalar ⟨42, 8⟩), .uninit, .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ (fun _ h => nomatch h) rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4EntryPreAnneal b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4EntryPreMiri b).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 0 :=
    fun tf₁ htf₁ => himm₁_step _ tf₁ rfl htf₁ 0 (by decide) (himm₀_all _ rfl 0)
  have hret : stepMirFn b s₁ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₁.memory :=
    rfl
  have hsim₂ := step_terminator_return_rawPtr_lm3_1_simulation hrel₁ (fun _ h => nomatch h)
    rfl rfl rfl rfl rfl rfl rfl himm₁
  rw [hret] at hsim₂
  obtain ⟨decl0, imm0, hdecl0, hop, himm, hmret⟩ := hsim₂.retNormal_rel
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 5) rfl rfl
    (.step .silent hs₁ (.refl _)) hret
    (.step hm₁ (frames_ne_of_step_ok_true hmret) (.refl _))
    hmret rfl (by change (annealControlHooks.returnOperand () m₁).2 = _; rw [hop])

/-- `arith_offset::<u64>(copy ptrIdx, const count_isize) -> bb2` into `_0` (for `ptr4EntryBody`). -/
def arithOffsetEntryTerm (ptrIdx : Local) (countBits : Nat) : TerminatorKind :=
  .call (.constant (WitnessLM4_2.fnItem "core::intrinsics::arith_offset" WitnessLM4_2.u64K))
    [.copy (WitnessLM4_2.local42 ptrIdx),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.isizeK countBits 8)]
    (WitnessLM4_2.local42 0) (some 2) .unreachable

/-- `StorageLive(_1.._3); _1 = 42_u64; goto bb1; bb1: _0 = arith_offset(copy _2, 1) -> bb2`
with `_2` uninitialized. -/
def arithOffsetUninitBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::arith_offset_uninit"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K []
    (arithOffsetEntryTerm 2 1)

/-- `arith_offset` on an uninitialized pointer is undefined behavior in both machines
from program entry. -/
theorem w3_arith_offset_uninit_ub :
    AgreeUB arithOffsetUninitBody (annealMiriHooks arithOffsetUninitBody)
      (initMachineState arithOffsetUninitBody [])
      (miriEntryState arithOffsetUninitBody) := by
  let b := arithOffsetUninitBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b "lm_4_3_witness::arith_offset_uninit"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K []
    (arithOffsetEntryTerm 2 1) rfl
  have hsim := call_intrinsic_arithOffset_stage1_simulation hrel₀.toLM3_1 (fun _ h => nomatch h)
    rfl rfl rfl rfl rfl rfl (Or.inl (by decide)) rfl rfl (fun tf htf => himm₀_all tf htf 2)
    (fun _ h => by simp [ptr4EntryPreAnneal, get?] at h)
    WitnessLM4_2.isize_integral
    (fun tf _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.isize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf)
    rfl rfl (fun tf htf => himm₀_all tf htf 0) rfl rfl (by decide)
    (fun _ _ hp _ _ => by simp [ptr4EntryPreAnneal, get?] at hp)
  have hfail : stepMirFn b (ptr4EntryPreAnneal b) = .fail .ub := rfl
  rw [hfail] at hsim
  obtain ⟨m', msg, herr⟩ := hsim.miri_ub_of_anneal_ub
  exact agreeUB_of_paths (p := 5) rfl rfl (.refl _) hfail (.refl _) herr rfl

/-! ## 4. Tree Borrows -/

/-- `I-10` child write then parent read through a two-level reborrow
(`tb_child_write_then_parent_read`, `lm32ReborrowTreeBody`):
```text
bb0: _2 = &mut _1; _3 = &mut (*_2); (*_3) = const 99_u64; _0 = copy (*_2); return
```
From the `StateRel`-related pre-states `Witness.mkPre4AnnealLM32` /
`Witness.mkPre4MiriLM32` with `_1 = 42_u64`, both machines run to a normal return
of `99_u64` (with `ImmediateRelLM3_2`-related return values), tracking the
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

/-! ### Reference bodies from the entry state

The traces below start at `initMachineState` / `miriEntryState`. Kernel
evaluation checks the allocation-free prefix of `StorageLive` and constant
assignments, and the `LM-3.2` step theorems check every later step. The helpers
track `lean-miri`'s allocation supply: the only allocation, id `1`, belongs to
the borrowed local, so every other local stays immediate. -/

/-- A `StepRelLM3_2` step whose Anneal side is a normal step has a normal
`lean-miri` step to `StateRelLM3_2`-related states. -/
private theorem stepRelLM3_2_step_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_2 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2 body s' m' allocMap := by
  generalize ha_eq : aRes = aNode at hsim
  cases hsim with
  | step s₁ m' hrel =>
    rw [ha] at ha_eq; injection ha_eq with hrun; injection hrun with hs; subst hs
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => rw [ha] at ha_eq; cases ha_eq
  | ub _ _ => rw [ha] at ha_eq; cases ha_eq

/-- After `_dst = &bk _target` from `StateRel`-related states with an empty
`lean-miri` machine, `lean-miri`'s allocation supply is ready with next id `2`
(the promoted target is allocation `1`). -/
private theorem step_ref_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {bk : BorrowKind} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hm_empty : m.machine = AnnealMachine.empty)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
  have hsupply : AllocIdSupplyReady m.machine.memory := hm_empty ▸ AllocIdSupplyReady.empty
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRel body m.machine s.frame tfa := hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨_, mls_t, _, hlt_t, _, hmls_t, hmls_t_eq, hloc_t⟩ := hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.layout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hval_tb : (tfb.locals[targetIdx]'(by rw [cacheFrameLocalLayout_size]; exact hlt_t)).value =
      mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  cases hloc_t with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
  | dead _ _ =>
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl
      (by rw [cacheFrameLocalLayout_size]; exact hlt_t) hval_tb
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_ref_force_error (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  | immediate _ imm _ _ hval =>
    have hlt_tb : targetIdx < tfb.locals.size := by
      rw [cacheFrameLocalLayout_size]; exact hlt_t
    have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
        some (translateTy targetDecl.ty body.layouts) := by
      simp [tfb, cacheFrameLocalLayout]
    obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
    obtain ⟨mem', hres⟩ := hsupply.reserve_eq
    let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
    obtain ⟨alloc', hfill⟩ :
        ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
          (imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
          ∃ sc, imm = .scalar sc ∧
            Miri.Memory.Allocation.writeScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
              (allocation.withExtra none) = .ok () alloc' := by
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · exact ⟨allocation.withExtra none, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨sc, msc, rfl, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
        have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
            (translateTy targetDecl.ty body.layouts).layout.align.abi .Uninit
            annealZeroedStorage = .ok allocation := hsz ▸ htry
        obtain ⟨alloc'', hw'', -⟩ := freshStackAlloc_writeScalar_readScalar hrel htry'
        exact ⟨alloc'', Or.inr ⟨_, rfl, hw''⟩⟩
    have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
      hlt_tb hlay_tb hval_tb hsized htry hres hfill
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tf.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace freshId)
          { stack := ⟨#[{ tfb with
              locals := tfb.locals.set targetIdx
                { tfb.locals[targetIdx]'hlt_tb with
                  value := .live (.indirect (stackAllocPlace freshId)) }
                hlt_tb }]⟩
            machine := stackAllocMachine m.machine mem' freshId alloc' } := by
      unfold annealForceAllocation; erw [hforce₀]
    have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
      (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce (stackAllocPlace_toRef freshId)
    let tfc : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect (stackAllocPlace freshId)) }
          hlt_tb }
    let machc := stackAllocMachine m.machine mem' freshId alloc'
    have hdc_eq : tfc.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfc, tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
        Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
    have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
    cases hloc_d with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
    | dead _ _ =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
          rfl hget_dc]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
      cases hstep
    | immediate _ _ _ _ _ =>
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
            .concrete freshId Miri.Memory.BorTag.one⟩))
        (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          ({ (⟨⟨#[tfc]⟩, machc⟩ : AnnealStepState) with
              stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                          .concrete freshId Miri.Memory.BorTag.one⟩))) }
                  hlt_dc }]⟩ },
            .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr.location_eq] at hstep
      injection hstep with hm' _
      subst hm'
      obtain ⟨hsup', hnext', _⟩ := hsupply.of_stackAllocMachine
        (by rw [hm_empty]; decide) (by rw [hm_empty]; intro h; cases h) hres alloc'
      exact ⟨hsup', by rw [hnext', hm_empty]; rfl⟩

/-- A direct constant write to the promoted local of allocation `1` keeps
`lean-miri`'s allocation supply ready with next id `2`. -/
private theorem step_direct_write_promoted_const_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.constant c)), span⟩)
    {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : c.ty.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame (.constant c) c.ty)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = dstIdx)
    (ha1 : e₀.allocId = Witness.lm31AllocId1)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
  cases he₀_loc
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy c.ty := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨e₀.localIdx, .nil⟩ (.constant c) span m
  have htr_dst : translatePlace ⟨e₀.localIdx, .nil⟩ = ⟨e₀.localIdx, #[]⟩ := rfl
  obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[e₀.localIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa := hop_tf.of_cacheFrameLocalLayout e₀.localIdx hlt_d
    (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, _, hm_op_ub⟩ |
    ⟨sc, msc, tf', _, hm_op_ok, hstate_tf', himm_sc, _, htf'_preserve⟩
  · have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
      have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
          Miri.Interpreter.RvalueM AnnealStepState Unit) st,
          ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
            annealReadImmediate opv >>= f) st) =
          (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
        intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
          body.localDecls body.layouts (translateOperand (.constant c))
          (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
      rw [hassoc, EStateM.bind_eq_error hm_op_ub]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · obtain ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩ := id hstate_tf'
    injection hframes_tf' with h₁; injection h₁ with htf'; subst htf'
    obtain ⟨_, mls_dc, _, _, _, hmls_dc, _, _⟩ := hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[e₀.localIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve e₀.localIdx; rw [hd_tfa, hmls_dc] at hp; injection hp
    by_cases hsd_dead : slot_d = .dead
    · subst hsd_dead
      have hmd_dead : mls_d.value = .dead := by
        cases hloc_d with
        | lm3_1 h1 =>
          cases h1 with
          | base hb =>
            cases hb with
            | dead _ _ => rfl
            | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
            | indirect _ _ _ _ hne _ => exact absurd rfl hne
      have hdc_dead : tf'.locals[e₀.localIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
        rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val, hmd_dead]
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hdc_dead
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
            Miri.Interpreter.RvalueM AnnealStepState Unit) st,
            ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
              annealReadImmediate opv >>= f) st) =
            (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
          intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
            body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
        rw [hassoc, EStateM.bind_eq_ok hm_op_ok,
          annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
            rfl hget_dc]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hstep
      cases hstep
    · obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_tf'.local_alloc_sync tf' rfl e₀ he₀).1 slot_d hslot_d hsd_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_tf'.base_addr_valid e₀ he₀
      obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
        (himm_sc.of_ty_kind_eq hval_prim hval_kind).of_primitive_scalar hdst_prim
      injection hsc_eq with hsc'; subst hsc'
      have hmsc' : msc = msc' := by
        injection hmsc_eq with h1; unfold Miri.Memory.Scalar.fromScalarInt at h1
        injection h1 with h2; injection h2
      subst hmsc'
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
          localAlloc.allocation := hsz_sc ▸ hshape_la
      obtain ⟨alloc', hw_alloc, -⟩ := hshape_sc.writeScalar_readScalar hrel_sc
      have hmsc_sz : msc.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel_sc.size_eq, ← hsz_sc]
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc) = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel_sc hbool_val hchar_val
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc))
        (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dc
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf']⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
          ({ stack := ⟨#[tf']⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
            Miri.Interpreter.RvalueM AnnealStepState Unit) st,
            ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
              annealReadImmediate opv >>= f) st) =
            (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
          intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
            body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
        rw [hassoc, EStateM.bind_eq_ok hm_op_ok, hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr_tf'.location_eq] at hstep
      injection hstep with hm' _
      subst hm'
      refine ⟨hsupply.of_setLive ?_ _, hnext2⟩
      rw [ha1, hnext2]; decide

/-- With next allocation id `2`, every local other than the owner of allocation
`1` is immediate in `lean-miri`'s root frame. -/
private theorem isImmediateFrameLocal_of_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    {e : AllocMapEntry} (he : e ∈ allocMap) (ha1 : e.allocId = Witness.lm31AllocId1)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (k : Nat) ( hk_ne : k ≠ e.localIdx) :
    IsImmediateFrameLocal tf k := by
  intro mls hmls mp hmp
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, halloc, hdisj⟩ := id hstate
  rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
  have hmls_ind : tf.locals[k]? = some ⟨.live (.indirect mp), mls.layout⟩ := by
    rw [hmls]; rcases mls with ⟨v0, l0⟩; dsimp only at hmp; subst hmp; rfl
  obtain ⟨a, la, hprov_a, hl_a⟩ := hfr.indirect_allocId hmls_ind
  have ha_lt2 : a.value.toNat < 2 := by
    have hlt := hsupply.live (a, la) (Array.mem_toList_iff.mp hl_a)
    rw [hnext2] at hlt
    exact hlt
  have ha_eq : a = Witness.lm31AllocId1 := by
    have hpos : 0 < a.value.toNat := Nat.pos_of_ne_zero fun h => a.nonzero (UInt64.toNat_inj.mp h)
    have hnat1 : a.value.toNat = 1 := by omega
    have h1 : a.value = 1 := UInt64.toNat_inj.mp hnat1
    rcases a with ⟨v, nz⟩
    subst h1; rfl
  subst ha_eq
  have hnot_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
    intro hdead
    have hfind_none := (halloc.local_alloc_sync tf hframes e he).2 hdead
    rw [ha1] at hfind_none
    have hfalse := Array.find?_eq_none.mp hfind_none (Witness.lm31AllocId1, la)
      (Array.mem_toList_iff.mp hl_a)
    simp at hfalse
  obtain ⟨tgtDecl, hdecl_e, _⟩ := halloc.target_decl e he
  obtain ⟨slot_e, _, _, _, hslot_e, _, _, _⟩ := hfr.lookup_local hdecl_e
  have hs_ne : slot_e ≠ .dead := fun hd => hnot_dead (hslot_e.trans (congrArg some hd))
  obtain ⟨⟨lay_e, hlay_e⟩, _, _⟩ :=
    (halloc.local_alloc_sync tf hframes e he).1 slot_e hslot_e hs_ne
  rw [ha1] at hlay_e
  have hprov_e : (stackAllocPlace Witness.lm31AllocId1).ptr.provenance.bind
      Miri.Memory.Provenance.getAllocId = some Witness.lm31AllocId1 := rfl
  exact hdisj k e.localIdx mp (stackAllocPlace Witness.lm31AllocId1) mls.layout lay_e hk_ne
    hmls_ind hlay_e (hprov_a.trans hprov_e.symm)

/-- Body of the safe-reference return witness `w4_safe_ref_return`
(`_0 : &u64`, `_1 : u64`):
```text
bb0: StorageLive(_1); _1 = const 42_u64; _0 = &_1; return
```
-/
def safeRefReturnBody : CapturedMir where
  defPath := "lm_4_3_witness::safe_ref_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.refU64Decl, Witness.u64Decl]
  basicBlocks := [
    { statements := [
        Witness.mkStmt (.storageLive 1),
        Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 42)))),
        Witness.mkStmt (.assign (Witness.local_ 0) (.ref .shared (Witness.local_ 1)))]
      terminator := Witness.mkTerm .return_
      isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state after the allocation-free prefix `StorageLive(_1);
_1 = const 42_u64` of `safeRefReturnBody`. -/
def safeRefPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .init (.scalar ⟨42, 8⟩)] }
    memory := (initMachineState safeRefReturnBody []).memory }

/-- `lean-miri`'s root frame after the same prefix. -/
def safeRefPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody safeRefReturnBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy Witness.refU64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy Witness.u64Ty) }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 2⟩ }

/-- `lean-miri`'s state after the same prefix. -/
def safeRefPreMiri : AnnealStepState :=
  { stack := ⟨#[safeRefPreMiriFrame]⟩, machine := AnnealMachine.empty }

theorem safeRef_prefix_anneal :
    runAnnealBounded safeRefReturnBody 2 (initMachineState safeRefReturnBody []) =
      .running safeRefPreAnneal := rfl

theorem safeRef_prefix_miri :
    runLoopFuel (annealMiriHooks safeRefReturnBody) 2 (miriEntryState safeRefReturnBody) =
      .running safeRefPreMiri := rfl

theorem safeRef_pre_stateRel_and_imm :
    StateRel safeRefReturnBody safeRefPreAnneal safeRefPreMiri ∧
    (∀ tf, safeRefPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k) := by
  have himm : ∀ tf, safeRefPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 => simp [safeRefPreMiriFrame] at hmls; subst hmls; cases hmp
    | _ + 2 => simp [safeRefPreMiriFrame] at hmls
  refine ⟨StateRel.mk safeRefPreMiriFrame rfl rfl ⟨translateTy Witness.refU64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl (MemoryAllocDisjoint.of_no_indirect _ (himm _ rfl)), himm⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [safeRefPreAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [safeRefPreMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = Witness.u64Decl := by simpa [safeRefReturnBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [safeRefPreAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
                      layout := some (translateTy Witness.u64Ty) } := by
      simpa [safeRefPreMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy Witness.u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl (fun h => nomatch h)
        (fun h => nomatch h)⟩)
  | _ + 2 => simp [safeRefReturnBody, get?] at hdecl

/-- A safe reference `&u64` returned from the root frame (`safeRefReturnBody`:
`StorageLive(_1); _1 = const 42_u64; _0 = &_1; return`). From
`initMachineState safeRefReturnBody []` / `miriEntryState safeRefReturnBody`
both machines return the reference to `_1`: Anneal returns
`.ptr { allocId := 1, offsetBytes := 0 } 8`, and `lean-miri` returns an
immediate that is `ImmediateRelLM3_2`-related to it through the shared borrow
entry of `_1`. The reference step is `evalRvalue_ref_simulation` and the root
return is `step_terminator_goto_return_lm3_2_simulation`. -/
theorem w4_safe_ref_return :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns safeRefReturnBody (annealMiriHooks safeRefReturnBody)
        (initMachineState safeRefReturnBody []) (miriEntryState safeRefReturnBody)
        (.ptr { allocId := 1, offsetBytes := 0 } 8) (.immediate imm0) ∧
      get? safeRefReturnBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_2
        [refAllocMapEntry safeRefReturnBody.localDecls safeRefReturnBody.layouts .shared 1 1
          Witness.lm31AllocId1]
        decl0.ty safeRefReturnBody.layouts (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0 := by
  let b := safeRefReturnBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hrel₀, himm₀⟩ := safeRef_pre_stateRel_and_imm
  let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 Witness.lm31AllocId1
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3,
                 locals := [.init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                            .init (.scalar ⟨42, 8⟩)] }
      memory := { (initMachineState b []).memory with
        borrows := [entry.toBorrowEntry], nextTag := 2 } }
  have hs₁ : stepMirFn b safeRefPreAnneal = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 0) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 0, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_step_of_anneal_step hsim₁ hs₁
  change StateRelLM3_2 b s₁ m₁ [entry] at hrel₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_nextAllocId_two hrel₀ (dstIdx := 0) (targetIdx := 1)
    (bk := .shared) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 0, himm₀ tf htf 1⟩) rfl hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => isImmediateFrameLocal_of_nextAllocId_two hrel₁ hsup₁ hnext₁
      (List.Mem.head _) rfl htf 0 (by decide)
  have hret : stepMirFn b s₁ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₁.memory :=
    rfl
  have hsim₂ := step_terminator_goto_return_lm3_2_simulation hrel₁ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, Witness.refU64Decl, rfl, by decide, himm₁⟩))
  rw [hret] at hsim₂
  generalize hm₂_eq : Miri.Interpreter.Step.step
    (annealStepHooks b.localDecls b.layouts) () m₁ = mRes₂ at hsim₂
  cases hsim₂ with
  | retRoot decl0 _ imm0 _ m₂ hdecl0 hop0 himm0 hm₂ =>
    refine ⟨decl0, imm0, ?_, hdecl0, himm0⟩
    exact agreeReturns_of_paths safeRef_prefix_anneal safeRef_prefix_miri
      (.step .silent hs₁ (.refl _)) hret
      (.step hm₁ (frames_ne_of_step_ok_true hm₂_eq) (.refl _))
      hm₂_eq (by rw [hm₂]) (by change (annealControlHooks.returnOperand () m₁).2 = _; rw [hop0])

/-- Entry-to-return MIR body for Stage-1 invalid `bool` read through `&bool`:
`StorageLive(_1); StorageLive(_2); _1 = const 2_u8; _2 = &_1; _0 = copy (*_2); return`. -/
def invalidBoolRefEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::invalid_bool_ref_read_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.boolDeclLM32, Witness.u8DeclLM32, Witness.refBoolDeclLM32]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1),
      Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.assign (Witness.local_ 1) (.use (cU8 2))),
      Witness.mkStmt (.assign (Witness.local_ 2) (.ref .shared (Witness.local_ 1))),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 2))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private def invalidBoolRefPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3, locals := [.uninit, .init (.scalar ⟨2, 1⟩), .uninit] }
    memory := (initMachineState invalidBoolRefEntryBody []).memory }

private def invalidBoolRefPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame invalidBoolRefEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      Witness.lm32MlsU8Two,
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 3⟩ }

private def invalidBoolRefPreMiri : AnnealStepState :=
  { stack := ⟨#[invalidBoolRefPreMiriFrame]⟩, machine := AnnealMachine.empty }

private theorem invalidBoolRef_prefix_anneal :
    runAnnealBounded invalidBoolRefEntryBody 3 (initMachineState invalidBoolRefEntryBody []) =
      .running invalidBoolRefPreAnneal := rfl

private theorem invalidBoolRef_prefix_miri :
    runLoopFuel (annealMiriHooks invalidBoolRefEntryBody) 3
      (miriEntryState invalidBoolRefEntryBody) =
      .running invalidBoolRefPreMiri := rfl

/-- **Stage-1 lockstep from entry** (`invalidBoolRefEntryBody`): from
`initMachineState` / `miriEntryState`, both machines execute
`StorageLive(_1); StorageLive(_2); _1 = const 2_u8; _2 = &_1` in lockstep and
reject `_0 = copy (*_2)` at type `bool` with undefined behavior
(`step_safeRef_deref_read_invalid_scalar_simulation`). -/
theorem w4_invalid_bool_ref_read_ub :
    AgreeUB invalidBoolRefEntryBody (annealMiriHooks invalidBoolRefEntryBody)
      (initMachineState invalidBoolRefEntryBody [])
      (miriEntryState invalidBoolRefEntryBody) := by
  let b := invalidBoolRefEntryBody
  have hpa := invalidBoolRef_prefix_anneal
  have hpm := invalidBoolRef_prefix_miri
  have hrel2 : ScalarRel ⟨2, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 2) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hrel₀ : StateRel b invalidBoolRefPreAnneal invalidBoolRefPreMiri := by
    refine StateRel.mk invalidBoolRefPreMiriFrame rfl rfl
      ⟨translateTy Witness.boolTyLM32 emptyLayoutTable, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with
        | 0 | 1 | 2 | _ + 3 =>
          simp [invalidBoolRefPreMiriFrame, Witness.lm32MlsU8Two] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 =>
      have hs : slot = .uninit := by simpa [invalidBoolRefPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [invalidBoolRefPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = Witness.u8DeclLM32 := by
        simpa [b, invalidBoolRefEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨2, 1⟩) := by
        simpa [invalidBoolRefPreAnneal, get?] using hslot.symm
      have hm : mls = Witness.lm32MlsU8Two := by
        simpa [invalidBoolRefPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy Witness.u8TyLM32 emptyLayoutTable))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel2 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 3 => simp [b, invalidBoolRefEntryBody, get?] at hdecl
  have himm₀ : ∀ tf, invalidBoolRefPreMiri.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hv
    have htf : invalidBoolRefPreMiriFrame = tf := by simpa [invalidBoolRefPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 => simp [invalidBoolRefPreMiriFrame, Witness.lm32MlsU8Two] at hmls; subst hmls; cases hv
    | _ + 3 => simp [invalidBoolRefPreMiriFrame] at hmls
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu8 : IsPrimScalarTy Witness.u8TyLM32 := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hinvalid : ¬ AnnealScalarValid Witness.boolTyLM32 ⟨2, 1⟩ := fun ⟨hb, _⟩ => by
    rcases hb rfl with h | h <;> exact absurd h (by decide)
  let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 Witness.lm31AllocId1
  let p0 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4,
                 locals := [.uninit, .init (.scalar ⟨2, 1⟩), .init (.ptr p0 8)] }
      memory := { (initMachineState b []).memory with
        borrows := [entry.toBorrowEntry], nextTag := 2 } }
  have hs₁ : stepMirFn b invalidBoolRefPreAnneal = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl hu8 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_step_of_anneal_step hsim₁ hs₁
  change StateRelLM3_2 b s₁ m₁ [entry] at hrel₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_nextAllocId_two hrel₀ (dstIdx := 2) (targetIdx := 1)
    (bk := .shared) rfl rfl rfl rfl hu8 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
  have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
    fun tf htf => isImmediateFrameLocal_of_nextAllocId_two hrel₁ hsup₁ hnext₁
      (List.Mem.head _) rfl htf 2 (by decide)
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  obtain ⟨_, hs₂, m₂, hm₂⟩ := step_safeRef_deref_read_invalid_scalar_simulation hrel₁
    hphase (Or.inl rfl) rfl rfl (dstDecl := Witness.boolDeclLM32)
    (refDecl := Witness.refBoolDeclLM32) (allocDecl := Witness.u8DeclLM32)
    rfl rfl rfl (Or.inl rfl) himm₁_2 (ptrVal := p0) (e := entry) (sc := ⟨2, 1⟩)
    rfl (List.Mem.head _) rfl rfl (fun h => nomatch h) rfl rfl rfl hinvalid (fun h => nomatch h)
  exact agreeUB_of_paths hpa hpm
    (.step .silent hs₁ (.refl _)) hs₂
    (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _))
    hm₂ rfl

/-- Body of the Tree Borrows boundary witness `w4_disabled_read_divergence`
(`_0 _1 : u64`, `_2 : &mut u64`):
```text
bb0: StorageLive(_1); StorageLive(_2);
     _1 = const 42_u64;
     _2 = &mut _1;
     _1 = const 77_u64;
     _0 = copy *_2;
     return
```
-/
def disabledReadEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::disabled_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u64Decl, Witness.u64Decl, Witness.refMutU64Decl]
  basicBlocks := [
    { statements := [
        Witness.mkStmt (.storageLive 1),
        Witness.mkStmt (.storageLive 2),
        Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 42)))),
        Witness.mkStmt (.assign (Witness.local_ 2) (.ref (.mut false) (Witness.local_ 1))),
        Witness.mkStmt (.assign (Witness.local_ 1) (.use (.constant (Witness.constU64 77)))),
        Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 2))))]
      terminator := Witness.mkTerm .return_
      isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state after the allocation-free prefix `StorageLive(_1);
StorageLive(_2); _1 = const 42_u64` of `disabledReadEntryBody`. -/
def disabledReadPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3, locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
    memory := (initMachineState disabledReadEntryBody []).memory }

/-- `lean-miri`'s root frame after the same prefix. -/
def disabledReadPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody disabledReadEntryBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy Witness.u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy Witness.u64Ty) },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 3⟩ }

/-- `lean-miri`'s state after the same prefix. -/
def disabledReadPreMiri : AnnealStepState :=
  { stack := ⟨#[disabledReadPreMiriFrame]⟩, machine := AnnealMachine.empty }

theorem disabledRead_prefix_anneal :
    runAnnealBounded disabledReadEntryBody 3 (initMachineState disabledReadEntryBody []) =
      .running disabledReadPreAnneal := rfl

theorem disabledRead_prefix_miri :
    runLoopFuel (annealMiriHooks disabledReadEntryBody) 3 (miriEntryState disabledReadEntryBody) =
      .running disabledReadPreMiri := rfl

theorem disabledRead_pre_stateRel_and_imm :
    StateRel disabledReadEntryBody disabledReadPreAnneal disabledReadPreMiri ∧
    (∀ tf, disabledReadPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k) := by
  have himm : ∀ tf, disabledReadPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 | 2 => simp [disabledReadPreMiriFrame] at hmls; subst hmls; cases hmp
    | _ + 3 => simp [disabledReadPreMiriFrame] at hmls
  refine ⟨StateRel.mk disabledReadPreMiriFrame rfl rfl ⟨translateTy Witness.u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl (MemoryAllocDisjoint.of_no_indirect _ (himm _ rfl)), himm⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 =>
    have hs : slot = .uninit := by simpa [disabledReadPreAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [disabledReadPreMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = Witness.u64Decl := by simpa [disabledReadEntryBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [disabledReadPreAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
                      layout := some (translateTy Witness.u64Ty) } := by
      simpa [disabledReadPreMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy Witness.u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 3 => simp [disabledReadEntryBody, get?] at hdecl

/-- **Tree Borrows boundary witness** (`LM-3.2`,
`step_safeRef_deref_read_disabled_divergence`): in `disabledReadEntryBody` the
direct write `_1 = const 77_u64` disables the reborrow `_2`. From
`initMachineState disabledReadEntryBody []`, Anneal's read `copy *_2` is
undefined behavior, so Anneal's whole program is not `TreeSafe`. From
`miriEntryState disabledReadEntryBody`, `lean-miri`'s memory accesses run no
borrow-tracker hooks (`annealMemoryCopyHooks_access_ok`): the read succeeds and
the whole program returns `77_u64`, so `miriSystem` is `System.Safe` and
partially correct for that value. Hence `TreeSafe ↔ System.Safe` fails on this
body, which lies outside every agreed fragment. For `lean-miri`'s read and
return steps the proof relates its state to an Anneal state whose borrow table
holds the reborrow before it was disabled
(`StateRelLM3_2.replace_borrows_skeleton`); this changes only the Anneal side
of the relation, not the `lean-miri` state. -/
theorem w4_disabled_read_divergence :
    MirReachesUB (mirCallTree disabledReadEntryBody []) ∧
    ¬ TreeSafe (mirCallTree disabledReadEntryBody []) ∧
    (miriSystem (annealMiriHooks disabledReadEntryBody)).Safe
      (miriEntryState disabledReadEntryBody) ∧
    (∃ msc, ScalarRel ⟨77, 8⟩ msc ∧
      (miriSystem (annealMiriHooks disabledReadEntryBody)).ReachesOutcome
        (miriEntryState disabledReadEntryBody)
        (.returned (.immediate (.scalar (.fromScalarInt msc)))) ∧
      (miriSystem (annealMiriHooks disabledReadEntryBody)).PartialCorrect
        (miriEntryState disabledReadEntryBody)
        (· = .immediate (.scalar (.fromScalarInt msc)))) ∧
    ¬ (TreeSafe (mirCallTree disabledReadEntryBody []) ↔
      (miriSystem (annealMiriHooks disabledReadEntryBody)).Safe
        (miriEntryState disabledReadEntryBody)) := by
  let b := disabledReadEntryBody
  have ha := anneal_ub_of_obs (body := b) (N := 7) (s := initMachineState b []) (by decide)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hrel₀, himm₀⟩ := disabledRead_pre_stateRel_and_imm
  let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 Witness.lm31AllocId1
  let entryDis : AllocMapEntry := { entry with perm := .disabled }
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4,
                 locals := [.uninit, .init (.scalar ⟨42, 8⟩),
                            .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
      memory := { (initMachineState b []).memory with borrows := [entry.toBorrowEntry], nextTag := 2 } }
  have hs₁ : stepMirFn b disabledReadPreAnneal = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_step_of_anneal_step hsim₁ hs₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_nextAllocId_two hrel₀ (dstIdx := 2) (targetIdx := 1)
    (bk := .mut false) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
  let s₂ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 5,
                 locals := [.uninit, .init (.scalar ⟨77, 8⟩),
                            .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
      memory := { (initMachineState b []).memory with borrows := [entryDis.toBorrowEntry], nextTag := 2 } }
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hc77 : ∀ tf, WellTypedScalarOperand b tf (.constant (Witness.constU64 77)) Witness.u64Ty :=
    fun tf => .constScalar (Witness.constU64 77) ⟨77, 8⟩ rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
      (fun h => nomatch h) (fun h => nomatch h)
  have hsim₂ := step_direct_write_promoted_lm3_2_simulation hrel₁ hphase rfl rfl
    (dstDecl := Witness.u64Decl) (valTy := Witness.u64Ty) rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl (fun tf _ => hc77 tf) ⟨entry, List.Mem.head _, rfl⟩
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_step_of_anneal_step hsim₂ hs₂
  change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
  obtain ⟨hsup₂, hnext₂⟩ := step_direct_write_promoted_const_nextAllocId_two hrel₁ rfl rfl
    (dstDecl := Witness.u64Decl) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => hc77 tf) (List.Mem.head _) rfl rfl hsup₁ hnext₁ hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 2 :=
    fun tf htf =>
      ⟨isImmediateFrameLocal_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 0 (by decide),
       isImmediateFrameLocal_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 2 (by decide)⟩
  obtain ⟨_, m₃, tf₃, msc, hsc, hm₃, htf₃, hv₃⟩ :=
    step_safeRef_deref_read_disabled_divergence hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := Witness.u64Decl) (refDecl := Witness.refMutU64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entryDis) (sc := ⟨77, 8⟩)
      rfl (List.Mem.head _) rfl rfl rfl rfl
      (fun d hd => by injection hd with hd'; subst hd'; rfl) (fun h => nomatch h)
  -- Ghost-borrow swap on `(s₂, m₂)` (`entryDis ↦ entry`): `m₂` is unchanged!
  let s₂_act : MachineState :=
    { s₂ with memory := { s₂.memory with borrows := [entry.toBorrowEntry] } }
  have hrel₂_act : StateRelLM3_2 b s₂_act m₂ [entry] :=
    hrel₂.replace_borrows_skeleton (am₂ := [entry]) (.cons ⟨rfl, rfl, rfl⟩ .nil)
  let s₃_act : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 6,
                 locals := [.init (.scalar ⟨77, 8⟩), .init (.scalar ⟨77, 8⟩),
                            .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
      memory := { (initMachineState b []).memory with borrows := [entry.toBorrowEntry], nextTag := 2 } }
  have hs₃_act : stepMirFn b s₂_act = .step s₃_act := rfl
  have hsim₃ := step_safeRef_deref_read_simulation_explicit hrel₂_act hphase (Or.inl rfl)
    rfl rfl (dstDecl := Witness.u64Decl) (refDecl := Witness.refMutU64Decl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂
    (fun ptrVal hp e he _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        dsimp only [s₂_act, s₂, get?] at hp
        injection hp with h1; injection h1 with h2; injection h2 with h3 _; exact h3.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        subst hp'
        refine ⟨rfl, (fun h => nomatch h), fun d hd => ?_⟩
        dsimp only [entry, refAllocMapEntry, b, disabledReadEntryBody, get?] at hd
        injection hd with hd'; subst hd'; rfl)
  obtain ⟨m₃', hm₃', hrel₃⟩ := stepRelLM3_2_step_of_anneal_step hsim₃ hs₃_act
  have hm₃_eq : m₃ = m₃' := by rw [hm₃] at hm₃'; injection hm₃'
  cases hm₃_eq
  have himm₃_0 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf htf mls hmls mp hmp
    rw [htf₃] at htf; injection htf with h1; injection h1 with h2; subst h2
    rw [hmls] at hv₃; simp [hmp] at hv₃
  have hret_act : stepMirFn b s₃_act = .retNormal (.scalar ⟨77, 8⟩) s₃_act.memory := rfl
  have hsim₄ := step_terminator_goto_return_lm3_2_simulation hrel₃ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, Witness.u64Decl, rfl, by decide, himm₃_0⟩))
  rw [hret_act] at hsim₄
  generalize hm₄_eq :
    Miri.Interpreter.Step.step
      (annealStepHooks disabledReadEntryBody.localDecls disabledReadEntryBody.layouts) () m₃ = mRes₄
    at hsim₄
  cases hsim₄ with
  | retRoot _ _ imm0 _ m₄ _ hop0 _ hm₄_empty =>
    have hop_msc : imm0 = .scalar (.fromScalarInt msc) := by
      rcases htf_opt : tf₃.locals[0]? with _ | ⟨val0, lay0⟩
      · simp [htf_opt] at hv₃
      · simp [htf_opt] at hv₃
        subst hv₃
        have hget_fn := frame_getLocal_of_getElem? tf₃ 0 _ htf_opt
        have hop_sc := annealControlHooks_returnOperand_scalar htf₃ hget_fn
        rw [hop_sc] at hop0
        injection hop0 with _ h1; injection h1 with h2; injection h2 with h3; exact h3.symm
    subst hop_msc
    have hpathM : MiriPath (annealMiriHooks b) (miriEntryState b) m₃ :=
      (MiriPath.of_runLoopFuel disabledRead_prefix_miri).trans
        (.step hm₁ (frames_ne_of_step_ok_true hm₂)
          (.step hm₂ (frames_ne_of_step_ok_true hm₃)
            (.step hm₃ (frames_ne_of_eq_singleton htf₃) (.refl _))))
    have hemp₄ : m₄.stack.frames = #[] := by rw [hm₄_empty]
    obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_path_return hpathM hm₄_eq hemp₄
      (by change (annealControlHooks.returnOperand () m₃).2 = _; rw [hop0])
    exact ⟨ha.1, ha.2, hsafe, ⟨msc, hsc, hreach, fun v' hv' => by have := huniq _ hv'; injection this⟩,
      fun hiff => ha.2 (hiff.mpr hsafe)⟩


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
`bb0: StorageLive(_1); _1 = U { a: 5_u8 }; _0 = copy (_1.0: u8); return`
(`_0 : u8`, `_1 : union U { a: u8, b: u32 }`). -/
def unionRetBody : CapturedMir where
  defPath := "lm_4_3_witness::union_init_prefix_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.lm24Decl Witness.lm24U8Ty, Witness.lm24Decl Witness.lm24UTy]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 1, span := "lm-4.3-witness" },
        Witness.lm24AggStmt 1 5,
        { kind := .assign ⟨0, .nil⟩ (.use (unionFieldReadOperand false 1 0 Witness.lm24U8Ty))
          span := "lm-4.3-witness" }]
      terminator := { kind := .return_, span := "lm-4.3-witness" }
      isCleanup := false }]
  fnAbi := { args := [], ret := { layout := Witness.lm24U8Layout, mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := Witness.lm24Layouts
  allocations := []

/-- Anneal's state after the `StorageLive(_1)` step of `unionRetBody` from
`initMachineState unionRetBody []` (`unionRet_prefix_anneal`). -/
def unionRetPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .uninit] }
    memory := (initMachineState unionRetBody []).memory }

/-- `lean-miri`'s root frame after the `StorageLive(_1)` step of `unionRetBody`. -/
def unionRetPreMiriFrame :
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
    location := .mir ⟨0, 1⟩ }

/-- `lean-miri`'s state after the `StorageLive(_1)` step of `unionRetBody` from
`miriEntryState unionRetBody` (`unionRet_prefix_miri`). -/
def unionRetPreMiri : AnnealStepState :=
  { stack := ⟨#[unionRetPreMiriFrame]⟩, machine := AnnealMachine.empty }

theorem unionRet_prefix_anneal :
    runAnnealBounded unionRetBody 1 (initMachineState unionRetBody []) =
      .running unionRetPreAnneal := rfl

theorem unionRet_prefix_miri :
    runLoopFuel
      (.ofHooks (annealStepHooksLM2_4 unionRetBody.localDecls unionRetBody.layouts)
        annealControlHooks) 1 (miriEntryState unionRetBody) =
      .running unionRetPreMiri := rfl

theorem unionRet_pre_stateRel : StateRel unionRetBody unionRetPreAnneal unionRetPreMiri := by
  refine StateRel.mk unionRetPreMiriFrame rfl rfl
    ⟨translateTy Witness.lm24U8Ty Witness.lm24Layouts, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      match i with | 0 | 1 | _ + 2 => simp [unionRetPreMiriFrame] at hi)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 =>
    have hs : slot = .uninit := by simpa [unionRetPreAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [unionRetPreMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 2 => simp [unionRetBody, get?] at hdecl

theorem unionRet_pre_imm (j : Nat) :
    ∀ tf, unionRetPreMiri.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
  intro tf h mls hmls mp hv
  have htf : unionRetPreMiriFrame = tf := by simpa [unionRetPreMiri] using h
  subst htf
  match j with
  | 0 | 1 => simp [unionRetPreMiriFrame] at hmls; subst hmls; cases hv
  | _ + 2 => simp [unionRetPreMiriFrame] at hmls

/-- **Whole-program `AgreeReturns` safe union witness**: `unionRetBody`
(`StorageLive(_1); _1 = U { a: 5_u8 }; _0 = copy (_1.0: u8); return`) runs from
the entry states `initMachineState unionRetBody []` / `miriEntryState unionRetBody`
through `annealStepHooksLM2_4` to an agreeing root return of `5_u8`
(`ImmediateRel`). The trace goes through `step_union_aggregate_simulation` and
`step_union_field_read_simulation`: `_1` is read while only its `u8` prefix is
initialized. -/
theorem w2_union_init_prefix_returns :
    ∃ imm0,
      AgreeReturns unionRetBody
        (.ofHooks (annealStepHooksLM2_4 unionRetBody.localDecls unionRetBody.layouts)
          annealControlHooks)
        (initMachineState unionRetBody []) (miriEntryState unionRetBody)
        (.scalar ⟨5, 1⟩) (.immediate imm0) ∧
      ImmediateRel Witness.lm24U8Ty Witness.lm24Layouts (.scalar ⟨5, 1⟩) imm0 := by
  let b := unionRetBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hc5 : ∀ tf, WellTypedScalarOperand b tf (.constant (Witness.lm24ConstU8 5)) Witness.lm24U8Ty :=
    fun tf => .constScalar (Witness.lm24ConstU8 5) ⟨5, 1⟩ rfl Witness.lm24_isPrim_u8 (Or.inl rfl)
      (by decide) rfl (fun h => nomatch h) (fun h => nomatch h)
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2,
                 locals := [.uninit, .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])] }
      memory := (initMachineState b []).memory }
  let s₂ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3,
                 locals := [.init (.scalar ⟨5, 1⟩), .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])] }
      memory := (initMachineState b []).memory }
  have hs₁ : stepMirFn b unionRetPreAnneal = .step s₁ := rfl
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hs₃ : stepMirFn b s₂ = .retNormal (.scalar ⟨5, 1⟩) s₂.memory := rfl
  have hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls b.layouts "U" b.localDecls,
      b.layouts.entries[(Witness.lm24Decl Witness.lm24UTy).ty.layoutIdx]? = some l := by
    have hs : stringEq "U" "U" = true := by decide
    simp [b, collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, hs, LayoutTable.lookup,
      unionRetBody, Witness.lm24Layouts, Witness.lm24Decl, Witness.lm24UTy, Witness.lm24U8Ty,
      get?, eq_comm]
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation unionRet_pre_stateRel.toLM2_4
    List.Pairwise.nil MemoryHighWater.empty.canReserveAllocId hphase
    (u := 1) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl (by decide) rfl rfl rfl
    (unionRet_pre_imm 1) Witness.lm24_isPrim_u8 (fun tf _ => hc5 tf) (by decide)
    (hdecls_adt := hdecls_adt)
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
    subst h; exact himm₁ _ rfl 0 (by decide) (unionRet_pre_imm 0 _ rfl)
  obtain ⟨hrel₂, _, hmach₂⟩ := (step_union_field_read_simulation hstate₁ hnodup₁ hphase
    (r := 0) (u := 1) (j := 0) (fty := Witness.lm24U8Ty) (isMove := false)
    rfl rfl rfl rfl rfl Witness.lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl (f := 0) Witness.lm24_wt_U
    rfl (by decide) (by decide)
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
      have hsl₁ : sl₁ = .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]) := Option.some.inj hs₁.symm
      rw [hmls₀] at hm₀; injection hm₀ with hm₀; subst hm₀
      rcases mls₀ with ⟨v₀, lay₀⟩; dsimp only at hmp₀; subst hmp₀
      have hc_pre : unionRetPreMiri.machine.memory.nextAllocId.toNat = 1 := rfl
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
        | union _ _ _ _ _ _ _ _ _ _ _ hm =>
          rcases hm with ⟨id₀, _, _, la₀, _, hp₀, _, _, hlive₀, _⟩
          exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
        | unionOverlay _ _ _ _ _ _ _ _ _ _ _ _ _ hm =>
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
        | union _ _ _ _ _ mp₁ lay₁ _ _ _ _ hm =>
          rcases hm with ⟨id₁, _, _, la₁, _, hp₁, _, _, hlive₁, _⟩
          exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
        | unionOverlay _ _ _ _ _ _ _ mp₁ lay₁ _ _ _ _ hm =>
          rcases hm with ⟨id₁, _, _, la₁, _, hp₁, _, _, hlive₁, _⟩
          exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
        | base _ _ hl₁ =>
          cases hl₁ with
          | dead _ _ => cases hsl₁
          | immediate _ _ _ _ hval =>
            rw [hsl₁] at hval
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
      have hd0 : decl0 = Witness.lm24Decl Witness.lm24U8Ty := Option.some.inj hdecl0.symm
      subst hd0
      refine ⟨imm0, ?_, himm0⟩
      exact agreeReturns_of_paths unionRet_prefix_anneal unionRet_prefix_miri
        (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hs₃
        (.step hm₁ (frames_ne_of_eq_singleton hframes₁)
          (.step hm₂_eq (frames_ne_of_step_ok_true hm₃_eq) (.refl _)))
        hm₃_eq (by rw [hm₃]) (by change (annealControlHooks.returnOperand () m₂).2 = _; rw [hop0])

/-- Union-returning MIR body (`_0 : U`): `bb0: _0 = U { a: 5_u8 }; return`. -/
def unionValReturnBody : CapturedMir where
  defPath := "lm_4_3_witness::union_val_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.lm24Decl Witness.lm24UTy]
  basicBlocks := [{
    statements := [Witness.lm24AggStmt 0 5]
    terminator := { kind := .return_, span := "lm-4.3-witness" }
    isCleanup := false }]
  fnAbi := { args := [], ret := { layout := Witness.lm24ULayout, mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := Witness.lm24Layouts
  allocations := []

/-- **Stage-1 union-valued root return from entry** (`unionValReturnBody`): from
`initMachineState unionValReturnBody []` / `miriEntryState unionValReturnBody`,
`_0 = U { a: 5_u8 }; return` runs in lockstep through
`step_union_aggregate_simulation` and `step_terminator_return_wellTypedUnion_lm2_4_simulation`,
returning `UnionRetRel`-related values (`AgreeReturns`). -/
theorem w2_union_return :
    ∃ mp0,
      AgreeReturns unionValReturnBody
        (.ofHooks (annealStepHooksLM2_4 unionValReturnBody.localDecls unionValReturnBody.layouts)
          annealControlHooks)
        (initMachineState unionValReturnBody [])
        (miriEntryState unionValReturnBody)
        (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])
        (.indirect mp0) ∧
      UnionRetRel unionValReturnBody (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]) (.indirect mp0) := by
  let b := unionValReturnBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hc5 : ∀ tf, WellTypedScalarOperand b tf (.constant (Witness.lm24ConstU8 5)) Witness.lm24U8Ty :=
    fun _ => .constScalar (Witness.lm24ConstU8 5) ⟨5, 1⟩ rfl
      Witness.lm24_isPrim_u8 (Or.inl rfl) (by decide) rfl (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ : ∀ tf, (miriEntryState b).stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf h mls hmls mp hv
    have htf : miriEntryFrame b = tf := by simpa [miriEntryState] using h
    subst htf
    simp [b, unionValReturnBody, miriEntryFrame, miriEntryLocals] at hmls; subst hmls; cases hv
  have hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls b.layouts "U" b.localDecls,
      b.layouts.entries[(Witness.lm24Decl Witness.lm24UTy).ty.layoutIdx]? = some l := by
    have hs : stringEq "U" "U" = true := by decide
    simp [b, collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, hs, LayoutTable.lookup,
      unionValReturnBody, Witness.lm24Layouts, Witness.lm24Decl, Witness.lm24UTy, get?, eq_comm]
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1,
                 locals := [.init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])] }
      memory := (initMachineState b []).memory }
  have hs₁ : stepMirFn b (initMachineState b []) = .step s₁ := rfl
  have hs₂ : stepMirFn b s₁ = .retNormal (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]) s₁.memory := rfl
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (stateRelLM2_4_entry b)
    List.Pairwise.nil MemoryHighWater.empty.canReserveAllocId hphase
    (u := 0) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl (by decide) rfl rfl rfl
    himm₀ Witness.lm24_isPrim_u8 (fun tf _ => hc5 tf) (by decide)
    (hdecls_adt := hdecls_adt)
  obtain ⟨_, _, m₁, _, hm₁, _, hstate₁, _, hframes₁, _, _, _, _, _, _, _, _⟩ := hpost₁ s₁ hs₁
  have hsim₂ := step_terminator_return_wellTypedUnion_lm2_4_simulation hstate₁ hphase
    rfl rfl rfl rfl rfl (decl0 := Witness.lm24Decl Witness.lm24UTy) rfl Witness.lm24_wt_U
    (by rintro ⟨h, _⟩; cases h)
  rw [hs₂] at hsim₂
  generalize hm₂_eq : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 b.localDecls b.layouts) () m₁ = mRes₂ at hsim₂
  cases hsim₂ with
  | retRootImm _ _ imm0 _ _ _ _ himmRel _ =>
    cases himmRel
  | retRootUnion decl0 _ mp0 _ m₂ hdecl0 hop0 huloc0 hm₂ =>
    refine ⟨mp0, ?_, decl0, m₂.machine, mp0, hdecl0, rfl, huloc0⟩
    exact agreeReturns_of_paths (p := 0) rfl rfl
      (.step .silent hs₁ (.refl _)) hs₂
      (.step hm₁ (frames_ne_of_eq_singleton hframes₁) (.refl _))
      hm₂_eq (by rw [hm₂]) (by change (annealControlHooks.returnOperand () m₁).2 = _; rw [hop0])

/-- Entry-to-return MIR body for `pass_union_overlay_word_bytes`:
`StorageLive(_1); _1 = U { b: 0x04030201_u32 }; _1.0 = const 0x09_u8;
_0 = copy (_1.1: u32); return`, returning `0x04030209_u32 = 67305993`. -/
def unionOverlayPunBody : CapturedMir where
  defPath := "lm_4_3_witness::union_overlay_type_punning_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.lm24Decl Witness.lm24U32Ty, Witness.lm24Decl Witness.lm24UTy]
  basicBlocks := [{
    statements := [
      { kind := .storageLive 1, span := "lm-4.3-witness" },
      Witness.lm24AggU32Stmt 1 0x04030201,
      Witness.lm24FieldWriteStmt 1 0x09,
      { kind := .assign ⟨0, .nil⟩ (.use (unionFieldReadOperand false 1 1 Witness.lm24U32Ty))
        span := "lm-4.3-witness" }]
    terminator := { kind := .return_, span := "lm-4.3-witness" }
    isCleanup := false }]
  fnAbi := { args := [], ret := { layout := Witness.lm24U32Layout, mode := .direct },
             conv := .rust, canUnwind := false }
  layouts := Witness.lm24Layouts
  allocations := []

private def unionOverlayPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .uninit] }
    memory := (initMachineState unionOverlayPunBody []).memory }

private def unionOverlayPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame unionOverlayPunBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 1⟩ }

private def unionOverlayPreMiri : AnnealStepState :=
  { stack := ⟨#[unionOverlayPreMiriFrame]⟩, machine := AnnealMachine.empty }

/-- **Stage-1 union overlay & sibling type-punning from entry**
(`pass_union_overlay_word_bytes`, `unionOverlayPunBody`): from
`initMachineState` / `miriEntryState`, `_1 = U { b: 0x04030201_u32 }` initializes
field `1`, `_1.0 = 0x09_u8` splices byte `0` via Stage-1 `UnionLocalRel.unionOverlay`
(`step_union_narrower_field_write_simulation`), `_0 = copy (_1.1: u32)` type-puns
`0x04030209_u32 = 67305993` (`step_union_overlay_field_read_simulation`), and the
root frame returns `67305993_u32` (`AgreeReturns`). -/
theorem w2_union_overlay_type_punning_returns :
    ∃ imm0,
      AgreeReturns unionOverlayPunBody
        (.ofHooks (annealStepHooksLM2_4 unionOverlayPunBody.localDecls unionOverlayPunBody.layouts)
          annealControlHooks)
        (initMachineState unionOverlayPunBody [])
        (miriEntryState unionOverlayPunBody)
        (.scalar ⟨0x04030209, 4⟩)
        (.immediate imm0) ∧
      ImmediateRel Witness.lm24U32Ty Witness.lm24Layouts (.scalar ⟨0x04030209, 4⟩) imm0 := by
  let b := unionOverlayPunBody
  have hpa : runAnnealBounded b 1 (initMachineState b []) = .running unionOverlayPreAnneal := rfl
  have hpm : runLoopFuel
      (.ofHooks (annealStepHooksLM2_4 b.localDecls b.layouts) annealControlHooks) 1
      (miriEntryState b) = .running unionOverlayPreMiri := rfl
  have hrel₀ : StateRel b unionOverlayPreAnneal unionOverlayPreMiri := by
    refine StateRel.mk unionOverlayPreMiriFrame rfl rfl
      ⟨translateTy Witness.lm24U32Ty Witness.lm24Layouts, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | _ + 2 => simp [unionOverlayPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 1 =>
      have hs : slot = .uninit := by simpa [unionOverlayPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [unionOverlayPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | _ + 2 => simp [b, unionOverlayPunBody, get?] at hdecl
  have himm₀ : ∀ j tf, unionOverlayPreMiri.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j tf h mls hmls mp hv
    have htf : unionOverlayPreMiriFrame = tf := by simpa [unionOverlayPreMiri] using h
    subst htf
    match j with
    | 0 | 1 => simp [unionOverlayPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 2 => simp [unionOverlayPreMiriFrame] at hmls
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hcU32 : ∀ tf, WellTypedScalarOperand b tf
      (.constant (Witness.lm24ConstU32 0x04030201)) Witness.lm24U32Ty :=
    fun _ => .constScalar (Witness.lm24ConstU32 0x04030201) ⟨0x04030201, 4⟩ rfl
      Witness.lm24_isPrim_u32 (Or.inr (Or.inr (Or.inl rfl))) (by decide) rfl
      (fun h => nomatch h) (fun h => nomatch h)
  have hcU8 : ∀ tf, WellTypedScalarOperand b tf
      (.constant (Witness.lm24ConstU8 0x09)) Witness.lm24U8Ty :=
    fun _ => .constScalar (Witness.lm24ConstU8 0x09) ⟨0x09, 1⟩ rfl
      Witness.lm24_isPrim_u8 (Or.inl rfl) (by decide) rfl
      (fun h => nomatch h) (fun h => nomatch h)
  have hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls b.layouts "U" b.localDecls,
      b.layouts.entries[(Witness.lm24Decl Witness.lm24UTy).ty.layoutIdx]? = some l := by
    have hs : stringEq "U" "U" = true := by decide
    simp [b, collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, hs, LayoutTable.lookup,
      unionOverlayPunBody, Witness.lm24Layouts, Witness.lm24Decl, Witness.lm24UTy,
      Witness.lm24U32Ty, get?, eq_comm]
  let uSlot₁ : LocalSlot := .init (.aggregate 0 [.unit, .scalar ⟨0x04030201, 4⟩])
  let mergedBs : List AbstractByte :=
    encodeLittleEndianBytes 0x09 1 none ++
      ((encodeLittleEndianBytes 0x04030201 4 none).drop 1 ++ replicateUninitBytes 0)
  let uSlot₂ : LocalSlot :=
    .init (.aggregate 0 [.scalar ⟨0x09, 1⟩, .unit, .aggregate 0 (encodeRawAbstractByteVals mergedBs)])
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, uSlot₁] }
      memory := (initMachineState b []).memory }
  let s₂ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3, locals := [.uninit, uSlot₂] }
      memory := (initMachineState b []).memory }
  let s₃ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4, locals := [.init (.scalar ⟨0x04030209, 4⟩), uSlot₂] }
      memory := (initMachineState b []).memory }
  have hs₁ : stepMirFn b unionOverlayPreAnneal = .step s₁ := rfl
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hs₄ : stepMirFn b s₃ = .retNormal (.scalar ⟨0x04030209, 4⟩) s₃.memory := rfl
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation hrel₀.toLM2_4
    List.Pairwise.nil MemoryHighWater.empty.canReserveAllocId hphase
    (u := 1) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl (by decide) rfl rfl rfl
    (himm₀ 1) Witness.lm24_isPrim_u32 (fun tf _ => hcU32 tf) (by decide)
    (hdecls_adt := hdecls_adt)
  obtain ⟨sc₁, mp, m₁, tf₁, hm₁, hop₁, hst₁, hu_slot₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, _, _, _, hhw₁⟩ := hpost₁ s₁ hs₁
  have hsc₁ : sc₁ = ⟨0x04030201, 4⟩ := by
    have h : evalOperand unionOverlayPreAnneal.frame.locals
        (.constant (Witness.lm24ConstU32 0x04030201)) .nil unionOverlayPreAnneal.memory.globals
        b.layouts = .ok (.scalar ⟨0x04030201, 4⟩) unionOverlayPreAnneal.frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hmsc₀ : ∃ msc0 : Miri.Memory.ScalarInt,
      ImmediateRel Witness.lm24U32Ty b.layouts (.scalar ⟨0x04030201, 4⟩)
        (.scalar (.fromScalarInt msc0)) := by
    cases hmem₁ with
    | mk _ _ _ _ msc0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi0 _ => exact ⟨msc0, hi0⟩
  have hu_init₁ : UnionInitSlotRel b.layouts Witness.lm24UTy 4 2 ⟨0x04030201, 4⟩ uSlot₁ :=
    .plain 1 Witness.lm24U32Ty (by decide) Witness.lm24_isPrim_u32 hmsc₀ ⟨_, rfl, rfl⟩
  obtain ⟨_, hpost₂⟩ := step_union_narrower_field_write_simulation hst₁ hnodup₁ hphase
    (u := 1) (j := 0) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl (by decide) hu_slot₁ hu_init₁
    hu_mls₁ hmem₁ (by intro h; cases h) (by intro h; cases h) Witness.lm24_isPrim_u8
    (fun tf _ => hcU8 tf) (by decide)
  obtain ⟨_, hov₂_raw, _, m₂, _, tf₂, _, _, _, hm₂, hst₂, _, hframes₂, hu_mls₂_eq,
    himm₂, hmach_live₂, _, hnodup₂, _, _, _, hmem₂_raw, hhw₂_raw⟩ := hpost₂ ⟨0x09, 1⟩ rfl
  change StateRelLM2_4 b s₂ m₂ at hst₂
  have hsp : unionSpliceLowScalar ⟨0x04030201, 4⟩ ⟨0x09, 1⟩ = ⟨0x04030209, 4⟩ := by
    unfold unionSpliceLowScalar; rw [scalarModulus_eq_two_pow]; rfl
  have hmem₂ : UnionMemRel m₂.machine Witness.lm24UTy Witness.lm24Layouts 4
      Witness.lm24U32Ty ⟨0x04030209, 4⟩ mp := hsp ▸ hmem₂_raw
  have hov₂ : UnionOverlaySlotSpec b.layouts Witness.lm24UTy 4 2 0 ⟨0x04030209, 4⟩
      ⟨0x09, 1⟩ mergedBs := hsp ▸ hov₂_raw
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h; exact ⟨_, hu_mls₂_eq⟩
  have hr_imm₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0 := by
    intro tf htf; rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact himm₂ tf₁ hframes₁ 0 (himm₁ unionOverlayPreMiriFrame rfl 0 (by decide) (himm₀ 0 _ rfl))
  obtain ⟨_, _, hpost₃⟩ := step_union_overlay_field_read_simulation hst₂ hnodup₂ hphase
    (bb := _) (r := 0) (u := 1) (j := 1) (fty := Witness.lm24U32Ty) (isMove := false)
    rfl rfl rfl rfl rfl Witness.lm24_isPrim_u32 (Or.inr (Or.inr (Or.inl rfl))) rfl
    Witness.lm24_wt_U rfl (by decide) hov₂ rfl hu_mls₂ hmem₂ hr_imm₂ (by decide) (by decide)
    (fun h => nomatch h) (fun h => nomatch h)
  obtain ⟨s₃', m₃, tf₃, _, hs₃', hm₃, hst₃, _, hmach₃, hframes₃, _, _⟩ :=
    hpost₃ (fun h => nomatch h)
  have hs₃_eq : s₃' = s₃ := by
    have h := hs₃'.symm.trans hs₃
    unfold MirStepNode.step at h; injection h with h; injection h
  subst hs₃_eq
  have himm₃_0 : ∀ topFrame, m₃.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0 := by
    intro tf₃' htf₃' mls₀ hmls₀ mp₀ hmp₀
    rcases hst₃ with ⟨tf₃'', htf₃'', _, _, hfr₃, _, _, _, _, _, hdisj₃⟩
    have htf_eq : tf₃' = tf₃'' := by rw [htf₃'] at htf₃''; injection htf₃'' with h; injection h
    subst htf_eq
    obtain ⟨_, _, _, _, _, hm₀, _, hul₀⟩ :=
      hfr₃.lookup_local (i := 0) (decl := Witness.lm24Decl Witness.lm24U32Ty) rfl
    obtain ⟨sl₁, ml₁, _, _, hs₁_l, hm₁_l, _, hul₁⟩ :=
      hfr₃.lookup_local (i := 1) (decl := Witness.lm24Decl Witness.lm24UTy) rfl
    have hsl₁ : sl₁ = uSlot₂ := Option.some.inj hs₁_l.symm
    dsimp [uSlot₂] at hsl₁
    rw [hmls₀] at hm₀; injection hm₀ with hm₀; subst hm₀
    rcases mls₀ with ⟨_, lay₀⟩; dsimp only at hmp₀; subst hmp₀
    have hid_eq1 : ∀ id la, (id, la) ∈ m₃.machine.memory.live.toList → id.value.toNat = 1 := by
      intro id la hlive
      have hc_pre : unionOverlayPreMiri.machine.memory.nextAllocId.toNat = 1 := rfl
      have hhw₁_app := hhw₁ rfl MemoryHighWater.empty (by decide)
      have hle_next₁ : m₁.machine.memory.nextAllocId.toNat ≤ 2 := by
        have h := hhw₁_app.2; dsimp only at h; omega
      have hhw₂_app := hhw₂_raw rfl hhw₁_app.1 (by omega)
      have hle_next₂ : m₂.machine.memory.nextAllocId.toNat ≤ 2 := by
        have h := hhw₂_app.2; dsimp only at h; omega
      have hlt : id.value.toNat < m₃.machine.memory.nextAllocId.toNat := by
        have hhw₃_mem : MemoryHighWater m₃.machine.memory := by
          rw [hmach₃]; exact hhw₂_app.1
        have h_in : (id, la) ∈ m₃.machine.memory.live := by simpa using hlive
        exact hhw₃_mem.live_lt ⟨id, la⟩ h_in
      have hle_next : m₃.machine.memory.nextAllocId.toNat ≤ 2 := by
        rw [hmach₃]; omega
      have hpos := Nat.pos_of_ne_zero fun h0 => id.nonzero (UInt64.toNat_inj.mp h0)
      omega
    have hid₀ : ∃ id₀ : Miri.Memory.AllocId,
        mp₀.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id₀ ∧
        id₀.value.toNat = 1 := by
      cases hul₀ with
      | union _ _ _ _ _ _ _ _ _ _ _ hm =>
        rcases hm with ⟨id₀, _, _, la₀, _, hp₀, _, _, hlive₀, _⟩
        exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
      | unionOverlay _ _ _ _ _ _ _ _ _ _ _ _ _ hm =>
        rcases hm with ⟨id₀, _, _, la₀, _, hp₀, _, _, hlive₀, _⟩
        exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
      | base _ _ hl₀ =>
        cases hl₀ with
        | indirect _ _ _ _ _ hm =>
          rcases hm with ⟨id₀, _, _, _, la₀, hp₀, _, _, hlive₀, _⟩
          exact ⟨id₀, by rw [hp₀]; rfl, hid_eq1 id₀ la₀ hlive₀⟩
    have hid₁ : ∃ (mp₁ : Miri.Interpreter.MemPlace AnnealProv)
        (lay₁ : Option Miri.Interpreter.LocalLayout) (id₁ : Miri.Memory.AllocId),
        tf₃'.locals[1]? = some ⟨.live (.indirect mp₁), lay₁⟩ ∧
        mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id₁ ∧
        id₁.value.toNat = 1 := by
      cases hul₁ with
      | union _ _ _ _ _ mp₁ lay₁ _ _ _ _ hm =>
        rcases hm with ⟨id₁, _, _, la₁, _, hp₁, _, _, hlive₁, _⟩
        exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
      | unionOverlay _ _ _ _ _ _ _ mp₁ lay₁ _ _ _ _ hm =>
        rcases hm with ⟨id₁, _, _, la₁, _, hp₁, _, _, hlive₁, _⟩
        exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
      | base _ _ hl₁ =>
        cases hl₁ with
        | dead _ _ => cases hsl₁
        | immediate _ _ _ _ hval =>
          rw [hsl₁] at hval
          rcases hval with ⟨h, _⟩ | ⟨v, hv, himm⟩
          · cases h
          · injection hv with hv; subst hv; cases himm
        | indirect _ mp₁ lay₁ _ _ hm =>
          rcases hm with ⟨id₁, _, _, _, la₁, hp₁, _, _, hlive₁, _⟩
          exact ⟨mp₁, lay₁, id₁, hm₁_l, by rw [hp₁]; rfl, hid_eq1 id₁ la₁ hlive₁⟩
    obtain ⟨id₀, hp₀, hv₀⟩ := hid₀
    obtain ⟨mp₁, lay₁, id₁, hm₁', hp₁, hv₁⟩ := hid₁
    have heq_id : id₀ = id₁ := by
      rcases id₀ with ⟨x₀, _⟩; rcases id₁ with ⟨x₁, _⟩
      have : x₀ = x₁ := UInt64.toNat_inj.mp (hv₀.trans hv₁.symm)
      subst this; rfl
    exact hdisj₃ 0 1 mp₀ mp₁ lay₀ lay₁ (by decide) hmls₀ hm₁' (by rw [hp₀, hp₁, heq_id])
  have hsim₄ := step_terminator_return_lm2_4_simulation hst₃ hphase rfl rfl rfl rfl rfl
    (decl0 := Witness.lm24Decl Witness.lm24U32Ty) rfl (by decide) himm₃_0
  rw [hs₄] at hsim₄
  generalize hm₄_eq : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 b.localDecls b.layouts) () m₃ = mRes₄ at hsim₄
  cases hsim₄ with
  | retRoot decl0 _ imm0 _ m₄ hdecl0 hop0 himm0 hm₄ =>
    have hd0 : decl0 = Witness.lm24Decl Witness.lm24U32Ty := Option.some.inj hdecl0.symm
    subst hd0
    refine ⟨imm0, ?_, himm0⟩
    exact agreeReturns_of_paths hpa hpm
      (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.refl _)))) hs₄
      (.step hm₁ (frames_ne_of_eq_singleton hframes₁)
        (.step hm₂ (frames_ne_of_eq_singleton hframes₂)
          (.step hm₃ (frames_ne_of_eq_singleton hframes₃) (.refl _))))
      hm₄_eq (by rw [hm₄]) (by change (annealControlHooks.returnOperand () m₃).2 = _; rw [hop0])

/-! ## 6. Intrinsics (memory) -/

/-- Entry-to-UB MIR body for overlapping `CopyNonOverlapping` (`src = dst`,
no `miri-diff` corpus program):
`bb0: StorageLive(_1.._3); _1 = 42_u64; goto bb1;
bb1: _2 = &raw mut _1; copy_nonoverlapping(copy _2, copy _2, 1); return`. -/
def copyOverlapEntryBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::copy_overlap_entry"
    WitnessLM4_2.unitK WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1))),
     WitnessLM4_2.copyStmt 2 2 1]
    .return_

/-- `CopyNonOverlapping` with overlapping source and destination (`src = dst`,
`copyOverlapEntryBody`; no `miri-diff` corpus program) is undefined behavior in
both machines from program entry. -/
theorem w6_copy_nonoverlapping_overlap_ub :
    AgreeUB copyOverlapEntryBody (annealMiriHooks copyOverlapEntryBody)
      (initMachineState copyOverlapEntryBody [])
      (miriEntryState copyOverlapEntryBody) := by
  let b := copyOverlapEntryBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b "lm_4_3_witness::copy_overlap_entry"
    WitnessLM4_2.unitK WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1))),
     WitnessLM4_2.copyStmt 2 2 1] .return_ rfl
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4EntryPreMiri b).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4EntryPreAnneal b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4EntryPreMiri b).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  obtain ⟨_, hsim₂⟩ := step_intrinsic_copyNonOverlapping_stage1_simulation
    (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u64K)
    hrel₁ hphase rfl rfl rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    WitnessLM4_2.usize_integral
    (fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₁)
    WitnessLM4_2.u64_copyPointee (by decide)
    (by
      intro _ _ countSc _ _ hc hc0
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      subst hc'; cases hc0)
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ => cases hd_s; cases hd_d; exact ⟨rfl, rfl, rfl, rfl⟩)
    (by
      intro srcPtr dstPtr countSc hsrc hdst hc _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, WitnessLM4_2.mkPtrState, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, WitnessLM4_2.mkPtrState, get?] using hdst.symm
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      subst hpS hpD hc'; exact ⟨rfl, rfl, rfl⟩)
    (by
      intro _ _ _ e_s e_d _ _ _ _ he_s _ he_d _ _ _
      cases he_s with
      | tail _ h => cases h
      | head _ =>
        cases he_d with
        | tail _ h => cases h
        | head _ =>
          exact ⟨by nofun, Or.inl rfl,
            by simp [s₁, WitnessLM4_2.mkPtrState, entry, rawPtrAllocMapEntry, get?]⟩)
  have hfail : stepMirFn b s₁ = .fail .ub := rfl
  rw [hfail] at hsim₂
  obtain ⟨m₂, msg, herr⟩ := hsim₂.miri_ub_of_anneal_ub
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  exact agreeUB_of_paths (p := 5) rfl rfl (.step .silent hs₁ (.refl _)) hfail
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

/-- Anneal's state of a `ptr4Body` after `_2 = &raw mut _1` (`_2` holds the raw
pointer to `_1`'s stack allocation `1`, tagged `1`). -/
def wbAddrOfState (b : CapturedMir) : MachineState :=
  WitnessLM4_2.mkPtrState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [(rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1).toBorrowEntry] 2

/-- **Stage-1 external-call boundary** (`write_bytes::<u64>(ptr, 0xAB, 1)`,
`writeBytesMutBody 0xAB 1`): both machines take the `_2 = &raw mut _1` step in
lockstep (`AgreeReaches`). Then Stage-1 `stepMirFn` hands `write_bytes` to the
environment (`MirStepNode.extCall`, `WitnessLM4_2.wit_lm4_2_write_bytes_boundary`):
when the environment returns `()` without touching memory, Anneal's whole program
returns `()`; when it unwinds, the call's `UnwindAction::Unreachable` is undefined
behavior, so Anneal's whole program is not `TreeSafe`. `lean-miri` executes
`write_bytes` inline: `miriSystem` reaches a state `StateRelLM3_1`-related to an
Anneal state with `_1 = 0xABABABABABABABAB`. (Before Stage-1, Anneal wrote the
bytes inline in lockstep with `lean-miri`.) -/
theorem w6_write_bytes_extCall_boundary :
    ∃ m₁ m₂,
      AgreeReaches (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 1))
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1))
        (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1))
        (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 1) WitnessLM4_2.unitK) m₁ ∧
      stepMirFn (WitnessLM4_2.writeBytesMutBody 0xAB 1)
          (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1)) =
        WitnessLM4_2.ptr4Stage1ExtCall "core::intrinsics::write_bytes" WitnessLM4_2.u64K
          (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1))
          [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨0xAB, 1⟩, .scalar ⟨1, 8⟩] ∧
      (∃ tr mem, ReachesRet (mirTree (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1))) tr
          (.normal (.unit, mem))) ∧
      MirReachesUB (mirTree (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1))) ∧
      ¬ TreeSafe (mirTree (WitnessLM4_2.writeBytesMutBody 0xAB 1)
        (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1))) ∧
      (miriSystem (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 1))).Reaches
        (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 1) WitnessLM4_2.unitK) m₂ ∧
      ∃ s₂, StateRelLM3_1 (WitnessLM4_2.writeBytesMutBody 0xAB 1) s₂ m₂
          [rawPtrAllocMapEntry (WitnessLM4_2.writeBytesMutBody 0xAB 1).localDecls
            (WitnessLM4_2.writeBytesMutBody 0xAB 1).layouts .mut 1 1 Witness.lm31AllocId1] ∧
        get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) := by
  obtain ⟨s₁, m₁, m₂, hs₁, hm₁, hrel₁, hext, hm₂, s₂, hrel₂, hget⟩ :=
    WitnessLM4_2.wit_lm4_2_write_bytes_boundary
  have hs₁' : stepMirFn (WitnessLM4_2.writeBytesMutBody 0xAB 1)
      (WitnessLM4_2.ptr4AnnealPre (WitnessLM4_2.writeBytesMutBody 0xAB 1)) =
      .step (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1)) := rfl
  have hs_eq : s₁ = wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1) := by
    have h := hs₁.symm.trans hs₁'
    unfold MirStepNode.step at h
    injection h with h
    injection h
  subst hs_eq
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  have hM₂ : MiriPath (annealMiriHooks (WitnessLM4_2.writeBytesMutBody 0xAB 1))
      (WitnessLM4_2.ptr4MiriPre (WitnessLM4_2.writeBytesMutBody 0xAB 1) WitnessLM4_2.unitK) m₂ :=
    .step hm₁ (frames_ne_of_eq_singleton htf₁) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _))
  obtain ⟨⟨tr, hrr⟩, hub, hns⟩ := anneal_extCall_boundary
    (retVal := .unit) (v := .unit)
    (mem := (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1)).memory)
    (.step .silent hs₁ (.refl _)) hext rfl (.refl _) rfl
    (wbAddrOfState (WitnessLM4_2.writeBytesMutBody 0xAB 1)).memory
  exact ⟨m₁, m₂, agreeReaches_of_paths (.step .silent hs₁ (.refl _))
      (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _)),
    hext, ⟨tr, _, hrr⟩, hub, hns, hM₂.reaches, s₂, hrel₂, hget⟩

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

/-- **Stage-1 `StorageDead` with active `CallId` protector** (`LM-3.3` `D15`,
`SimLM3_3.sim_lm3_3_storage_dead_and_live_protector_step`): across all 6-state
`TreeBorrowPerm` permissions `perm`:
* when `activeProtectors = [1]`, Anneal's whole program faults with undefined
  behavior (`MirReachesUB ∧ ¬ TreeSafe`), and for every non-`Cell` permission
  (`perm ≠ .cell`), `lean-miri`'s `BorrowTree.deallocateBorrowRange` also rejects
  the protected deallocation (`status ≠ Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated`);
* when `activeProtectors = []`, `StorageDead(_1)` steps cleanly, disabling the
  local borrow in `TreeBorrowsRel` lockstep with `deallocateBorrowRange`;
* on a protected `Cell` (`perm = .cell`), Stage-1 Anneal faults (`MirReachesUB`)
  while `deallocateBorrowRange` succeeds (`sim_lm3_3_storage_dead_protected_cell_divergence`). -/
theorem w4_storage_dead_protected_ub (perm : TreeBorrowPerm) :
    (MirReachesUB (mirTree SimLM3_3.storageDeadBody (SimLM3_3.childState perm true)) ∧
      ¬ TreeSafe (mirTree SimLM3_3.storageDeadBody (SimLM3_3.childState perm true))) ∧
    (perm ≠ .cell →
      ((hooksTwoNodeTree perm).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected true).protectedTags).status ≠ Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) ∧
    (∃ s_dead : MachineState,
      stepMirFn SimLM3_3.storageDeadBody (SimLM3_3.childState perm false) = .step s_dead ∧
      s_dead.memory.borrows = [SimLM3_3.entry 1 .disabled] ∧
      TreeBorrowsRel s_dead.memory.borrows [] (basedNormalTree s_dead.memory.borrows []) ∧
      ((hooksTwoNodeTree perm).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected false).protectedTags).status = Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) ∧
    (((hooksTwoNodeTree .cell).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected true).protectedTags).status = Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) := by
  obtain ⟨hub, _, hne_cell, ⟨s_dead, _, hs_dead, _, hb_dead, hrel_dead, _, _, _, _⟩, hdealloc_ok⟩ :=
    SimLM3_3.sim_lm3_3_storage_dead_and_live_protector_step perm
  exact ⟨anneal_ub_of_coReach (.refl _) hub, hne_cell,
    ⟨s_dead, hs_dead, hb_dead, hrel_dead, hdealloc_ok⟩,
    SimLM3_3.sim_lm3_3_storage_dead_protected_cell_divergence.2.2⟩

/-! ## 5. Multi-frame calls -/

/-- The body of the active `lean-miri` frame among `bodies` (by translation). -/
def frameBody (bodies : List CapturedMir) (fallback : CapturedMir) (m : AnnealStepState) :
    CapturedMir :=
  match m.stack.currentFrame? with
  | some f => (bodies.find? fun b => decide (translateBody b = f.body)).getD fallback
  | none => fallback

/-- The `LM-4.1` multi-frame interpreter: `annealStepHooksLM4_1` instantiated at the
body of the active frame (with optional registered function pointers `fnPtrs`),
and `annealControlHooksLM4_1` reading the root's `_0`. -/
def callHooks (root : CapturedMir) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) : AnnealMiriHooks :=
  multiFrameHooks root fun c m =>
    Miri.Interpreter.Step.step
      (annealStepHooksLM4_1 (frameBody (root :: callees) root m) callees {} fnPtrs) c m

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
      [] rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl
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

/-! ### Stage-1 multi-frame stack unwinding and indirect `FnPtr` calls from entry -/

/-- Leaf callee `crate::unwind_leaf`: jumps to cleanup `bb1` and executes `UnwindResume`. -/
def unwindLeafBody : CapturedMir :=
  { mkBody "crate::unwind_leaf" [dcl tyU8]
      [blk [] (.goto 1),
       { statements := [], terminator := tm .unwindResume, isCleanup := true }] with
    defPath := "crate::unwind_leaf",
    fnAbi := { args := [], ret := { layout := u8Layout, mode := .direct },
               conv := .rust, canUnwind := true } }
  where u8Layout : TypeLayout :=
    { size := ⟨1⟩, align := ⟨0⟩, fields := .primitive, variants := .single 0,
      backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
      isUninhabited := false, fieldLayouts := [] }

def unwindLeafFnTy : Ty := { kind := .fnDef "crate::unwind_leaf" [], layoutIdx := 0 }

/-- Middle callee `crate::unwind_mid`: calls `crate::unwind_leaf` with `UnwindAction::Continue`. -/
def unwindMidBody : CapturedMir :=
  { mkBody "crate::unwind_mid" [dcl tyU8]
      [blk [] (.call (.constant { ty := unwindLeafFnTy, val := .zeroSized }) []
        (pl 0) (some 1) .continue_),
       blk [] .return_] with
    defPath := "crate::unwind_mid",
    fnAbi := unwindLeafBody.fnAbi }

def unwindMidFnTy : Ty := { kind := .fnDef "crate::unwind_mid" [], layoutIdx := 0 }

/-- Root caller catching a 2-frame (`k = 2`) `UnwindResume` unwind at cleanup `bb2`,
jumping to `bb3`, writing `_0 = const 77_u8`, and returning normally. -/
def unwindCatchRootBody : CapturedMir :=
  mkBody "crate::unwind_catch_root" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
       (.call (.constant { ty := unwindMidFnTy, val := .zeroSized }) []
         (pl 1) (some 1) (.cleanup 2)),
     blk [st (.assign (pl 0) (.use (.copy (pl 1))))] .return_,
     { statements := [], terminator := tm (.goto 3), isCleanup := true },
     blk [st (.assign (pl 0) (.use (cU8 77))), st (.storageDead 1)] .return_]

/-- **Stage-1 multi-frame stack unwinding caught at cleanup pad, from entry**
(`unwindCatchRootBody -> unwindMidBody -> unwindLeafBody`): `unwindLeafBody`
executes `UnwindResume`, unwinding across 2 frames (`unwindLeafBody` and
`unwindMidBody`'s `.continue_` edge) into `unwindCatchRootBody`'s `.cleanup 2`
landing pad, and both machines return `77_u8` (`AgreeReturnsBits`). -/
theorem w5_unwind_cleanup_returns :
    AgreeReturnsBits unwindCatchRootBody
      (callHooks unwindCatchRootBody [unwindMidBody, unwindLeafBody])
      (initMachineStateWithCallees unwindCatchRootBody [] [unwindMidBody, unwindLeafBody])
      (miriEntryState unwindCatchRootBody) 1 77 :=
  agreeReturnsBits_of_obs (N := 12) (M := 14) (by decide) (by decide +kernel)

/-- Root caller whose call to `crate::unwind_mid` carries `UnwindAction::Unreachable`. -/
def unwindUnreachableRootBody : CapturedMir :=
  mkBody "crate::unwind_unreachable_root" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
       (.call (.constant { ty := unwindMidFnTy, val := .zeroSized }) []
         (pl 1) (some 1) .unreachable),
     blk [st (.assign (pl 0) (.use (.copy (pl 1))))] .return_]

/-- **Stage-1 multi-frame stack unwinding into `UnwindAction::Unreachable`, from entry**:
unwinding across `unwindMidBody` into `unwindUnreachableRootBody`'s `.unreachable`
unwind action raises undefined behavior in both machines (`AgreeUB`). -/
theorem w5_unwind_unreachable_ub :
    AgreeUB unwindUnreachableRootBody
      (callHooks unwindUnreachableRootBody [unwindMidBody, unwindLeafBody])
      (initMachineStateWithCallees unwindUnreachableRootBody [] [unwindMidBody, unwindLeafBody])
      (miriEntryState unwindUnreachableRootBody) :=
  agreeUB_of_obs (N := 8) (M := 10) (by decide) (by decide +kernel)

/-- Root caller whose call to `crate::unwind_mid` carries `UnwindAction::Continue`,
so `UnwindResume` unwinds all the way past the root stack frame. -/
def unwindPastRootBody : CapturedMir :=
  mkBody "crate::unwind_past_root" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
       (.call (.constant { ty := unwindMidFnTy, val := .zeroSized }) []
         (pl 1) (some 1) .continue_),
     blk [st (.assign (pl 0) (.use (.copy (pl 1))))] .return_]

/-- **Stage-1 multi-frame root-unwind divergence, from entry**
(`step_terminator_unwindResume_root_panic_vs_ub_divergence`): unwinding across
both callees and past `unwindPastRootBody`'s root `.continue_` edge halts with
`.retOutcome .panic` in Stage-1 Anneal (a defined panic outcome, so `TreeSafe`
holds), while `lean-miri` reports `"unwinding past the topmost stack frame"`
undefined behavior (`¬ System.Safe`). -/
theorem w5_unwind_root_panic_vs_ub_divergence :
    TreeSafe (mirTree unwindPastRootBody
      (initMachineStateWithCallees unwindPastRootBody [] [unwindMidBody, unwindLeafBody])) ∧
    (∃ e, (miriSystem (callHooks unwindPastRootBody [unwindMidBody, unwindLeafBody])).ReachesOutcome
      (miriEntryState unwindPastRootBody) (.undefinedBehavior e)) ∧
    ¬ (miriSystem (callHooks unwindPastRootBody [unwindMidBody, unwindLeafBody])).Safe
      (miriEntryState unwindPastRootBody) := by
  have hm := miri_ub_of_obs
    (H := callHooks unwindPastRootBody [unwindMidBody, unwindLeafBody]) (N := 12)
    (m := miriEntryState unwindPastRootBody) (by decide +kernel)
  refine ⟨?_, hm.1, hm.2⟩
  let s₀ := initMachineStateWithCallees unwindPastRootBody [] [unwindMidBody, unwindLeafBody]
  have hsteps :
      ∃ s₁ s₂ s₃ s₄,
        stepMirFn unwindPastRootBody s₀ = .step s₁ ∧
        stepMirFn unwindPastRootBody s₁ = .step s₂ ∧
        stepMirFn unwindPastRootBody s₂ = .step s₃ ∧
        stepMirFn unwindPastRootBody s₃ = .step s₄ ∧
        stepMirFn unwindPastRootBody s₄ = .retOutcome .panic :=
    ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨s₁, s₂, s₃, s₄, hs₀, hs₁, hs₂, hs₃, hs₄⟩ := hsteps
  rw [mirTree_eq_cofix, treeSafe_cofix_iff]
  intro y hy hf
  have hchain : ∀ x z, CoReach (stepMirState unwindPastRootBody) x z →
      x = .running s₀ ∨ x = .running s₁ ∨ x = .running s₂ ∨ x = .running s₃ ∨ x = .running s₄ →
      z = .running s₀ ∨ z = .running s₁ ∨ z = .running s₂ ∨ z = .running s₃ ∨ z = .running s₄ := by
    intro x z hz
    induction hz with
    | refl _ => exact fun hx => hx
    | head hstep hr ih =>
      intro hx
      apply ih
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · cases hstep with
        | tau ht => change stepMirState unwindPastRootBody (.running s₀) = _ at ht; dsimp [stepMirState] at ht; rw [hs₀] at ht; injection ht with ht; exact Or.inr (Or.inl (by rw [ht]))
        | vis hv _ _ => change stepMirState unwindPastRootBody (.running s₀) = _ at hv; dsimp [stepMirState] at hv; rw [hs₀] at hv; cases hv
      · cases hstep with
        | tau ht => change stepMirState unwindPastRootBody (.running s₁) = _ at ht; dsimp [stepMirState] at ht; rw [hs₁] at ht; injection ht with ht; exact Or.inr (Or.inr (Or.inl (by rw [ht])))
        | vis hv _ _ => change stepMirState unwindPastRootBody (.running s₁) = _ at hv; dsimp [stepMirState] at hv; rw [hs₁] at hv; cases hv
      · cases hstep with
        | tau ht => change stepMirState unwindPastRootBody (.running s₂) = _ at ht; dsimp [stepMirState] at ht; rw [hs₂] at ht; injection ht with ht; exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [ht]))))
        | vis hv _ _ => change stepMirState unwindPastRootBody (.running s₂) = _ at hv; dsimp [stepMirState] at hv; rw [hs₂] at hv; cases hv
      · cases hstep with
        | tau ht => change stepMirState unwindPastRootBody (.running s₃) = _ at ht; dsimp [stepMirState] at ht; rw [hs₃] at ht; injection ht with ht; exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [ht]))))
        | vis hv _ _ => change stepMirState unwindPastRootBody (.running s₃) = _ at hv; dsimp [stepMirState] at hv; rw [hs₃] at hv; cases hv
      · cases hstep with
        | tau ht => change stepMirState unwindPastRootBody (.running s₄) = _ at ht; dsimp [stepMirState] at ht; rw [hs₄] at ht; cases ht
        | vis hv _ _ => change stepMirState unwindPastRootBody (.running s₄) = _ at hv; dsimp [stepMirState] at hv; rw [hs₄] at hv; cases hv
  rcases hchain _ _ hy (Or.inl rfl) with rfl | rfl | rfl | rfl | rfl
  · change IsFaultNode (stepMirState unwindPastRootBody (.running s₀)) at hf
    dsimp [stepMirState] at hf; rw [hs₀] at hf; obtain ⟨_, _, h, _⟩ := hf; cases h
  · change IsFaultNode (stepMirState unwindPastRootBody (.running s₁)) at hf
    dsimp [stepMirState] at hf; rw [hs₁] at hf; obtain ⟨_, _, h, _⟩ := hf; cases h
  · change IsFaultNode (stepMirState unwindPastRootBody (.running s₂)) at hf
    dsimp [stepMirState] at hf; rw [hs₂] at hf; obtain ⟨_, _, h, _⟩ := hf; cases h
  · change IsFaultNode (stepMirState unwindPastRootBody (.running s₃)) at hf
    dsimp [stepMirState] at hf; rw [hs₃] at hf; obtain ⟨_, _, h, _⟩ := hf; cases h
  · change IsFaultNode (stepMirState unwindPastRootBody (.running s₄)) at hf
    dsimp [stepMirState] at hf; rw [hs₄] at hf; obtain ⟨_, _, h, _⟩ := hf; cases h

/-- Safe `fn() -> u8` pointer type and entry for `crate::five`. -/
def fiveFnPtrTy : Ty := { kind := .fnPtr [] (.uint .u8) .safe .rust, layoutIdx := 0 }

def fiveFnPtrEntry : FnPtrEntry :=
  { allocId := fnPtrAllocBase
    defPath := "crate::five"
    typeArgs := []
    fnSig := some (.fnPtr [] (.uint .u8) .safe .rust) }

/-- Caller reifying `crate::five` via `PointerCoercion(ReifyFnPointer)` and
invoking it through an indirect `FnPtr` `Call(move _2)` from entry. -/
def indirectCallFiveBody : CapturedMir :=
  mkBody "crate::indirect_call_five" [dcl tyU8, dcl tyU8, dcl fiveFnPtrTy]
    [blk [st (.storageLive 1), st (.storageLive 2),
          st (.assign (pl 2)
            (.cast (.pointerCoercion "ReifyFnPointer")
              (.constant { ty := fiveFnTy, val := .zeroSized }) fiveFnPtrTy))]
       (.call (.move (pl 2)) [] (pl 1) (some 1) .continue_),
     blk [st (.assign (pl 0) (.use (.copy (pl 1)))),
          st (.storageDead 2), st (.storageDead 1)] .return_]

/-- **Stage-1 `ReifyFnPointer` + indirect `FnPtr` call and return, from entry**:
`indirectCallFiveBody` coerces `crate::five` to `fn() -> u8`, calls `move _2`
indirectly, receives `5_u8`, and returns `5_u8` in both machines (`AgreeReturnsBits`).
`AnnealMachine` has no function-pointer registry, so the `lean-miri` hooks read the
function pointer from the static table `[fiveFnPtrEntry]` (`callHooks … fnPtrs`),
the entry that Stage-1's `ReifyFnPointer` registers in `Memory.fnPtrs` during the
run (`indirectCallFive_reify_fnPtrs`). -/
theorem w5_indirect_fnPtr_call_returns :
    AgreeReturnsBits indirectCallFiveBody
      (callHooks indirectCallFiveBody [fiveBody] [fiveFnPtrEntry])
      (initMachineStateWithCallees indirectCallFiveBody [] [fiveBody])
      (miriEntryState indirectCallFiveBody) 1 5 :=
  agreeReturnsBits_of_obs (N := 12) (M := 12) (by decide) (by decide +kernel)

/-- The static function-pointer table `[fiveFnPtrEntry]` of
`w5_indirect_fnPtr_call_returns` is the one Stage-1 builds: after
`StorageLive(_1); StorageLive(_2); _2 = crate::five as fn() -> u8 (ReifyFnPointer)`,
Anneal's `Memory.fnPtrs` is exactly `[fiveFnPtrEntry]`. -/
theorem indirectCallFive_reify_fnPtrs :
    ∃ s, runAnnealBounded indirectCallFiveBody 3
        (initMachineStateWithCallees indirectCallFiveBody [] [fiveBody]) = .running s ∧
      s.memory.fnPtrs = [fiveFnPtrEntry] :=
  ⟨_, rfl, rfl⟩

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

Both machines take the two steps of `wit_lm4_2_arith_offset_pos` in lockstep (the
`arith_offset` call through Stage-1's `call_intrinsic_arithOffset_stage1_simulation`),
and then both return from the root frame. Anneal returns the raw pointer
`{ allocId := 1, offsetBytes := 40 }`, which points `40` bytes past the start of
the 8-byte stack allocation of `_1`, and `lean-miri` returns an immediate
related to it by `ImmediateRelLM3_1.rawPtr`. -/
def arithOffsetPosEntryBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::arith_offset_pos"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    (arithOffsetEntryTerm 2 5)

theorem retArithOffset_trace :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := arithOffsetPosEntryBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (ptr4EntryPreMiri b) = (m₁, .ok true) ∧
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
  let b := arithOffsetPosEntryBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b "lm_4_3_witness::arith_offset_pos"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
      (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    (arithOffsetEntryTerm 2 5) rfl
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4EntryPreMiri b).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  -- Step 1: `_2 = &raw mut _1`.
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : (ptr4EntryPreAnneal b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(ptr4EntryPreMiri b).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  -- Step 2: `_0 = arith_offset::<u64>(copy _2, 5_isize) -> bb2`.
  let s₂ := WitnessLM4_2.mkPtrState b 2 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hcountOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.isizeK 5 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.isizeK) :=
    fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.isize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₁
  have hsim₂ := call_intrinsic_arithOffset_stage1_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl (by decide)) rfl rfl (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    (fun _ h => by simp [s₁, WitnessLM4_2.mkPtrState, get?] at h)
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

/-- `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2` into the unit local
`_3` (block `bb1` of `retWriteBytesReadBody`). -/
def retWriteBytesTerm : TerminatorKind :=
  .call (.constant (WitnessLM4_2.fnItem "core::intrinsics::write_bytes" WitnessLM4_2.u64K))
    [.copy (WitnessLM4_2.local42 2),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.u8K 0xAB 1),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8)]
    (WitnessLM4_2.local42 3) (some 2) .unreachable

/-! ### `write_bytes` return trace

`retWriteBytesCall_preserves_imm` keeps every immediate local of `lean-miri`'s
frame immediate across a `write_bytes` call. With it, `retWriteBytesRead_ref_trace`
needs no `StorageLive(_0)`, and `lean-miri`'s program returns the bytes that
`write_bytes` wrote, read back through the raw pointer, in lockstep with the
pre-Stage-1 reference model; Stage-1 Anneal instead hands the call to the
environment (`w6_write_bytes_read_extCall_divergence`). -/

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

/-- Whole-program `write_bytes` read-back witness, run from program entry
(`_0 : u64`, `_1 : u64`, `_2 : *mut u64`, `_3 : ()`):

```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 42_u64;
     goto -> bb1;
bb1: _2 = &raw mut _1;
     _3 = write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2;
bb2: _0 = copy (*_2);
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
    { statements := [WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
        WitnessLM4_2.mkStmt42 (.storageLive 3),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 42 8))))]
      terminator := WitnessLM4_2.mkTerm42 (.goto 1)
      isCleanup := false },
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

/-- Anneal's state of `retWriteBytesReadBody` after the entry block `bb0`
(`_1 = 42_u64`, every other local uninitialized, at `bb1`). -/
def retWriteBytesReadPreAnneal : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState retWriteBytesReadBody []).memory }

/-- `lean-miri`'s root frame of `retWriteBytesReadBody` after the entry block `bb0`. -/
def retWriteBytesReadPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame retWriteBytesReadBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨1, 0⟩ }

/-- `lean-miri`'s state of `retWriteBytesReadBody` after the entry block `bb0`. -/
def retWriteBytesReadPreMiri : AnnealStepState :=
  { stack := ⟨#[retWriteBytesReadPreMiriFrame]⟩, machine := AnnealMachine.empty }

/-- The entry block (three `StorageLive`s, `_1 = const 42_u64`, `goto`) of
`retWriteBytesReadBody`, from `initMachineState`. -/
theorem retWriteBytesRead_prefix_anneal :
    runAnnealBounded retWriteBytesReadBody 5 (initMachineState retWriteBytesReadBody []) =
      .running retWriteBytesReadPreAnneal := rfl

/-- The entry block of `retWriteBytesReadBody`, from `miriEntryState`. -/
theorem retWriteBytesRead_prefix_miri :
    runLoopFuel (annealMiriHooks retWriteBytesReadBody) 5 (miriEntryState retWriteBytesReadBody) =
      .running retWriteBytesReadPreMiri := rfl

/-- The post-entry-block states of `retWriteBytesReadBody` (`_1 = 42_u64`, all
other locals uninitialized) are `StateRel`-related, and every `lean-miri` local is
immediate. -/
theorem retWriteBytesRead_stateRel :
    StateRel retWriteBytesReadBody retWriteBytesReadPreAnneal retWriteBytesReadPreMiri ∧
    ∀ tf, retWriteBytesReadPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk retWriteBytesReadPreMiriFrame rfl rfl
      ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K), rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | _ + 4 => simp [retWriteBytesReadPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 =>
      have hs : slot = .uninit := by simpa [retWriteBytesReadPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [retWriteBytesReadPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [retWriteBytesReadBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by
        simpa [retWriteBytesReadPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [retWriteBytesReadPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 4 => simp [retWriteBytesReadBody, get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : retWriteBytesReadPreMiriFrame = tf := by simpa [retWriteBytesReadPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 => simp [retWriteBytesReadPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 4 => simp [retWriteBytesReadPreMiriFrame] at hmls

/-- **`retWriteBytesRead_ref_trace`**: `lean-miri`'s run of `retWriteBytesReadBody`
from the post-entry-block state `retWriteBytesReadPreMiri` (reached from
`miriEntryState`, `retWriteBytesRead_prefix_miri`) to its root return, in lockstep
with the pre-Stage-1 reference model `stepMirFnLM4_2` at the `write_bytes` call
and with Stage-1 `stepMirFn` elsewhere, from `retWriteBytesReadPreAnneal`:

1. `_2 = &raw mut _1` (`stepMirFn`);
2. `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2`, which `lean-miri` and
   the reference model execute inline, filling all 8 bytes of `_1` with `0xAB`
   (`0xABAB_ABAB_ABAB_ABAB = 12370169555311111083`); Stage-1 `stepMirFn` instead
   hands the call to the environment (`MirStepNode.extCall`, the conjunct after
   the reference step);
3. `_0 = copy (*_2)`, which reads the written bytes back through the raw
   pointer;
4. the root-frame `return`, at which the reference state returns the scalar
   `0xABAB_ABAB_ABAB_ABAB` and `lean-miri` returns an immediate related to it
   by `ImmediateRel`.

`retWriteBytesCall_preserves_imm` keeps `_0` and `_2` immediate in
`lean-miri`'s frame across the `write_bytes` call. -/
theorem retWriteBytesRead_ref_trace :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := retWriteBytesReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b retWriteBytesReadPreAnneal = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () retWriteBytesReadPreMiri = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFnLM4_2 b s₁ = .step s₂ ∧
      stepMirFn b s₁ =
        MirStepNode.extCall
          { defPath := "core::intrinsics::write_bytes", typeArgs := [WitnessLM4_2.u64K]
            args := [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨0xAB, 1⟩, .scalar ⟨1, 8⟩]
            memory := s₁.memory }
          (resumeExternalCall s₁ s₁.frame.locals (WitnessLM4_2.local42 3) 2 .unreachable) ∧
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
  obtain ⟨hrel₀, himm₀_all⟩ := retWriteBytesRead_stateRel
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, retWriteBytesReadPreMiri.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  -- Step 1: `_2 = &raw mut _1`.
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b retWriteBytesReadPreAnneal = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : retWriteBytesReadPreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨retWriteBytesReadPreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  -- Step 2: `_3 = write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2`.
  let s₂ := WitnessLM4_2.mkPtrState b 2 0
    [.uninit, .init (.scalar ⟨0xABABABABABABABAB, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := rfl
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
  let s₃ := WitnessLM4_2.mkPtrState b 2 1
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
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, hrel₁, hs₂, rfl, hm₂, hrel₂, rfl,
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
        WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
        WitnessLM4_2.mkStmt42 (.storageLive 3), WitnessLM4_2.mkStmt42 (.storageLive 4),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 42 8)))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 99 8))))]
      terminator := WitnessLM4_2.mkTerm42 (.goto 1)
      isCleanup := false },
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
      { blockIdx := 1
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
    location := .mir ⟨1, 0⟩ }

/-- `lean-miri` pre-state of `retCopyBody`. -/
def retCopyMiriPre : AnnealStepState :=
  { stack := ⟨#[retCopyMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem retCopy_prefix_anneal :
    runAnnealBounded retCopyBody 7 (initMachineState retCopyBody []) =
      .running retCopyAnnealPre := rfl

theorem retCopy_prefix_miri :
    runLoopFuel (annealMiriHooks retCopyBody) 7 (miriEntryState retCopyBody) =
      .running retCopyMiriPre := rfl

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
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
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
  let s₂ := WitnessLM4_2.mkPtrState b 1 2
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
  let s₃ := WitnessLM4_2.mkPtrState b 1 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr1, .init ptr2]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have hcount₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      WellTypedScalarOperand b tf₂
        (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 1 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.usizeK) :=
    fun tf₂ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₂
  have hsim₃ := step_intrinsic_copyNonOverlapping_stage1_simulation_explicit
    (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u64K)
    hrel₂ hphase rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide) (by decide))
    rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 4 (by decide) (by decide))
    WitnessLM4_2.usize_integral hcount₂ WitnessLM4_2.u64_copyPointee (by decide)
    (by
      intro _ _ countSc _ _ hc hc0
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      subst hc'; cases hc0)
    (by
      intro _ _ e_s e_d decl_s decl_d _ _ he_s _ he_d _ hd_s hd_d
      obtain ⟨rfl, hun_s⟩ : decl_s = WitnessLM4_2.declOf WitnessLM4_2.u64K ∧
          unionLocalByteSize? b.localDecls b.layouts e_s.localIdx = none := by
        rcases List.mem_cons.mp he_s with rfl | he'
        · exact ⟨Option.some.inj hd_s.symm, rfl⟩
        · rcases List.mem_cons.mp he' with rfl | h
          · exact ⟨Option.some.inj hd_s.symm, rfl⟩
          · cases h
      obtain ⟨rfl, hun_d⟩ : decl_d = WitnessLM4_2.declOf WitnessLM4_2.u64K ∧
          unionLocalByteSize? b.localDecls b.layouts e_d.localIdx = none := by
        rcases List.mem_cons.mp he_d with rfl | he'
        · exact ⟨Option.some.inj hd_d.symm, rfl⟩
        · rcases List.mem_cons.mp he' with rfl | h
          · exact ⟨Option.some.inj hd_d.symm, rfl⟩
          · cases h
      exact ⟨rfl, rfl, hun_s, hun_d⟩)
    (by
      intro srcPtr dstPtr countSc hsrc hdst hc _
      have hpS : srcPtr = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₂, WitnessLM4_2.mkPtrState, ptr1, get?] using hsrc.symm
      have hpD : dstPtr = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₂, WitnessLM4_2.mkPtrState, ptr2, get?] using hdst.symm
      have hc' : countSc = ⟨1, 8⟩ := by
        rcases hc with ⟨cc, hcc, hval⟩ | ⟨_, hidx, _⟩
        · injection hcc with hcc'; subst hcc'; simpa [WitnessLM4_2.constInt] using hval.symm
        · cases hidx
      subst hpS hpD hc'; exact ⟨rfl, rfl, rfl⟩)
    (by
      intro srcPtr dstPtr _ e_s e_d hsrc hdst _ _ he_s het_s he_d het_d _ _
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
        by simp [s₂, WitnessLM4_2.mkPtrState, e₁, rawPtrAllocMapEntry, get?]⟩)
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
  let s₄ := WitnessLM4_2.mkPtrState b 1 4
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
    (hchar_dst : dstDecl.ty.kind = .char → sc0.sizeBytes = 4 ∧ isValidCharCode sc0.bits = true)
    (hnu : placeTouchesUnion body.localDecls body.layouts
      ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩ = false := by rfl)
    (hvalid : validateLoadedValue body.layouts body.localDecls
      (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩) (.scalar sc0) = true := by rfl) :
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
      have h_ld : evalOperand s.frame.locals (.copy ⟨p, [.field 0 { kind := t0, layoutIdx := 0 }]⟩)
          [] s.memory.globals body.layouts [] body.localDecls = .ok (.scalar sc0) s.frame.locals := by
        have h0 := h_a'
        unfold evalOperand at h0 ⊢
        dsimp only at h0 ⊢
        rw [hls] at h0 ⊢
        dsimp only at h0 ⊢
        rw [hnu]
        exact h0
      unfold evalRvalue
      dsimp only
      rw [hbor, hcaller, h_ld]
      dsimp only
      rw [hvalid]
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

/-- **`arith_offset` returns from entry** (`LM-4.2`, `arithOffsetPosEntryBody`):
`StorageLive(_1.._3); _1 = 42_u64; goto bb1; bb1: _2 = &raw mut _1;
_0 = arith_offset(copy _2, 5_isize) -> bb2; bb2: return` runs in both machines from
`initMachineState` / `miriEntryState` to a normal root return of the raw pointer `40`
bytes past `_1` (`step_terminator_return_rawPtr_lm3_1_simulation`), with
`ImmediateRelLM3_1`-related return values. -/
theorem w3_arith_offset_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns arithOffsetPosEntryBody (annealMiriHooks arithOffsetPosEntryBody)
        (initMachineState arithOffsetPosEntryBody [])
        (miriEntryState arithOffsetPosEntryBody)
        (.ptr { allocId := 1, offsetBytes := 40 } 8) (.immediate imm0) ∧
      get? arithOffsetPosEntryBody.localDecls 0 = some decl0 ∧
      ImmediateRelLM3_1
        [rawPtrAllocMapEntry arithOffsetPosEntryBody.localDecls
          arithOffsetPosEntryBody.layouts .mut 1 1 Witness.lm31AllocId1]
        decl0.ty arithOffsetPosEntryBody.layouts
        (.ptr { allocId := 1, offsetBytes := 40 } 8) imm0 := by
  obtain ⟨s₁, s₂, m₁, m₂, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, _, hret, hmret, hdecl0, hop,
    himm⟩ := retArithOffset_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths (p := 5) rfl rfl
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hmret)
      (.refl _)))
    hmret rfl (by change (annealControlHooks.returnOperand () m₂).2 = _; rw [hop])

/-- **Stage-1 external-call divergence, whole program from entry**
(`retWriteBytesReadBody`): `StorageLive(_1.._3); _1 = const 42_u64; goto bb1;
bb1: _2 = &raw mut _1; _3 = write_bytes::<u64>(copy _2, 0xAB, 1) -> bb2;
bb2: _0 = copy (*_2); return`, run from `initMachineState` / `miriEntryState`.

* `lean-miri` fills `_1` with `0xAB` bytes through the raw pointer, reads them back
  through it, and its whole program is `System.Safe`, returns
  `0xABABABABABABABAB_u64` (`ImmediateRel`), and is partially correct only for that
  value (`retWriteBytesRead_prefix_miri`, then `retWriteBytesRead_ref_trace`, in
  lockstep with the pre-Stage-1 reference model).
* Stage-1 `stepMirFn` hands `write_bytes` to the environment, and an environment
  response cannot write Anneal's stack locals (`resumeExternalCall` keeps the
  caller's locals): when the environment returns `()` without touching memory,
  Anneal's whole program returns the unchanged `42_u64`; when it unwinds, the
  call's `UnwindAction::Unreachable` is undefined behavior, so Anneal is not
  `TreeSafe` although `lean-miri` is `System.Safe`. -/
theorem w6_write_bytes_read_extCall_divergence :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      (miriSystem (annealMiriHooks retWriteBytesReadBody)).Safe
        (miriEntryState retWriteBytesReadBody) ∧
      (miriSystem (annealMiriHooks retWriteBytesReadBody)).ReachesOutcome
        (miriEntryState retWriteBytesReadBody) (.returned (.immediate imm0)) ∧
      (miriSystem (annealMiriHooks retWriteBytesReadBody)).PartialCorrect
        (miriEntryState retWriteBytesReadBody) (· = .immediate imm0) ∧
      get? retWriteBytesReadBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retWriteBytesReadBody.layouts (.scalar ⟨0xABABABABABABABAB, 8⟩) imm0 ∧
      (∃ tr mem, ReachesRet (mirCallTree retWriteBytesReadBody []) tr
        (.normal (.scalar ⟨42, 8⟩, mem))) ∧
      MirReachesUB (mirCallTree retWriteBytesReadBody []) ∧
      ¬ TreeSafe (mirCallTree retWriteBytesReadBody []) := by
  obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, _, _, hext, hm₂, _, _, _, hm₃, _, _, _,
    hmret, hdecl0, hop, himm⟩ := retWriteBytesRead_ref_trace
  -- `lean-miri`: the entry block, then the traced run to the root pop.
  have hpath : MiriPath (annealMiriHooks retWriteBytesReadBody)
      (miriEntryState retWriteBytesReadBody) m₃ :=
    (MiriPath.of_runLoopFuel retWriteBytesRead_prefix_miri).trans
      (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hmret) (.refl _))))
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_path_return hpath hmret rfl
    (by change (annealControlHooks.returnOperand () m₃).2 = _; rw [hop])
  -- Anneal: the entry block, the `&raw mut` step, the external call, and the read
  -- of the unchanged `_1`.
  let entry := rawPtrAllocMapEntry retWriteBytesReadBody.localDecls retWriteBytesReadBody.layouts
    .mut 1 1 Witness.lm31AllocId1
  have hs₁' : stepMirFn retWriteBytesReadBody retWriteBytesReadPreAnneal =
      .step (WitnessLM4_2.mkPtrState retWriteBytesReadBody 1 1
        [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
          .uninit]
        [entry.toBorrowEntry] 2) := rfl
  have hs_eq : s₁ = WitnessLM4_2.mkPtrState retWriteBytesReadBody 1 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
        .uninit]
      [entry.toBorrowEntry] 2 := by
    have h := hs₁.symm.trans hs₁'
    unfold MirStepNode.step at h
    injection h with h
    injection h
  subst hs_eq
  let sᵣ := WitnessLM4_2.mkPtrState retWriteBytesReadBody 2 0
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init .unit]
    [entry.toBorrowEntry] 2
  let sₖ := WitnessLM4_2.mkPtrState retWriteBytesReadBody 2 1
    [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init .unit]
    [entry.toBorrowEntry] 2
  have hk : stepMirFn retWriteBytesReadBody sᵣ = .step sₖ := rfl
  obtain ⟨⟨tr, hrr⟩, hub, hns⟩ := anneal_extCall_boundary_of_prefix (sᵣ := sᵣ) (sₖ := sₖ)
    (retVal := .unit) (v := .scalar ⟨42, 8⟩) (mem := sᵣ.memory) (memR := sₖ.memory)
    retWriteBytesRead_prefix_anneal (.step .silent hs₁ (.refl _)) hext rfl
    (.step .silent hk (.refl _)) rfl (initMachineState retWriteBytesReadBody []).memory
  refine ⟨decl0, imm0, hsafe, hreach, fun v' hv' => ?_, hdecl0, himm, ⟨tr, _, hrr⟩, hub, hns⟩
  have := huniq _ hv'
  injection this

/-! ### Out-of-bounds `write_bytes`, from program entry -/

/-- `write_bytes::<u64>(copy _2, 0xAB_u8, 2_usize) -> bb2` into the unit local `_3`:
`16` bytes into the `8`-byte allocation of `_1` (block `bb1` of
`retWriteBytesOobBody`). -/
def retWriteBytesOobTerm : TerminatorKind :=
  .call (.constant (WitnessLM4_2.fnItem "core::intrinsics::write_bytes" WitnessLM4_2.u64K))
    [.copy (WitnessLM4_2.local42 2),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.u8K 0xAB 1),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 2 8)]
    (WitnessLM4_2.local42 3) (some 2) .unreachable

/-- `retWriteBytesReadBody` with an out-of-bounds count (no `miri-diff` corpus
program; the shape of `WitnessLM4_2.wit_lm4_2_write_bytes_oob_boundary`, run from
program entry):

```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 42_u64;
     goto -> bb1;
bb1: _2 = &raw mut _1;
     _3 = write_bytes::<u64>(copy _2, 0xAB_u8, 2_usize) -> bb2;
bb2: _0 = copy (*_2);
     return
``` -/
def retWriteBytesOobBody : CapturedMir :=
  { retWriteBytesReadBody with
    defPath := "lm_4_3_witness::ret_write_bytes_oob"
    basicBlocks := [
      { statements := [WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
          WitnessLM4_2.mkStmt42 (.storageLive 3),
          WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
            (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 42 8))))]
        terminator := WitnessLM4_2.mkTerm42 (.goto 1)
        isCleanup := false },
      { statements := [WitnessLM4_2.mkStmt42
          (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
        terminator := WitnessLM4_2.mkTerm42 retWriteBytesOobTerm
        isCleanup := false },
      { statements := [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
          (.use (.copy { local_ := 2, projection := [.deref] })))]
        terminator := WitnessLM4_2.mkTerm42 .return_
        isCleanup := false }] }

/-- Anneal's state of `retWriteBytesOobBody` after the entry block `bb0`. -/
def retWriteBytesOobPreAnneal : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState retWriteBytesOobBody []).memory }

/-- `lean-miri`'s root frame of `retWriteBytesOobBody` after the entry block `bb0`. -/
def retWriteBytesOobPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame retWriteBytesOobBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨1, 0⟩ }

/-- `lean-miri`'s state of `retWriteBytesOobBody` after the entry block `bb0`. -/
def retWriteBytesOobPreMiri : AnnealStepState :=
  { stack := ⟨#[retWriteBytesOobPreMiriFrame]⟩, machine := AnnealMachine.empty }

/-- The entry block of `retWriteBytesOobBody`, from `initMachineState`. -/
theorem retWriteBytesOob_prefix_anneal :
    runAnnealBounded retWriteBytesOobBody 5 (initMachineState retWriteBytesOobBody []) =
      .running retWriteBytesOobPreAnneal := rfl

/-- The entry block of `retWriteBytesOobBody`, from `miriEntryState`. -/
theorem retWriteBytesOob_prefix_miri :
    runLoopFuel (annealMiriHooks retWriteBytesOobBody) 5 (miriEntryState retWriteBytesOobBody) =
      .running retWriteBytesOobPreMiri := rfl

/-- The post-entry-block states of `retWriteBytesOobBody` are `StateRel`-related, and
every `lean-miri` local is immediate. -/
theorem retWriteBytesOob_stateRel :
    StateRel retWriteBytesOobBody retWriteBytesOobPreAnneal retWriteBytesOobPreMiri ∧
    ∀ tf, retWriteBytesOobPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk retWriteBytesOobPreMiriFrame rfl rfl
      ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K), rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | 3 | _ + 4 => simp [retWriteBytesOobPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 =>
      have hs : slot = .uninit := by simpa [retWriteBytesOobPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [retWriteBytesOobPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [retWriteBytesOobBody, retWriteBytesReadBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by
        simpa [retWriteBytesOobPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar42))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [retWriteBytesOobPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ Witness.lm31_scalarRel42 rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 4 => simp [retWriteBytesOobBody, retWriteBytesReadBody, get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : retWriteBytesOobPreMiriFrame = tf := by simpa [retWriteBytesOobPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 => simp [retWriteBytesOobPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 4 => simp [retWriteBytesOobPreMiriFrame] at hmls

/-- **Stage-1 external-call divergence, whole program from entry**
(`retWriteBytesOobBody`): `StorageLive(_1.._3); _1 = const 42_u64; goto bb1;
bb1: _2 = &raw mut _1; _3 = write_bytes::<u64>(copy _2, 0xAB, 2) -> bb2;
bb2: _0 = copy (*_2); return`, run from `initMachineState` / `miriEntryState`.

* `lean-miri` takes the entry block and `_2 = &raw mut _1` in lockstep with Anneal
  (`step_rawPtr_addrOf_simulation`), then reports the `16`-byte write into the
  `8`-byte allocation of `_1` as undefined behavior (in lockstep with the
  pre-Stage-1 reference model `stepMirFnLM4_2`, `call_intrinsic_write_bytes_simulation`):
  `miriSystem` reaches `.undefinedBehavior` and is not `System.Safe`.
* Stage-1 `stepMirFn` hands `write_bytes` to the environment without checking it:
  when the environment returns `()` without touching memory, Anneal's whole
  program returns the unchanged `42_u64`; when it unwinds, the call's
  `UnwindAction::Unreachable` is undefined behavior (`MirReachesUB`, not
  `TreeSafe`). (Before Stage-1, both machines reported undefined behavior at the
  call.) -/
theorem w6_write_bytes_oob_extCall_divergence :
    (∃ e, (miriSystem (annealMiriHooks retWriteBytesOobBody)).ReachesOutcome
        (miriEntryState retWriteBytesOobBody) (.undefinedBehavior e)) ∧
    ¬ (miriSystem (annealMiriHooks retWriteBytesOobBody)).Safe
        (miriEntryState retWriteBytesOobBody) ∧
    (∃ tr mem, ReachesRet (mirCallTree retWriteBytesOobBody []) tr
        (.normal (.scalar ⟨42, 8⟩, mem))) ∧
    MirReachesUB (mirCallTree retWriteBytesOobBody []) ∧
    ¬ TreeSafe (mirCallTree retWriteBytesOobBody []) := by
  let b := retWriteBytesOobBody
  obtain ⟨hrel₀, himm₀_all⟩ := retWriteBytesOob_stateRel
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, retWriteBytesOobPreMiri.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  -- Step 1: `_2 = &raw mut _1`, in lockstep.
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b retWriteBytesOobPreAnneal = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : retWriteBytesOobPreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨retWriteBytesOobPreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := Witness.step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  -- Step 2: `write_bytes::<u64>(copy _2, 0xAB_u8, 2_usize)` is out of bounds.
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := rfl
  have hvalOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.u8K 0xAB 1))
        (WitnessLM4_2.tyOf WitnessLM4_2.u8K) :=
    fun tf₁ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.u8_integral WitnessLM4_2.valid1
      (by decide) rfl b rfl tf₁
  have hcountOp : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      WellTypedScalarOperand b tf₁ (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 2 8))
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
    (fun ptrVal countSc e tgtDecl tgtKind hp hc _ _ he _ htgt ht _ hinb => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := by
        simpa [s₁, WitnessLM4_2.mkPtrState, get?] using hp.symm
      have hc' : countSc = ⟨2, 8⟩ := by
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
          exact absurd hinb (by decide))
  rw [hs₂] at hsim₂
  obtain ⟨m₂, msg, hm₂⟩ := hsim₂.miri_ub_of_anneal_ub
  -- `lean-miri`: the entry block, the `&raw mut` step, then undefined behavior.
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  have hM : MiriPath (annealMiriHooks b) (miriEntryState b) m₁ :=
    (MiriPath.of_runLoopFuel retWriteBytesOob_prefix_miri).trans
      (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _))
  have h := miri_outcome_of_path_error hM hm₂
  rw [classifyError_eq_ub_iff.2 ⟨rfl, rfl⟩] at h
  -- Anneal: the entry block, the `&raw mut` step, the external call, and the read
  -- of the unchanged `_1`.
  have hext : stepMirFn b s₁ =
      MirStepNode.extCall
        { defPath := "core::intrinsics::write_bytes", typeArgs := [WitnessLM4_2.u64K]
          args := [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨0xAB, 1⟩, .scalar ⟨2, 8⟩]
          memory := s₁.memory }
        (resumeExternalCall s₁ s₁.frame.locals (WitnessLM4_2.local42 3) 2 .unreachable) := rfl
  let sᵣ := WitnessLM4_2.mkPtrState b 2 0
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init .unit]
    [entry.toBorrowEntry] 2
  let sₖ := WitnessLM4_2.mkPtrState b 2 1
    [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init .unit]
    [entry.toBorrowEntry] 2
  have hk : stepMirFn b sᵣ = .step sₖ := rfl
  obtain ⟨⟨tr, hrr⟩, hub, hns⟩ := anneal_extCall_boundary_of_prefix (sᵣ := sᵣ) (sₖ := sₖ)
    (retVal := .unit) (v := .scalar ⟨42, 8⟩) (mem := sᵣ.memory) (memR := sₖ.memory)
    retWriteBytesOob_prefix_anneal (.step .silent hs₁ (.refl _)) hext rfl
    (.step .silent hk (.refl _)) rfl (initMachineState b []).memory
  exact ⟨⟨_, h.1⟩, h.2, ⟨tr, _, hrr⟩, hub, hns⟩

/-- **Valid `CopyNonOverlapping` returns from entry** (`pass_copy_nonoverlapping_disjoint_locals`,
`retCopyBody`): `StorageLive(_1.._4); _1 = 42_u64; _2 = 99_u64; goto bb1;
bb1: _3 = &raw const _1; _4 = &raw mut _2; copy_nonoverlapping(copy _3, copy _4, 1);
_0 = copy (*_4); return` runs from `initMachineState` / `miriEntryState` in both
machines to a normal root return of the copied `42_u64`. -/
theorem w6_copy_nonoverlapping_disjoint_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns retCopyBody (annealMiriHooks retCopyBody)
        (initMachineState retCopyBody []) (miriEntryState retCopyBody)
        (.scalar ⟨42, 8⟩) (.immediate imm0) ∧
      get? retCopyBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retCopyBody.layouts (.scalar ⟨42, 8⟩) imm0 := by
  obtain ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, _, hs₂, hm₂, _, hs₃, hm₃, _,
    _, _, hs₄, hm₄, _, hret, hmret, hdecl0, hop, himm⟩ := retCopy_trace
  refine ⟨decl0, imm0, ?_, hdecl0, himm⟩
  exact agreeReturns_of_paths retCopy_prefix_anneal retCopy_prefix_miri
    (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))) hret
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_step_ok_true hm₃)
      (.step hm₃ (frames_ne_of_step_ok_true hm₄) (.step hm₄ (frames_ne_of_step_ok_true hmret)
        (.refl _)))))
    hmret rfl (by change (annealControlHooks.returnOperand () m₄).2 = _; rw [hop])

/-- Entry-to-return MIR body for Stage-1 multi-element `copyViaBytes`:
`StorageLive(_1.._5); _1 = 0x0102030405060708_u64; _2 = 0_u64;
_3 = &raw const _1; _4 = &raw mut _2; _5 = _3 as *const u8; _6 = _4 as *mut u8;
copy_nonoverlapping::<u8>(copy _5, copy _6, 8_usize); _0 = copy (*_4); return`. -/
def retCopyFullBytesEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::ret_copy_full_bytes_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.u64K,
    WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.rawConstU64K,
    WitnessLM4_2.declOf WitnessLM4_2.rawMutU64K, WitnessLM4_2.declOf WitnessLM4_2.rawConstU8K,
    WitnessLM4_2.declOf WitnessLM4_2.rawMutU8K]
  basicBlocks := [{
    statements := [
      WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
      WitnessLM4_2.mkStmt42 (.storageLive 3), WitnessLM4_2.mkStmt42 (.storageLive 4),
      WitnessLM4_2.mkStmt42 (.storageLive 5), WitnessLM4_2.mkStmt42 (.storageLive 6),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
        (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 0x0102030405060708 8)))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
        (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 0 8)))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 3)
        (.rawPtr .not (WitnessLM4_2.local42 1))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 4)
        (.rawPtr .mut (WitnessLM4_2.local42 2))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 5)
        (.cast .ptrToPtr (.copy (WitnessLM4_2.local42 3))
          (WitnessLM4_2.tyOf WitnessLM4_2.rawConstU8K))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 6)
        (.cast .ptrToPtr (.copy (WitnessLM4_2.local42 4))
          (WitnessLM4_2.tyOf WitnessLM4_2.rawMutU8K))),
      WitnessLM4_2.copyStmt 5 6 8,
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
        (.use (.copy ⟨4, [.deref]⟩)))]
    terminator := WitnessLM4_2.mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private def retCopyFullBytesPreAnneal : MachineState :=
  WitnessLM4_2.mkPtrState retCopyFullBytesEntryBody 0 8
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .uninit, .uninit, .uninit, .uninit] [] 1

private def retCopyFullBytesPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame retCopyFullBytesEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarSrc))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarZero))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨0, 8⟩ }

private def retCopyFullBytesPreMiri : AnnealStepState :=
  { stack := ⟨#[retCopyFullBytesPreMiriFrame]⟩, machine := AnnealMachine.empty }

private theorem retCopyFullBytes_prefix_anneal :
    runAnnealBounded retCopyFullBytesEntryBody 8
      (initMachineState retCopyFullBytesEntryBody []) =
      .running retCopyFullBytesPreAnneal := rfl

private theorem retCopyFullBytes_prefix_miri :
    runLoopFuel (annealMiriHooks retCopyFullBytesEntryBody) 8
      (miriEntryState retCopyFullBytesEntryBody) =
      .running retCopyFullBytesPreMiri := rfl

/-- **Stage-1 multi-element `copyViaBytes` lockstep return from entry**
(`retCopyFullBytesEntryBody`): from `initMachineState` / `miriEntryState`, both
machines copy all `8` bytes of `_1 = 0x0102030405060708_u64` into `_2 : u64` as
`copy_nonoverlapping::<u8>(..., 8_usize)` (`step_intrinsic_copyNonOverlapping_stage1_full_bytes_distinct_int_simulation`),
read `0x0102030405060708_u64` back through `*_4`, and return it in lockstep (`AgreeReturns`). -/
theorem w6_copy_nonoverlapping_full_bytes_returns :
    ∃ (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      AgreeReturns retCopyFullBytesEntryBody (annealMiriHooks retCopyFullBytesEntryBody)
        (initMachineState retCopyFullBytesEntryBody [])
        (miriEntryState retCopyFullBytesEntryBody)
        (.scalar ⟨0x0102030405060708, 8⟩) (.immediate imm0) ∧
      get? retCopyFullBytesEntryBody.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty retCopyFullBytesEntryBody.layouts
        (.scalar ⟨0x0102030405060708, 8⟩) imm0 := by
  let b := retCopyFullBytesEntryBody
  have hpa := retCopyFullBytes_prefix_anneal
  have hpm := retCopyFullBytes_prefix_miri
  have hrel₀ : StateRel b retCopyFullBytesPreAnneal retCopyFullBytesPreMiri := by
    refine StateRel.mk retCopyFullBytesPreMiriFrame rfl rfl
      ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K), rfl⟩ ?_
      rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 =>
          simp [retCopyFullBytesPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 3 | 4 | 5 | 6 =>
      have hs : slot = .uninit := by
        simpa [retCopyFullBytesPreAnneal, WitnessLM4_2.mkPtrState, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [retCopyFullBytesPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [b, retCopyFullBytesEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0x0102030405060708, 8⟩) := by
        simpa [retCopyFullBytesPreAnneal, WitnessLM4_2.mkPtrState, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarSrc))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [retCopyFullBytesPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ WitnessLM4_2.lm42_scalarRelSrc rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | 2 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [b, retCopyFullBytesEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0, 8⟩) := by
        simpa [retCopyFullBytesPreAnneal, WitnessLM4_2.mkPtrState, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarZero))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [retCopyFullBytesPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ WitnessLM4_2.lm42_scalarRelZero rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 7 => simp [b, retCopyFullBytesEntryBody, get?] at hdecl
  have himm₀ : ∀ tf, retCopyFullBytesPreMiri.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hv
    have htf : retCopyFullBytesPreMiriFrame = tf := by simpa [retCopyFullBytesPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
      simp [retCopyFullBytesPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 7 => simp [retCopyFullBytesPreMiriFrame] at hmls
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  let s₁ := WitnessLM4_2.mkPtrState b 0 9
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr1, .uninit, .uninit, .uninit] [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b retCopyFullBytesPreAnneal = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 3, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty).step_of_anneal_step hs₁
  have htag₀ : retCopyFullBytesPreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨retCopyFullBytesPreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 3, himm₀ tf htf 1⟩)
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀ _ rfl k)
  let s₂ := WitnessLM4_2.mkPtrState b 0 10
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr1, .init ptr2, .uninit, .uninit] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  obtain ⟨m₂, hm₂, hrel₂⟩ := (step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁).step_of_anneal_step hs₂
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      Witness.lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz; revert nz; rw [hnext₁]; intro _; rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨_, himm₂_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₁
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
    (by rw [hnext₁]; show (1 + 1 : UInt32).toNat + 1 < 2 ^ 32; decide)
    (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k h1 h2; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k h2 (himm₁ tf₁ htf₁ k h1)
  let s₃ := WitnessLM4_2.mkPtrState b 0 11
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr1, .init ptr2, .init ptr1, .uninit] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  obtain ⟨m₃, hm₃, hrel₃⟩ := (step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 5 (by decide) (by decide),
      himm₂ tf₂ htf₂ 3 (by decide) (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₃
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k h1 h2; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k h1 h2)
  let s₄ := WitnessLM4_2.mkPtrState b 0 12
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr1, .init ptr2, .init ptr1, .init ptr2] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 6 (by decide) (by decide),
      himm₃ tf₃ htf₃ 4 (by decide) (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar_mdw)).step_of_anneal_step hs₄
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k h1 h2; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k h1 h2)
  let s₅ := WitnessLM4_2.mkPtrState b 0 13
    [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩),
     .init (.scalar ⟨0x0102030405060708, 8⟩),
     .init ptr1, .init ptr2, .init ptr1, .init ptr2] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  have hcount₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] →
      WellTypedScalarOperand b tf₄ (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 8 8))
        (WitnessLM4_2.tyOf WitnessLM4_2.usizeK) :=
    fun tf₄ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₄
  have hsim₅ := step_intrinsic_copyNonOverlapping_stage1_full_bytes_distinct_int_simulation
    (pointeeTy := WitnessLM4_2.tyOf WitnessLM4_2.u8K)
    (e_s := e₁) (e_d := e₂)
    (decl_s := WitnessLM4_2.declOf WitnessLM4_2.u64K)
    (decl_d := WitnessLM4_2.declOf WitnessLM4_2.u64K)
    (srcKind := .u64) (dstKind := .u64)
    hrel₄ hphase rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩)))
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 5 (by decide) (by decide))
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 6 (by decide) (by decide))
    WitnessLM4_2.usize_integral hcount₄
    (⟨⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩ :
      CopyPointee b.layouts (WitnessLM4_2.tyOf WitnessLM4_2.u8K).kind _ 1 1)
    rfl rfl rfl rfl
    (Or.inl ⟨_, rfl, rfl⟩) (by decide)
    (.tail _ (.head _)) rfl (.head _) rfl
    (by nofun) (Or.inl rfl) (by decide) rfl rfl
    rfl rfl rfl (.uint .u64 rfl) rfl (.uint .u64 rfl)
    rfl rfl rfl (by decide)
  rw [hs₅] at hsim₅
  have hmap_eq : copyNextAllocMap s₄.frame.locals [e₂, e₁] 6
      (.constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK 8 8)) 1 = [e₂, e₁] := rfl
  rw [hmap_eq] at hsim₅
  obtain ⟨m₅, hm₅, hrel₅⟩ := hsim₅.step_of_anneal_step rfl
  have himm₅ : ∀ tf₅, m₅.stack.frames = #[tf₅] → ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₅ k := by
    intro tf₅ htf₅ k h1 h2
    obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
    exact retCopy_copyStep_preserves_imm hrel₄ (srcIdx := 5) (dstIdx := 6) rfl rfl rfl rfl
      (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 5 (by decide) (by decide)) rfl rfl
      (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 6 (by decide) (by decide))
      hcount₄ WitnessLM4_2.usize_integral.prim hm₅ tf₄ tf₅ htf₄ htf₅ k
      (himm₄ tf₄ htf₄ k h1 h2)
  let s₆ := WitnessLM4_2.mkPtrState b 0 14
    [.init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0x0102030405060708, 8⟩),
     .init (.scalar ⟨0x0102030405060708, 8⟩),
     .init ptr1, .init ptr2, .init ptr1, .init ptr2] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₆ : stepMirFn b s₅ = .step s₆ := rfl
  have hsim₆ := step_deref_read_simulation_explicit hrel₅ hphase
    (opKind := MirAst.Operand.copy) (Or.inl rfl) rfl (dstIdx := 0) (ptrIdx := 4) rfl rfl rfl rfl
    WitnessLM4_2.u64_integral.prim
    (fun tf₅ htf₅ => ⟨himm₅ tf₅ htf₅ 0 (by decide) (by decide),
      himm₅ tf₅ htf₅ 4 (by decide) (by decide)⟩)
    (by
      intro ptrVal hptr e he het _
      have hp : ptrVal = { allocId := 2, offsetBytes := 0 } := by
        simpa [s₅, WitnessLM4_2.mkPtrState, ptr2, get?] using hptr.symm
      subst hp
      have hed : e = e₂ := by
        rcases List.mem_cons.mp he with rfl | he'
        · rfl
        · rcases List.mem_cons.mp he' with rfl | h
          · cases het
          · cases h
      subst hed
      refine ⟨rfl, by nofun, fun decl hdecl => ?_⟩
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := Option.some.inj hdecl.symm
      subst hd
      rfl)
  rw [hs₆] at hsim₆
  have hmap6_eq : derefReadNextAllocMap s₅.frame.locals [e₂, e₁] 4 = [e₂, e₁] := rfl
  rw [hmap6_eq] at hsim₆
  obtain ⟨m₆, hm₆, hrel₆⟩ := hsim₆.miri_step_of_anneal_step
  obtain ⟨_, himm₆_step⟩ := Witness.step_assign_use_preserves hrel₅ (by rintro _ ⟨⟩) rfl rfl hm₆
  have himm₆_0 : ∀ tf₆, m₆.stack.frames = #[tf₆] → IsImmediateFrameLocal tf₆ 0 := by
    intro tf₆ htf₆; obtain ⟨tf₅, htf₅, _⟩ := id hrel₅
    exact himm₆_step tf₅ tf₆ htf₅ htf₆ 0 (himm₅ tf₅ htf₅ 0 (by decide) (by decide))
  have hs₇ : stepMirFn b s₆ = .retNormal (.scalar ⟨0x0102030405060708, 8⟩) s₆.memory := rfl
  have hsim₇ := step_terminator_goto_return_lm3_1_simulation hrel₆ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, WitnessLM4_2.declOf WitnessLM4_2.u64K, rfl,
      (by rintro _ _ ⟨⟩), (by decide), himm₆_0⟩))
  rw [hs₇] at hsim₇
  generalize hm₇_eq : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₆ =
    mRes₇ at hsim₇
  cases hsim₇ with
  | retRoot decl0 _ imm0 _ m₇ hdecl0 hop0 himm0 hm₇ =>
    refine ⟨decl0, imm0, ?_, hdecl0, himm0⟩
    exact agreeReturns_of_paths hpa hpm
      (.step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄
        (.step .silent hs₅ (.step .silent hs₆ (.refl _))))))) hs₇
      (.step hm₁ (frames_ne_of_step_ok_true hm₂)
        (.step hm₂ (frames_ne_of_step_ok_true hm₃)
          (.step hm₃ (frames_ne_of_step_ok_true hm₄)
            (.step hm₄ (frames_ne_of_step_ok_true hm₅)
              (.step hm₅ (frames_ne_of_step_ok_true hm₆)
                (.step hm₆ (frames_ne_of_step_ok_true hm₇_eq) (.refl _)))))))
      hm₇_eq (by rw [hm₇]) (by change (annealControlHooks.returnOperand () m₆).2 = _; rw [hop0])

/-- Entry-to-return MIR body where Stage-1 `stepMirFn` copies a provenance-carrying
raw pointer (`&raw const _1`) across `copy_nonoverlapping::<*const u64>` into `_5`,
dereferences `*_5`, and returns `42_u64` from `initMachineState`. -/
def copyRawPtrDerefEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::copy_rawptr_deref_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf WitnessLM4_2.u64K, WitnessLM4_2.declOf WitnessLM4_2.u64K,
    WitnessLM4_2.declOf WitnessLM4_2.rawConstU64K,
    WitnessLM4_2.declOf (.rawPtr .not WitnessLM4_2.rawConstU64K),
    WitnessLM4_2.declOf (.rawPtr .mut WitnessLM4_2.rawConstU64K),
    WitnessLM4_2.declOf WitnessLM4_2.rawConstU64K]
  basicBlocks := [{
    statements := [
      WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
      WitnessLM4_2.mkStmt42 (.storageLive 3), WitnessLM4_2.mkStmt42 (.storageLive 4),
      WitnessLM4_2.mkStmt42 (.storageLive 5),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
        (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 42 8)))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
        (.rawPtr .not (WitnessLM4_2.local42 1))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 3)
        (.rawPtr .not (WitnessLM4_2.local42 2))),
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 4)
        (.rawPtr .mut (WitnessLM4_2.local42 5))),
      WitnessLM4_2.copyStmt 3 4 1,
      WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0)
        (.use (.copy (Witness.derefLocal 5))))]
    terminator := WitnessLM4_2.mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **Stage-1 provenance-preserving pointer `CopyNonOverlapping` vs. `lean-miri`'s
`TyId 80` encoding boundary**:
* From `initMachineState copyRawPtrDerefEntryBody []`, Stage-1 `stepMirFn`
  copies the provenance-carrying pointer `&raw const _1` across
  `copy_nonoverlapping::<*const u64>` into `_5`, dereferences `*_5`, is `TreeSafe`,
  and returns `42_u64`.
* On `WitnessLM4_2.copyStage1RawPtrCastLockstepBody`, both machines run in
  `StateRelLM3_1` lockstep (`AgreeReaches`) through the 4 setup steps to `(s₄, m₄)`
  where `_4` and `_5` are initialized pointer-to-pointer values; Stage-1 `mirTree`
  is `TreeSafe` and returns `.ptr ⟨1, 0⟩ 8`, whereas `lean-miri` stops at
  `StepError.unsupported "pointee of TyId 80 is not encoded"`
  (`WitnessLM4_2.wit_lm4_2_copy_nonoverlapping_rawPtr_cast_lockstep_boundary`). -/
theorem w6_copy_nonoverlapping_rawPtr_tyId80_boundary :
    (TreeSafe (mirCallTree copyRawPtrDerefEntryBody []) ∧
      ∃ tr mem, ReachesRet (mirCallTree copyRawPtrDerefEntryBody []) tr
        (.normal (.scalar ⟨42, 8⟩, mem))) ∧
    (let b := WitnessLM4_2.copyStage1RawPtrCastLockstepBody
     let s₀ := WitnessLM4_2.partialCopyLockstepAnnealPre b 0
     let m₀ := WitnessLM4_2.partialCopyLockstepMiriPre b WitnessLM4_2.lm42ScalarZero
     ∃ s₄ m₄,
       AgreeReaches b (annealMiriHooks b) s₀ s₄ m₀ m₄ ∧
       get? s₄.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
       get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
       TreeSafe (mirTree b s₀) ∧
       (∃ tr mem, ReachesRet (mirTree b s₀) tr
         (.normal (.ptr { allocId := 1, offsetBytes := 0 } 8, mem))) ∧
       (miriSystem (annealMiriHooks b)).ReachesOutcome m₀
         (.unsupported (.unsupported "pointee of TyId 80 is not encoded")) ∧
       ¬ (miriSystem (annealMiriHooks b)).Safe m₀) := by
  refine ⟨anneal_returns_of_bits (N := 12) rfl, ?_⟩
  let b := WitnessLM4_2.copyStage1RawPtrCastLockstepBody
  let s₀ := WitnessLM4_2.partialCopyLockstepAnnealPre b 0
  let m₀ := WitnessLM4_2.partialCopyLockstepMiriPre b WitnessLM4_2.lm42ScalarZero
  obtain ⟨s₁, s₂, s₃, s₄, _, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, _, hs₂, hm₂, _, hs₃, hm₃, _, hs₄, hm₄, hrel₄, hl4, hl5, _, _, hm₅⟩ :=
    WitnessLM4_2.wit_lm4_2_copy_nonoverlapping_rawPtr_cast_lockstep_boundary
  obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
  have hpathA : AnnealPath b s₀ s₄ :=
    .step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))
  have hpathM : MiriPath (annealMiriHooks b) m₀ m₄ :=
    .step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_eq_singleton htf₄) (.refl _))))
  have ⟨memA, hretA⟩ : ∃ mem, runAnnealBounded b 6 s₀ =
      .returned (.ptr { allocId := 1, offsetBytes := 0 } 8) mem := ⟨_, rfl⟩
  obtain ⟨hsafeA, ⟨trA, hrrA⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned hretA
  have houtM := miri_outcome_of_path_error hpathM hm₅
  exact ⟨s₄, m₄, agreeReaches_of_paths hpathA hpathM, hl4, hl5, hsafeA, ⟨trA, memA, hrrA⟩,
    houtM.1, houtM.2⟩

/-! ### W1: `checkedAdd` equivalence

We show safety equivalence and UB-reachability equivalence of `checkedAddBody rhs` (which the
syntactic fragment excludes because it projects the `(u16, bool)` pair). -/
theorem w1_checked_add_treeSafe_iff_miriSafe (rhs : Nat) (hrhs : rhs < 65536) :
    (TreeSafe (mirCallTree (checkedAddBody rhs) []) ↔
      (miriSystem (annealMiriHooks (checkedAddBody rhs))).Safe (miriEntryState (checkedAddBody rhs))) ∧
    (MirReachesUB (mirCallTree (checkedAddBody rhs) []) ↔
      ∃ e, (miriSystem (annealMiriHooks (checkedAddBody rhs))).ReachesOutcome
        (miriEntryState (checkedAddBody rhs)) (.undefinedBehavior e)) :=
  ⟨checkedAdd_treeSafe_iff_miriSafe rhs hrhs, checkedAdd_reachesUB_iff rhs hrhs⟩


end LeanMiriSpec.Correspondence.MiriDiffWitnesses
