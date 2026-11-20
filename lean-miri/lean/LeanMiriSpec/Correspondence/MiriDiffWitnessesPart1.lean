/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
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
   raw pointer, from entry), `w3_use_after_storageDead_ub`, the from-entry null
   `*ptr` agreements `w3_deref_null_ptr_read_ub` (`ub_deref_null_ptr_read`) and
   `w3_deref_null_ptr_write_ub` (`ub_deref_null_ptr_write`), undefined behavior
   in both machines as before Stage-1, `w3_arith_offset_returns` (a returned
   Stage-1 `arith_offset` pointer, from entry), `w3_arith_offset_uninit_ub` (from
   entry), and the from-entry Stage-1 upgrades `w3_rawPtr_deref_null_reborrow_returns`
   (RFC 2582 `&raw const (*ptr::null())`, which pre-Stage-1 Anneal rejected with
   undefined behavior, `step_rawPtr_deref_null_divergence`), `w3_deref_oob_ub`
   (`ub_ptr_offset_oob_read` with `BinOp.Offset` stride `8`), `w3_deref_oob_write_ub`
   (`ub_ptr_offset_oob_write`), `w3_deref_misaligned_ub` (`ub_unaligned_ptr_read_u32`),
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
   from-entry Stage-1 upgrades `w4_reborrow_dangling_safeRef_ub` (reborrowing a
   dangling `&u64` after `StorageDead` is undefined behavior in both machines) and
   `w4_invalid_bool_ref_read_ub` (an invalid `bool` read through `&bool` is
   undefined behavior in both machines), and the boundary witness
   `w4_disabled_read_divergence` (from entry, a read through a `Disabled`
   reference is undefined behavior in Anneal, while `lean-miri`'s whole program,
   which does not check Tree Borrows permissions, is `System.Safe` and returns
   the read value).
5. Multi-frame calls and stack unwinding: `w5_call_return` (from entry, modeled on
   the former `known_anneal_bug` ratchet `pass_direct_fn_call`),
   `w5_protector_release_returns` (`GlobalState.endCall` releasing a live
   protector on the way to an agreeing root return), `w5_callee_unreachable_ub`,
   `w5_callee_uninit_return_ub` (both from entry), and the from-entry Stage-1 upgrades
   `w5_unwind_cleanup_returns` (3-frame `UnwindResume` caught at a caller
   cleanup pad), `w5_unwind_unreachable_ub` (multi-frame `UnwindResume` hitting
   `UnwindAction::Unreachable` UB), `w5_unwind_root_panic_vs_ub_divergence`
   (multi-frame `UnwindResume` unwinding past the root frame: `TreeSafe` `.panic`
   in Anneal vs. undefined behavior in `lean-miri`),
   `w5_indirect_fnPtr_call_returns` (`ReifyFnPointer` coercion and indirect
   `FnPtr` call), and `w5_panic_explicit_macro_extCall_boundary` (the open
   `known_anneal_bug` ratchet `panic_explicit_macro`, from entry: Stage-1 stops at
   `MirStepNode.extCall` for `core::fmt::Arguments::<'a>::from_str` and, when the
   environment returns, panics in `core::panicking::panic_fmt`, while `lean-miri`
   reports `.unsupported`).
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
   (from entry; `.unsupported` in `lean-miri`); and, from program entry, the
   inline `write_bytes` agreements (Stage-1 executes `write_bytes` inline since
   `ws-repatriate-leaked-ground-semantics-to-tcb`): `w6_write_bytes_inline_lockstep`
   (both machines fill `_1` with the written bytes; Anneal returns `()`),
   `w6_write_bytes_read_returns` (both return the written bytes) and
   `w6_write_bytes_oob_ub` (undefined behavior in both).

Every other witness runs from program entry (`initMachineState` /
`initMachineStateWithCallees` and `miriEntryState`) except `w2_enum_downcast_switch_returns`,
`w2_union_uninit_bytes_ub`, `w2_union_init_prefix_lockstep`,
`w4_child_write_then_parent_read_returns`, `w4_unsafe_cell_vs_freeze`,
`w4_protected_reservedFrz_conflict_ub`, `w4_storage_dead_protected_ub`,
`w5_protector_release_returns`, and `w6_copy_nonoverlapping_disjoint_lockstep`, which
start at the pre-states of the `Wit*` modules named in their statements; none of
these is a divergence witness of the `Safety.lean` ledger, whose `MiriDiffWitnesses`
entries all run from program entry.

`AgreeReturns` / `AgreeReturnsBits` (both machines `TreeSafe` / `System.Safe`
and returning the same value), `AgreeUB` (both reach undefined behavior and
neither is safe), and `AgreeReaches` (both run in lockstep to related states)
bundle the agreeing whole-program facts. Executions without memory allocation
are checked by kernel evaluation (`decide`, `kernel_decide`) of `runLoopFuel`
and `runAnnealBounded`; executions that allocate reuse the step-by-step traces
of the `LM-2` … `LM-4.2` witness modules through `MiriPath` / `AnnealPath`.
The `*_lockstep` witnesses reuse upstream bodies that never write `_0`; they
certify the lockstep segment (`AgreeReaches`) and state that Anneal's whole
program then faults at the root return. Stage-1 external calls are followed
through `coStep_of_extCall` for an explicit environment response
(`MirCallAns`), after a running prefix from program entry
(`anneal_extCall_boundary_of_prefix`); since a response carries a whole `Memory`,
an unwinding response may also carry a caller frame the program never pushed
(`anneal_extCall_continue_unwind_ub`). The `write_bytes` runs of `lean-miri` are
certified against the pre-Stage-1 reference model `stepMirFnLM4_2`
(`retWriteBytesRead_ref_trace`, `w6_write_bytes_oob_ub`), which executes the
intrinsic inline like `lean-miri`. Witnesses without a corpus program
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

/-- `agreeReaches_of_paths` after running `runAnnealBounded` / `runLoopFuel`
prefixes from the entry states (e.g. `initMachineState body []` /
`miriEntryState body`). -/
theorem agreeReaches_of_prefix_paths {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sA : MachineState} {entryM preM mB : AnnealStepState} {p : Nat}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sA) (hM : MiriPath H preM mB) :
    AgreeReaches body H entryA sA entryM mB :=
  ⟨reaches_cofix_of_coReach ((coReach_of_runAnnealBounded_running hpa).trans hA.coReach),
    ((MiriPath.of_runLoopFuel hpm).trans hM).reaches⟩

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

/-- **Unwinding through an environment-chosen `callStack`**: a `MirCallAns.panicked`
answer carries a whole `Memory`, and for an external call with
`UnwindAction::Continue`, `applyUnwindAction` unwinds through that memory's
`callStack` (`unwindFromCallStack`). So when Anneal reaches (`AnnealPath`) such a
call, the answer whose `callStack` starts with a caller frame with
`UnwindAction::Unreachable` (a frame the program never pushed) faults, and Anneal's
whole program reaches undefined behavior and is not `TreeSafe`, whatever the
program does after the call. -/
theorem anneal_extCall_continue_unwind_ub {body : CapturedMir} {s sₙ : MachineState}
    {req : MirCallReq} {locals : List LocalSlot} {dest : Place} {targetBb : BasicBlockIdx}
    (hA : AnnealPath body s sₙ)
    (hs : stepMirFn body sₙ =
      MirStepNode.extCall req (resumeExternalCall sₙ locals dest targetBb .continue_))
    {memP : Memory} {caller : SavedCallerFrame} {rest : List SavedCallerFrame}
    (hstack : memP.callStack = caller :: rest) (hcaller : caller.returnUnwind = .unreachable) :
    MirReachesUB (mirTree body s) ∧ ¬ TreeSafe (mirTree body s) := by
  have hp := hA.coReach.tail (coStep_of_extCall hs (.panicked memP))
  have hub : resumeExternalCall sₙ locals dest targetBb .continue_ (.panicked memP) =
      .faulted .ub := by
    simp only [resumeExternalCall, applyUnwindAction, hstack, unwindFromCallStack, hcaller]
  rw [hub] at hp
  exact anneal_ub_of_coReach hp rfl

local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

local elab "kernel_decide" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let inst ← Lean.Meta.synthInstance (Lean.mkApp (Lean.mkConst ``Decidable) tgt)
  let decExpr := Lean.mkApp2 (Lean.mkConst ``decide) tgt inst
  let eqProof := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) decExpr
  mvarId.assign (Lean.mkApp3 (Lean.mkConst ``of_decide_eq_true) tgt inst eqProof)
  Lean.Elab.Tactic.replaceMainGoal []

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
  agreeReturnsBits_of_obs (N := 6) (M := 6) (by kernel_decide) (by kernel_decide)

/-- Division by zero is undefined behavior in both machines. -/
theorem w1_div_by_zero_ub :
    AgreeUB (Witness.divBody 0) (annealMiriHooks (Witness.divBody 0))
      (initMachineState (Witness.divBody 0) []) (miriEntryState (Witness.divBody 0)) :=
  agreeUB_of_obs (N := 6) (M := 6) (by kernel_decide) (by kernel_decide)

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
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

/-- `SwitchInt` falls back to `otherwise` (returning `30`) in both machines. -/
theorem w1_switch_otherwise :
    AgreeReturnsBits (Witness.lm12SwitchBody 9) (annealMiriHooks (Witness.lm12SwitchBody 9))
      (initMachineState (Witness.lm12SwitchBody 9) []) (miriEntryState (Witness.lm12SwitchBody 9))
      1 30 :=
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

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
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by kernel_decide) (by kernel_decide)

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
  agreeReturnsBits_of_obs (N := 7) (M := 7) (by kernel_decide) (by kernel_decide)

/-- On overflow (`65500 + 36`), the failed assertion with `unwind: unreachable`
is undefined behavior in both machines. -/
theorem w1_checked_add_overflow_ub :
    AgreeUB (checkedAddBody 36) (annealMiriHooks (checkedAddBody 36))
      (initMachineState (checkedAddBody 36) []) (miriEntryState (checkedAddBody 36)) :=
  agreeUB_of_obs (N := 7) (M := 7) (by kernel_decide) (by kernel_decide)

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
  ⟨agreeReturnsBits_of_obs (N := 24) (M := 24) (by kernel_decide) (by kernel_decide),
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
      .stopped (miriEntryState storageDeadZeroBody) (.stack .cannotMakeReturnPlaceDead) := by kernel_rfl
  have hm := miri_outcome_of_runLoopFuel_stopped h
  exact ⟨hm.1, hm.2, anneal_ub_of_obs (body := storageDeadZeroBody) (N := 3)
    (s := initMachineState storageDeadZeroBody []) (by kernel_decide)⟩

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
      .faulted .ub := by kernel_rfl
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
    (s := initMachineState (transmuteBoolBody 1) []) (sz := 1) (b := 1) (by kernel_decide)
  have hm1 := miri_unsupported_of_obs (H := annealMiriHooks (transmuteBoolBody 1)) (N := 1)
    (m := miriEntryState (transmuteBoolBody 1)) (by kernel_decide)
  have ha2 := anneal_ub_of_obs (body := transmuteBoolBody 2) (N := 2)
    (s := initMachineState (transmuteBoolBody 2) []) (by kernel_decide)
  have hm2 := miri_unsupported_of_obs (H := annealMiriHooks (transmuteBoolBody 2)) (N := 1)
    (m := miriEntryState (transmuteBoolBody 2)) (by kernel_decide)
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
  by kernel_rfl

theorem loop_cycle : runAnnealBounded loopBody (5 + 1) loopHead = .running loopHead := by kernel_rfl

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
    (m := miriEntryState assertContinueBody) (by kernel_decide)
  refine ⟨?_, hm.1, hm.2⟩
  have hs : stepMirFn assertContinueBody (initMachineState assertContinueBody []) =
      .retOutcome .panic := by kernel_rfl
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
  agreeReturnsBits_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

/-- `assume(false)` is undefined behavior in both machines. -/
theorem w6_assume_false_ub :
    AgreeUB (assumeBody false) (annealMiriHooks (assumeBody false))
      (initMachineState (assumeBody false) []) (miriEntryState (assumeBody false)) :=
  agreeUB_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

/-- `exact_div::<u32>(a, 7)` (`bb0: _0 = exact_div(const a, const 7) -> bb1; bb1: return`). -/
def exactDivBody (a : Nat) : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::exact_div" WitnessLM4_2.u32K
    (WitnessLM4_2.binArgs WitnessLM4_2.u32K a 7 4) WitnessLM4_2.u32K

/-- `exact_div(42, 7)` (`pass_exact_div_valid`) returns `6` in both machines. -/
theorem w6_exact_div_valid :
    AgreeReturnsBits (exactDivBody 42) (annealMiriHooks (exactDivBody 42))
      (initMachineState (exactDivBody 42) []) (miriEntryState (exactDivBody 42)) 4 6 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by kernel_decide) (by kernel_decide)

/-- `exact_div(43, 7)` (`ub_exact_div_non_multiple`) is undefined behavior in both machines. -/
theorem w6_exact_div_non_multiple_ub :
    AgreeUB (exactDivBody 43) (annealMiriHooks (exactDivBody 43))
      (initMachineState (exactDivBody 43) []) (miriEntryState (exactDivBody 43)) :=
  agreeUB_of_obs (N := 3) (M := 3) (by kernel_decide) (by kernel_decide)

/-- `ctlz::<u32>(1)` returns `31` in both machines. -/
def ctlzBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::ctlz" WitnessLM4_2.u32K
    (WitnessLM4_2.bitArgs WitnessLM4_2.u32K 1 4) WitnessLM4_2.u32K

theorem w6_ctlz_returns :
    AgreeReturnsBits ctlzBody (annealMiriHooks ctlzBody) (initMachineState ctlzBody [])
      (miriEntryState ctlzBody) 4 31 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by kernel_decide) (by kernel_decide)

/-- `saturating_add::<u8>(250, 10)` saturates to `255` in both machines. -/
def saturatingAddBody : CapturedMir :=
  WitnessLM4_2.callBody "core::intrinsics::saturating_add" WitnessLM4_2.u8K
    (WitnessLM4_2.binArgs WitnessLM4_2.u8K 250 10 1) WitnessLM4_2.u8K

theorem w6_saturating_add_returns :
    AgreeReturnsBits saturatingAddBody (annealMiriHooks saturatingAddBody)
      (initMachineState saturatingAddBody []) (miriEntryState saturatingAddBody) 1 255 :=
  agreeReturnsBits_of_obs (N := 3) (M := 3) (by kernel_decide) (by kernel_decide)

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
        (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K := by kernel_rfl
  obtain ⟨⟨tr, hrr⟩, hub, hns⟩ := anneal_extCall_boundary (body := rotateLeftBody)
    (sᵣ := WitnessLM4_2.callAnnealPost "core::intrinsics::rotate_left" WitnessLM4_2.u32K
      (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K (.scalar ⟨3, 4⟩))
    (retVal := .scalar ⟨3, 4⟩) (v := .scalar ⟨3, 4⟩)
    (mem := (initMachineState rotateLeftBody []).memory)
    (memR := (initMachineState rotateLeftBody []).memory)
    (.refl _) hext rfl (.refl _) rfl (initMachineState rotateLeftBody []).memory
  have heq : miriEntryState rotateLeftBody =
      WitnessLM4_2.callMiriPre "core::intrinsics::rotate_left" WitnessLM4_2.u32K
        (WitnessLM4_2.binArgs WitnessLM4_2.u32K 2147483649 1 4) WitnessLM4_2.u32K := by kernel_rfl
  have hout := miri_outcome_of_path_error (H := annealMiriHooks rotateLeftBody)
    (.refl (miriEntryState rotateLeftBody)) (by rw [heq]; exact herr)
  rw [mirCallTree, hpre]
  exact ⟨⟨tr, _, hrr⟩, hub, hns, ⟨msg, hout.1⟩, hout.2⟩

/-! ## 3. Raw pointers -/

theorem lm31AddrOf_prefix_anneal : runAnnealBounded Witness.lm31AddrOfBody 3
    (initMachineState Witness.lm31AddrOfBody []) = .running Witness.lm31AddrOfAnnealPre := by kernel_rfl

theorem lm31AddrOf_prefix_miri : runLoopFuel (annealMiriHooks Witness.lm31AddrOfBody) 3
    (miriEntryState Witness.lm31AddrOfBody) = .running Witness.lm31AddrOfMiriPre := by kernel_rfl

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
    (initMachineState Witness.lm31DanglingBody []) = .running Witness.lm31DanglingAnnealPre := by kernel_rfl

theorem lm31Dangling_prefix_miri : runLoopFuel (annealMiriHooks Witness.lm31DanglingBody) 3
    (miriEntryState Witness.lm31DanglingBody) = .running Witness.lm31DanglingMiriPre := by kernel_rfl

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

theorem slot_ptr_ne_scalar_mdw {p : ProvenancePtr} {sz : Nat} {sc : MirAst.ScalarInt} :
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
        miriEntryState Witness.lm31OffsetDerefBody := by kernel_rfl
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
        miriEntryState Witness.lm31TypePunBody := by kernel_rfl
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
        miriEntryState Witness.lm31ReviveBody := by kernel_rfl
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
      .running derefMisalignedPreAnneal := by kernel_rfl

private theorem derefMisaligned_prefix_miri :
    runLoopFuel (annealMiriHooks derefMisalignedEntryBody) 6
      (miriEntryState derefMisalignedEntryBody) =
      .running derefMisalignedPreMiri := by kernel_rfl

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
  have hs₁ : stepMirFn b derefMisalignedPreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
  have hs₄ : stepMirFn b s₃ = .step s₄ := by kernel_rfl
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
  have hs₅ : stepMirFn b s₄ = .fail .ub := by kernel_rfl
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
      .running (fourLocalEntryPreAnneal derefOobWriteEntryBody ⟨42, 8⟩) := by kernel_rfl

private theorem derefOobWrite_prefix_miri :
    runLoopFuel (annealMiriHooks derefOobWriteEntryBody) 4
      (miriEntryState derefOobWriteEntryBody) =
      .running (fourLocalEntryPreMiri derefOobWriteEntryBody Witness.u64Ty Witness.lm31Scalar42) := by kernel_rfl

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
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨42, 8⟩) = .step s₁ := by kernel_rfl
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
      .running (fourLocalEntryPreAnneal ptrOffsetNegOobEntryBody ⟨42, 8⟩) := by kernel_rfl

private theorem ptrOffsetNegOob_prefix_miri :
    runLoopFuel (annealMiriHooks ptrOffsetNegOobEntryBody) 4
      (miriEntryState ptrOffsetNegOobEntryBody) =
      .running (fourLocalEntryPreMiri ptrOffsetNegOobEntryBody Witness.u64Ty Witness.lm31Scalar42) := by kernel_rfl

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
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨42, 8⟩) = .step s₁ := by kernel_rfl
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
      .running (fourLocalEntryPreAnneal invalidBoolPtrDerefEntryBody ⟨2, 1⟩) := by kernel_rfl

private theorem invalidBoolPtrDeref_prefix_miri :
    runLoopFuel (annealMiriHooks invalidBoolPtrDerefEntryBody) 4
      (miriEntryState invalidBoolPtrDerefEntryBody) =
      .running (fourLocalEntryPreMiri invalidBoolPtrDerefEntryBody Witness.u8TyLM31
        (Miri.Memory.ScalarInt.ofUInt8 2)) := by kernel_rfl

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
  have hs₁ : stepMirFn b (fourLocalEntryPreAnneal b ⟨2, 1⟩) = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
      .running ptrOffsetStridePreAnneal := by kernel_rfl

private theorem ptrOffsetStride_prefix_miri :
    runLoopFuel (annealMiriHooks ptrOffsetStrideEntryBody) 5
      (miriEntryState ptrOffsetStrideEntryBody) =
      .running ptrOffsetStridePreMiri := by kernel_rfl

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
  have hs₁ : stepMirFn b ptrOffsetStridePreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
  have ha₅ : stepMirFn b s₄ = .retNormal (.scalar ⟨300, 4⟩)
      { s₄.memory with borrows := disableFrameBorrows s₄.memory.borrows 0 b.localDecls.length } := by kernel_rfl
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

/-- Entry-to-UB MIR body for `ub_deref_null_ptr_read`:
`StorageLive(_1); _1 = const (0 as *const u64); _0 = copy (*_1); return`. -/
def nullPtrReadEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::deref_null_ptr_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.u64Decl, Witness.rawPtrConstU64Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1),
      Witness.mkStmt (.assign (Witness.local_ 1)
        (.use (.constant { ty := Witness.rawPtrConstU64Ty, val := .scalar (.int ⟨0, 8⟩) }))),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy (Witness.derefLocal 1))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **Agreement from entry** (`ub_deref_null_ptr_read`, `nullPtrReadEntryBody`):
dereferencing a null `*const u64` for a read is undefined behavior in both machines
(as before Stage-1), checked by kernel evaluation of both whole-program runs. -/
theorem w3_deref_null_ptr_read_ub :
    AgreeUB nullPtrReadEntryBody (annealMiriHooks nullPtrReadEntryBody)
      (initMachineState nullPtrReadEntryBody [])
      (miriEntryState nullPtrReadEntryBody) :=
  agreeUB_of_obs (N := 5) (M := 5) (by kernel_decide) (by kernel_decide)

/-- Entry-to-UB MIR body for `ub_deref_null_ptr_write`:
`StorageLive(_1); _1 = const (0 as *mut u64); (*_1) = const 99_u64; return`. -/
def nullPtrWriteEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::deref_null_ptr_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [WitnessLM4_2.declOf WitnessLM4_2.unitK, Witness.rawPtrMutU64Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1),
      Witness.mkStmt (.assign (Witness.local_ 1)
        (.use (.constant { ty := Witness.rawPtrMutU64Ty, val := .scalar (.int ⟨0, 8⟩) }))),
      Witness.mkStmt (.assign (Witness.derefLocal 1) (.use (.constant (Witness.constU64 99))))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **Agreement from entry** (`ub_deref_null_ptr_write`, `nullPtrWriteEntryBody`):
dereferencing a null `*mut u64` for a write is undefined behavior in both machines
(as before Stage-1), checked by kernel evaluation of both whole-program runs. -/
theorem w3_deref_null_ptr_write_ub :
    AgreeUB nullPtrWriteEntryBody (annealMiriHooks nullPtrWriteEntryBody)
      (initMachineState nullPtrWriteEntryBody [])
      (miriEntryState nullPtrWriteEntryBody) :=
  agreeUB_of_obs (N := 5) (M := 5) (by kernel_decide) (by kernel_decide)

/-- Entry-to-return MIR body for RFC 2582 `&raw const (*ptr::null::<u64>())`
(`step_rawPtr_deref_null_simulation`):
`StorageLive(_1); _1 = const (0 as *const u64); _0 = &raw const (*_1); return`. -/
def nullPtrRawReborrowEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::rawptr_deref_null_reborrow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.rawPtrConstU64Decl, Witness.rawPtrConstU64Decl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1),
      Witness.mkStmt (.assign (Witness.local_ 1)
        (.use (.constant { ty := Witness.rawPtrConstU64Ty, val := .scalar (.int ⟨0, 8⟩) }))),
      Witness.mkStmt (.assign (Witness.local_ 0) (.rawPtr .not (Witness.derefLocal 1)))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **RFC 2582 null place-to-pointer agreement from entry, a Stage-1 upgrade**
(`step_rawPtr_deref_null_simulation`, `nullPtrRawReborrowEntryBody`): unlike `*ptr`
reads/writes, `&raw const (*ptr::null::<u64>())` steps without undefined behavior in
both machines and returns the null pointer `0` (checked by kernel evaluation of both
whole-program runs). Pre-Stage-1 Anneal required a `Value.ptr` operand and rejected
this reborrow with undefined behavior (`step_rawPtr_deref_null_divergence` of the
pre-Stage-1 ledger). -/
theorem w3_rawPtr_deref_null_reborrow_returns :
    AgreeReturnsBits nullPtrRawReborrowEntryBody (annealMiriHooks nullPtrRawReborrowEntryBody)
      (initMachineState nullPtrRawReborrowEntryBody [])
      (miriEntryState nullPtrRawReborrowEntryBody) 8 0 :=
  agreeReturnsBits_of_obs (N := 5) (M := 5) (by kernel_decide) (by kernel_decide)

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

/-- Anneal's state of a `ptr4EntryBody` after its entry block `bb0` (at `bb1`):
`_1 = 42_u64`, every other local uninitialized. -/
def ptr4EntryPreAnneal (b : CapturedMir) : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState b []).memory }

/-- `lean-miri`'s root frame of a `ptr4EntryBody` after its entry block `bb0`. -/
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

/-- `lean-miri`'s state of a `ptr4EntryBody` after its entry block `bb0`
(`initMachineState` / `miriEntryState` reach `ptr4EntryPreAnneal` / `ptr4EntryPreMiri`
in `5` steps, checked by `rfl` per body). -/
def ptr4EntryPreMiri (b : CapturedMir) : AnnealStepState :=
  { stack := ⟨#[ptr4EntryPreMiriFrame b]⟩, machine := AnnealMachine.empty }

/-- The post-entry-block states of a `ptr4EntryBody` are `StateRel`-related, and
every `lean-miri` local is immediate. -/
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
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := by kernel_rfl
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
  have hret : stepMirFn b s₁ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8)
      { s₁.memory with borrows := disableFrameBorrows s₁.memory.borrows 0 b.localDecls.length } :=
    by kernel_rfl
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
  have hfail : stepMirFn b (ptr4EntryPreAnneal b) = .fail .ub := by kernel_rfl
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
      .running safeRefPreAnneal := by kernel_rfl

theorem safeRef_prefix_miri :
    runLoopFuel (annealMiriHooks safeRefReturnBody) 2 (miriEntryState safeRefReturnBody) =
      .running safeRefPreMiri := by kernel_rfl

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
  have hs₁ : stepMirFn b safeRefPreAnneal = .step s₁ := by kernel_rfl
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
  have hret : stepMirFn b s₁ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8)
      { s₁.memory with borrows := disableFrameBorrows s₁.memory.borrows 0 b.localDecls.length } :=
    by kernel_rfl
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
      .running invalidBoolRefPreAnneal := by kernel_rfl

private theorem invalidBoolRef_prefix_miri :
    runLoopFuel (annealMiriHooks invalidBoolRefEntryBody) 3
      (miriEntryState invalidBoolRefEntryBody) =
      .running invalidBoolRefPreMiri := by kernel_rfl

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
  have hs₁ : stepMirFn b invalidBoolRefPreAnneal = .step s₁ := by kernel_rfl
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

private theorem step_storageDead_lm3_2_preserves_mdw
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry} (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) (hne0 : loc ≠ 0)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hstep
  injection hstep with hm' _; subst hm'
  intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp
  rw [hframes] at htf₀; injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
  injection htf' with h₁; injection h₁ with h₁'; subst h₁'
  dsimp only [] at hmls'; rw [Array.getElem?_set] at hmls'
  by_cases hlk : loc = k
  · subst hlk; simp only [↓reduceIte, Option.some.injEq] at hmls'; rw [← hmls'] at hmp; cases hmp
  · simp only [hlk, ↓reduceIte] at hmls'; exact hk mls' hmls' mp hmp

/-- Entry-to-UB MIR body for reborrowing a dangling safe reference
(`evalRvalue_reborrow_safeRef_dangling_simulation`):
`bb0: StorageLive(_1.._3); _1 = 42_u64; goto bb1;
bb1: _2 = &_1; StorageDead(_1); _3 = &(*_2); return`. -/
def reborrowDanglingSafeRefEntryBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::reborrow_dangling_safe_ref"
    WitnessLM4_2.u64K (.ref .not WitnessLM4_2.u64K) (.ref .not WitnessLM4_2.u64K)
    [Witness.mkStmt (.assign (Witness.local_ 2) (.ref .shared (Witness.local_ 1))),
     Witness.mkStmt (.storageDead 1),
     Witness.mkStmt (.assign (Witness.local_ 3) (.ref .shared (Witness.derefLocal 2)))]
    .return_

/-- Entry block of `reborrowDanglingSafeRefEntryBody`, from `initMachineState`. -/
theorem reborrowDanglingSafeRef_prefix_anneal :
    runAnnealBounded reborrowDanglingSafeRefEntryBody 5
      (initMachineState reborrowDanglingSafeRefEntryBody []) =
      .running (ptr4EntryPreAnneal reborrowDanglingSafeRefEntryBody) := by kernel_rfl

/-- Entry block of `reborrowDanglingSafeRefEntryBody`, from `miriEntryState`. -/
theorem reborrowDanglingSafeRef_prefix_miri :
    runLoopFuel (annealMiriHooks reborrowDanglingSafeRefEntryBody) 5
      (miriEntryState reborrowDanglingSafeRefEntryBody) =
      .running (ptr4EntryPreMiri reborrowDanglingSafeRefEntryBody) := by kernel_rfl

/-- **Stage-1 lockstep from entry** (`evalRvalue_reborrow_safeRef_dangling_simulation`,
`reborrowDanglingSafeRefEntryBody`): from `initMachineState` / `miriEntryState`, both
machines execute `_2 = &_1` and `StorageDead(_1)` in lockstep and reject the dangling
reborrow `_3 = &(*_2)` with undefined behavior. -/
theorem w4_reborrow_dangling_safeRef_ub :
    AgreeUB reborrowDanglingSafeRefEntryBody (annealMiriHooks reborrowDanglingSafeRefEntryBody)
      (initMachineState reborrowDanglingSafeRefEntryBody [])
      (miriEntryState reborrowDanglingSafeRefEntryBody) := by
  let b := reborrowDanglingSafeRefEntryBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b
    "lm_4_3_witness::reborrow_dangling_safe_ref"
    WitnessLM4_2.u64K (.ref .not WitnessLM4_2.u64K) (.ref .not WitnessLM4_2.u64K)
    [Witness.mkStmt (.assign (Witness.local_ 2) (.ref .shared (Witness.local_ 1))),
     Witness.mkStmt (.storageDead 1),
     Witness.mkStmt (.assign (Witness.local_ 3) (.ref .shared (Witness.derefLocal 2)))]
    .return_ rfl
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 Witness.lm31AllocId1
  let entryDis : AllocMapEntry := { entry with perm := .disabled, allocDead := true }
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .uninit] [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := by kernel_rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_step_of_anneal_step hsim₁ hs₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_nextAllocId_two hrel₀ rfl rfl
    (dstDecl := Witness.refU64Decl) (targetDecl := Witness.u64Decl) rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩) rfl hm₁
  have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
    fun tf htf => isImmediateFrameLocal_of_nextAllocId_two hrel₁ hsup₁ hnext₁
      (List.Mem.head _) rfl htf 2 (by decide)
  let s₂ := WitnessLM4_2.mkPtrState b 1 2
    [.uninit, .dead, .init ptr1, .uninit] [entryDis.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
  have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_step_of_anneal_step hsim₂ hs₂
  change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
  have himm₂_step := step_storageDead_lm3_2_preserves_mdw hrel₁ rfl rfl rfl (by decide) hm₂
  have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf₂ htf₂; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ 2 (himm₁_2 tf₁ htf₁)
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  obtain ⟨_, hs₃, m₃, hm₃⟩ := evalRvalue_reborrow_safeRef_dangling_simulation
    hrel₂ hphase (dstIdx := 3) (refIdx := 2) (bk := .shared)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
    (fun h => nomatch h) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
    (e := entryDis) (List.Mem.head _) rfl rfl
  exact agreeUB_of_paths reborrowDanglingSafeRef_prefix_anneal reborrowDanglingSafeRef_prefix_miri
    (.step .silent hs₁ (.step .silent hs₂ (.refl _))) hs₃
    (.step hm₁ (frames_ne_of_step_ok_true hm₂) (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _)))
    hm₃ rfl

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
      .running disabledReadPreAnneal := by kernel_rfl

theorem disabledRead_prefix_miri :
    runLoopFuel (annealMiriHooks disabledReadEntryBody) 3 (miriEntryState disabledReadEntryBody) =
      .running disabledReadPreMiri := by kernel_rfl

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
  have ha := anneal_ub_of_obs (body := b) (N := 7) (s := initMachineState b []) (by kernel_decide)
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hrel₀, himm₀⟩ := disabledRead_pre_stateRel_and_imm
  let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 Witness.lm31AllocId1
  let entryDis : AllocMapEntry := { entry with perm := .disabled }
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4,
                 locals := [.uninit, .init (.scalar ⟨42, 8⟩),
                            .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
      memory := { (initMachineState b []).memory with borrows := [entry.toBorrowEntry], nextTag := 2 } }
  have hs₁ : stepMirFn b disabledReadPreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
  have hs₃_act : stepMirFn b s₂_act = .step s₃_act := by kernel_rfl
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
  have hret_act : stepMirFn b s₃_act = .retNormal (.scalar ⟨77, 8⟩)
      { s₃_act.memory with borrows := disableFrameBorrows s₃_act.memory.borrows 0 b.localDecls.length } := by kernel_rfl
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
  refine ⟨imm0, agreeReturns_of_bits_path (N := 9) (sz := 8) (b := 99) (by kernel_decide)
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
        (initMachineState Witness.lm22PaddedBody [])
        (miriEntryState Witness.lm22PaddedBody) (.scalar ⟨99, 4⟩) v ∧
      operandScalarBits? 4 v = some 99 := by
  obtain ⟨_, _, ha, hm⟩ := Witness.lm22Padded_full_trace_and_returns_agree
  obtain ⟨m', v, hrun, hbits⟩ := miriOutcomeScalarBits_spec hm
  have hentry : miriEntryState Witness.lm22PaddedBody = Witness.lm22PaddedMiriInit := by kernel_rfl
  have hloop := runLoopFuel_of_runMiriBoundedLM2_2 hrun
  rw [← hentry] at hloop
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
  have hentry : miriEntryState Witness.lm21FullFnBody = Witness.lm21FullFnInitMiri := by kernel_rfl
  have hloop := runLoopFuel_of_runMiriBounded hm
  rw [← hentry] at hloop
  obtain ⟨hts, ⟨tr, hrr⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned ha
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_runLoopFuel_returned hloop
  refine ⟨hts, ⟨tr, mem', hrr⟩, hsafe, hreach, fun v' hv' => ?_⟩
  have := huniq _ hv'
  injection this

/-- Entry-to-UB MIR body for `LM-2.1` array `Index` out of bounds:
`StorageLive(_1); StorageLive(_2); _2 = const 3_usize;
_1 = [0x0102_u16, 0x0304_u16, 0x0506_u16]; _0 = copy _1[_2]; return`. -/
def arrayIndexOobEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::array_index_oob_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [Witness.lm21U16Decl, Witness.lm21U16Arr3Decl, Witness.lm21UsizeDecl]
  basicBlocks := [{
    statements := [
      Witness.mkStmt (.storageLive 1),
      Witness.mkStmt (.storageLive 2),
      Witness.mkStmt (.assign (Witness.local_ 2) (.use (.constant (Witness.lm21ConstUsize 3)))),
      Witness.mkStmt (.assign (Witness.local_ 1) (.aggregate (.array Witness.lm21U16Ty)
        [.constant (Witness.lm21ConstU16 0x0102), .constant (Witness.lm21ConstU16 0x0304),
         .constant (Witness.lm21ConstU16 0x0506)])),
      Witness.mkStmt (.assign (Witness.local_ 0) (.use (.copy ⟨1, [.index 2]⟩)))]
    terminator := Witness.mkTerm .return_, isCleanup := false }]
  fnAbi := Witness.lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state of `arrayIndexOobEntryBody` after `StorageLive(_1)`,
`StorageLive(_2)`, and `_2 = const 3_usize` (statement `3` of `bb0`). -/
def arrayIndexOobPreAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .uninit, .init (.scalar ⟨3, 8⟩)] }
    memory := (initMachineState arrayIndexOobEntryBody []).memory }

/-- `lean-miri`'s root frame matching `arrayIndexOobPreAnneal`. -/
def arrayIndexOobPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame arrayIndexOobEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm21Usize3))),
        layout := some (translateTy Witness.lm21UsizeTy emptyLayoutTable) }]
    location := .mir ⟨0, 3⟩ }

/-- `lean-miri`'s state matching `arrayIndexOobPreAnneal`. -/
def arrayIndexOobPreMiri : AnnealStepState :=
  { stack := ⟨#[arrayIndexOobPreMiriFrame]⟩, machine := AnnealMachine.empty }

/-- The allocation-free prefix of `arrayIndexOobEntryBody`, from `initMachineState`. -/
theorem arrayIndexOob_prefix_anneal :
    runAnnealBounded arrayIndexOobEntryBody 3 (initMachineState arrayIndexOobEntryBody []) =
      .running arrayIndexOobPreAnneal := by kernel_rfl

/-- The allocation-free prefix of `arrayIndexOobEntryBody`, from `miriEntryState`. -/
theorem arrayIndexOob_prefix_miri :
    runLoopFuel (annealMiriHooks arrayIndexOobEntryBody) 3
      (miriEntryState arrayIndexOobEntryBody) = .running arrayIndexOobPreMiri := by kernel_rfl

/-- The post-prefix states of `arrayIndexOobEntryBody` are `StateRel`-related, and
every `lean-miri` local is immediate. -/
theorem arrayIndexOob_pre_stateRel_and_imm :
    StateRel arrayIndexOobEntryBody arrayIndexOobPreAnneal arrayIndexOobPreMiri ∧
    ∀ tf, arrayIndexOobPreMiri.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk arrayIndexOobPreMiriFrame rfl rfl
      ⟨entryReturnLayout arrayIndexOobEntryBody, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with | 0 | 1 | 2 | _ + 3 => simp [arrayIndexOobPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 1 =>
      have hs : slot = .uninit := by simpa [arrayIndexOobPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [arrayIndexOobPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 2 =>
      have hd : decl = Witness.lm21UsizeDecl := by
        simpa [arrayIndexOobEntryBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨3, 8⟩) := by
        simpa [arrayIndexOobPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt Witness.lm21Usize3))),
            layout := some (translateTy Witness.lm21UsizeTy emptyLayoutTable) } := by
        simpa [arrayIndexOobPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ _ (by intro _ h; cases h; rfl)
        (Or.inr ⟨.scalar ⟨3, 8⟩, rfl, Witness.lm21_idxRel_3⟩)
    | _ + 3 => simp [arrayIndexOobEntryBody, get?] at hdecl
  · intro tf htf k mls hmls mp hv
    have htf' : tf = arrayIndexOobPreMiriFrame := by
      simpa [arrayIndexOobPreMiri] using htf.symm
    subst htf'
    match k with
    | 0 | 1 | 2 => simp [arrayIndexOobPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 3 => simp [arrayIndexOobPreMiriFrame] at hmls

/-- `LM-2.1` array `Index` out of bounds (`_2 = 3_usize` on `[u16; 3]`):
from program entry, both machines reach undefined behavior (`AgreeUB`). -/
theorem w2_array_index_oob_ub :
    AgreeUB arrayIndexOobEntryBody (annealMiriHooks arrayIndexOobEntryBody)
      (initMachineState arrayIndexOobEntryBody []) (miriEntryState arrayIndexOobEntryBody) := by
  let b := arrayIndexOobEntryBody
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4,
                 locals := [.uninit, .init (.aggregate 0 Witness.lm21ArrElems),
                            .init (.scalar ⟨3, 8⟩)] }
      memory := (initMachineState b []).memory }
  have hs₀ : stepMirFn b arrayIndexOobPreAnneal = .step s₁ := by kernel_rfl
  obtain ⟨hrel₀, himm₀⟩ := arrayIndexOob_pre_stateRel_and_imm
  have hcU16 : ∀ tf (n : Nat), n < 65536 →
      WellTypedLM2_1ScalarOperand b tf (.constant (Witness.lm21ConstU16 n)) Witness.lm21U16Ty :=
    fun _ n hn => .ofScalar (.constScalar (Witness.lm21ConstU16 n) ⟨n, 2⟩ rfl
      Witness.lm21_isPrim_u16 (Or.inr (Or.inl rfl)) (by simpa [scalarModulus] using hn)
      rfl (fun h => nomatch h) (fun h => nomatch h))
  obtain ⟨hsim₁, hnd₁, himm₁, _⟩ := step_stmt_lm2_1_array_simulation hrel₀
    Witness.lm21_nodup_empty (by intro p h; cases h) rfl rfl (fun tf htf => by
      refine .aggregateArray 1 Witness.lm21U16Arr3Decl Witness.lm21U16Ty (.uint .u16) 3 _ _
        rfl Witness.lm21_wf_u16Arr3 rfl
        (Or.inr (Or.inl ⟨himm₀ tf htf 1, Witness.lm21_canReserve_empty⟩)) ?_
        Witness.lm21_isPrim_u16
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact hcU16 tf 0x0102 (by decide)
      · exact hcU16 tf 0x0304 (by decide)
      · exact hcU16 tf 0x0506 (by decide))
  rw [hs₀] at hsim₁
  generalize hm₁ : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) ()
    arrayIndexOobPreMiri = r₁ at hsim₁ hnd₁ himm₁
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    have hs₁ : stepMirFn b s₁ = .fail .ub := by kernel_rfl
    obtain ⟨hsim₂, _⟩ := step_stmt_lm2_1_array_simulation hrel₁ (hnd₁ rfl)
      (by intro p h; cases h) rfl rfl (fun tf htf =>
        .elemAssign (.readElem 0 1 Witness.lm21U16Decl Witness.lm21U16Arr3Decl (.uint .u16) 3
          (.index 2) false _ rfl Witness.lm21_wf_u16Arr3 rfl rfl
          (himm₁ rfl _ tf rfl htf 0 (by decide) (himm₀ _ rfl 0))
          (.index 2 Witness.lm21UsizeDecl rfl rfl
            (Or.inl (himm₁ rfl _ tf rfl htf 2 (by decide) (himm₀ _ rfl 2))))
          (Or.inr (Or.inr ⟨Witness.lm21ArrElems, rfl⟩))))
    rw [hs₁] at hsim₂
    generalize hm₂ : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) ()
      m₁ = r₂ at hsim₂
    cases hsim₂ with
    | ub m₂ msg =>
      exact agreeUB_of_obs_path (N := 6) (by kernel_decide)
        ((MiriPath.of_runLoopFuel arrayIndexOob_prefix_miri).trans
          (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _))) hm₂ rfl

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
  exact agreeUB_of_obs_path (N := 3) (by kernel_decide)
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
      (s := Witness.lm24InitAnneal 1) (by kernel_decide)).1⟩

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
      .running unionRetPreAnneal := by kernel_rfl

theorem unionRet_prefix_miri :
    runLoopFuel
      (.ofHooks (annealStepHooksLM2_4 unionRetBody.localDecls unionRetBody.layouts)
        annealControlHooks) 1 (miriEntryState unionRetBody) =
      .running unionRetPreMiri := by kernel_rfl

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
  have hs₁ : stepMirFn b unionRetPreAnneal = .step s₁ := by kernel_rfl
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
  have hs₃ : stepMirFn b s₂ = .retNormal (.scalar ⟨5, 1⟩) s₂.memory := by kernel_rfl
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
  have hs₁ : stepMirFn b (initMachineState b []) = .step s₁ := by kernel_rfl
  have hs₂ : stepMirFn b s₁ = .retNormal (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]) s₁.memory := by kernel_rfl
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (stateRelLM2_4_entry b)
    List.Pairwise.nil MemoryHighWater.empty.canReserveAllocId hphase
    (u := 0) (bb := _) rfl rfl rfl Witness.lm24_wt_U rfl (by decide) rfl rfl rfl
    himm₀ Witness.lm24_isPrim_u8 (fun tf _ => hc5 tf) (by decide)
    (hdecls_adt := hdecls_adt)
  obtain ⟨_, _, m₁, _, hm₁, _, hstate₁, _, hframes₁, _, _, _, _, _, _, _, _⟩ := hpost₁ s₁ hs₁
  have hsim₂ := step_terminator_return_wellTypedUnion_lm2_4_simulation hstate₁ hphase
    rfl rfl rfl rfl rfl (decl0 := Witness.lm24Decl Witness.lm24UTy) rfl Witness.lm24_wt_U
    (fun ⟨h, _⟩ => h.elim (fun h => nomatch h) (fun ⟨_, hv, hvc⟩ => by dsimp only [s₁, get?] at hv; injection hv with hv; injection hv with hv; subst hv; cases hvc))
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
  have hpa : runAnnealBounded b 1 (initMachineState b []) = .running unionOverlayPreAnneal := by kernel_rfl
  have hpm : runLoopFuel
      (.ofHooks (annealStepHooksLM2_4 b.localDecls b.layouts) annealControlHooks) 1
      (miriEntryState b) = .running unionOverlayPreMiri := by kernel_rfl
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
  have hs₁ : stepMirFn b unionOverlayPreAnneal = .step s₁ := by kernel_rfl
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
  have hs₃ : stepMirFn b s₂ = .step s₃ := by kernel_rfl
  have hs₄ : stepMirFn b s₃ = .retNormal (.scalar ⟨0x04030209, 4⟩) s₃.memory := by kernel_rfl
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
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step s₁ := by kernel_rfl
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
  have hfail : stepMirFn b s₁ = .fail .ub := by kernel_rfl
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
      (s := WitnessLM4_2.copy6AnnealPre WitnessLM4_2.copyDistinctBody true) (by kernel_decide)).1⟩

/-- `write_bytes::<u64>(copy ptrIdx, valBits_u8, countBits_usize) -> bb2` into the
unit return place `_0` (`WitnessLM4_2.writeBytesTerm` retargeted for
`ptr4EntryBody`). -/
def writeBytesEntryTerm (ptrIdx : Local) (valBits countBits : Nat) : TerminatorKind :=
  .call (.constant (WitnessLM4_2.fnItem "core::intrinsics::write_bytes" WitnessLM4_2.u64K))
    [.copy (WitnessLM4_2.local42 ptrIdx),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.u8K valBits 1),
     .constant (WitnessLM4_2.constInt WitnessLM4_2.usizeK countBits 8)]
    (WitnessLM4_2.local42 0) (some 2) .unreachable

/-- `WitnessLM4_2.writeBytesMutBody 0xAB 1` behind the entry block of `ptr4EntryBody`:

```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 42_u64;
     goto -> bb1;
bb1: _2 = &raw mut _1;
     _0 = write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2;
bb2: return
``` -/
def writeBytesEntryBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::write_bytes_boundary"
    WitnessLM4_2.unitK WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    (writeBytesEntryTerm 2 0xAB 1)

/-- The entry block of `writeBytesEntryBody`, from `initMachineState`. -/
theorem writeBytesEntry_prefix_anneal :
    runAnnealBounded writeBytesEntryBody 5 (initMachineState writeBytesEntryBody []) =
      .running (ptr4EntryPreAnneal writeBytesEntryBody) := by kernel_rfl

/-- The entry block of `writeBytesEntryBody`, from `miriEntryState`. -/
theorem writeBytesEntry_prefix_miri :
    runLoopFuel (annealMiriHooks writeBytesEntryBody) 5 (miriEntryState writeBytesEntryBody) =
      .running (ptr4EntryPreMiri writeBytesEntryBody) := by kernel_rfl

/-- Anneal's state of a `ptr4EntryBody` after `_2 = &raw mut _1` (`bb1`, statement
`1`; `_2` holds the raw pointer to `_1`'s stack allocation `1`, tagged `1`). -/
def wbAddrOfState (b : CapturedMir) : MachineState :=
  WitnessLM4_2.mkPtrState b 1 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [(rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1).toBorrowEntry] 2

/-- **Inline `write_bytes` in lockstep, from program entry** (`write_bytes::<u64>(ptr,
0xAB, 1)`, `writeBytesEntryBody`): both machines run the entry block and
`_2 = &raw mut _1` in lockstep from `initMachineState` / `miriEntryState`
(`AgreeReaches`, `step_rawPtr_addrOf_simulation`). Then both execute `write_bytes`
inline: Stage-1 `stepMirFn` (`Trusted.Rustc.V2026_06_01.MirSemantics.evalWriteBytesCall`,
since `ws-repatriate-leaked-ground-semantics-to-tcb`) fills `_1` with `0xAB` bytes,
and Anneal's whole program is `TreeSafe` and returns `()`; `lean-miri` (in lockstep
with the pre-Stage-1 reference model `stepMirFnLM4_2`,
`call_intrinsic_write_bytes_simulation`) reaches a state `StateRelLM3_1`-related to
an Anneal state with the same `_1 = 0xABABABABABABABAB`. (Before that episode,
Stage-1 handed the call to the environment, `MirStepNode.extCall`.) -/
theorem w6_write_bytes_inline_lockstep :
    ∃ m₁ m₂ sW,
      AgreeReaches writeBytesEntryBody (annealMiriHooks writeBytesEntryBody)
        (initMachineState writeBytesEntryBody []) (wbAddrOfState writeBytesEntryBody)
        (miriEntryState writeBytesEntryBody) m₁ ∧
      stepMirFn writeBytesEntryBody (wbAddrOfState writeBytesEntryBody) = .step sW ∧
      get? sW.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) ∧
      TreeSafe (mirCallTree writeBytesEntryBody []) ∧
      (∃ tr mem, ReachesRet (mirCallTree writeBytesEntryBody []) tr (.normal (.unit, mem))) ∧
      (miriSystem (annealMiriHooks writeBytesEntryBody)).Reaches
        (miriEntryState writeBytesEntryBody) m₂ ∧
      ∃ s₂, StateRelLM3_1 writeBytesEntryBody s₂ m₂
          [rawPtrAllocMapEntry writeBytesEntryBody.localDecls writeBytesEntryBody.layouts .mut 1 1
            Witness.lm31AllocId1] ∧
        get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) := by
  let b := writeBytesEntryBody
  obtain ⟨hrel₀, himm₀_all⟩ := ptr4Entry_stateRel_and_imm b "lm_4_3_witness::write_bytes_boundary"
    WitnessLM4_2.unitK WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    (writeBytesEntryTerm 2 0xAB 1) rfl
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (ptr4EntryPreMiri b).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩
  let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
  have hpa := writeBytesEntry_prefix_anneal
  have hpm := writeBytesEntry_prefix_miri
  -- Step 1: `_2 = &raw mut _1`, in lockstep.
  have hs₁ : stepMirFn b (ptr4EntryPreAnneal b) = .step (wbAddrOfState b) := by kernel_rfl
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
  -- Step 2: `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize)`, inline in `lean-miri`.
  let s₂ := WitnessLM4_2.mkPtrState b 2 0
    [.uninit, .init (.scalar ⟨0xABABABABABABABAB, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFnLM4_2 b (wbAddrOfState b) = .step s₂ := by kernel_rfl
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
        simpa [wbAddrOfState, WitnessLM4_2.mkPtrState, get?] using hp.symm
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
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
  have hM₂ : MiriPath (annealMiriHooks b) (miriEntryState b) m₂ :=
    (MiriPath.of_runLoopFuel hpm).trans
      (.step hm₁ (frames_ne_of_eq_singleton htf₁)
        (.step hm₂ (frames_ne_of_eq_singleton htf₂) (.refl _)))
  -- Anneal: `write_bytes` inline, then the root return of `()`.
  obtain ⟨hAsafe, ⟨tr, htr⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned
    (body := b) (N := 30) (s := initMachineState b []) (retVal := .unit)
    (by dsimp only [b]; rfl)
  have hagree : AgreeReaches b (annealMiriHooks b) (initMachineState b []) (wbAddrOfState b)
      (miriEntryState b) m₁ :=
    agreeReaches_of_prefix_paths hpa hpm (.step .silent hs₁ (.refl _))
      (.step hm₁ (frames_ne_of_eq_singleton htf₁) (.refl _))
  have hget : get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) := by kernel_rfl
  exact ⟨m₁, m₂, _, hagree, rfl, rfl, hAsafe, ⟨tr, _, htr⟩, hM₂.reaches, s₂, hrel₂, hget⟩

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
      (s := WitnessLM3_3.initD) (sz := 4) (b := 7) (by kernel_decide),
      c₂, c₃, .step .silent hc₁ (.step .silent hc₂ (.refl _)), hc₃, hcb₂, hcb₃,
      hcw, hcrel, hcr⟩,
    ⟨anneal_ub_of_obs (body := WitnessLM3_3.bodyD SimLM3_3.u32T) (N := 6) (s := WitnessLM3_3.initD)
      (by kernel_decide),
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
      (by kernel_decide),
    s₂, s₃, s₄, .step .silent h₁ (.step .silent h₂ (.refl _)), h₃, h₄,
    hfail, hprot, hb₄, hrel₃, hread, hrel₄, hwrite⟩

/-- **Stage-1 `StorageDead` with active `CallId` protector** (`LM-3.3` `D15`,
`SimLM3_3.sim_lm3_3_storage_dead_and_live_protector_step`): across all 6-state
`TreeBorrowPerm` permissions `perm`:
* when `activeProtectors = [1]` and `preventsDeallocation perm = true`
  (`perm ≠ .cell ∧ perm ≠ .disabled`), Anneal's whole program faults with undefined
  behavior (`MirReachesUB ∧ ¬ TreeSafe`), and for every non-`Cell` permission
  (`perm ≠ .cell`), `lean-miri`'s `BorrowTree.deallocateBorrowRange` also rejects
  the protected deallocation (`status ≠ Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated`);
* when `activeProtectors = []`, `StorageDead(_1)` steps cleanly, disabling the
  local borrow in `TreeBorrowsRel` lockstep with `deallocateBorrowRange`;
* on a protected `Cell` (`perm = .cell`), BOTH Stage-1 Anneal `StorageDead` and
  `deallocateBorrowRange` succeed (`sim_lm3_3_storage_dead_protected_cell_simulation`).
  (A protected `.disabled` entry in a live allocation is not claimed here: Anneal treats
  `.disabled` as not preventing deallocation, which matches Tree Borrows only because a
  strongly protected tag cannot become `Disabled` without earlier UB; Anneal reaches
  protected `.disabled` entries only after the allocation was already deallocated.) -/
theorem w4_storage_dead_protected_ub (perm : TreeBorrowPerm) :
    (preventsDeallocation perm = true →
      MirReachesUB (mirTree SimLM3_3.storageDeadBody (SimLM3_3.childState perm true)) ∧
      ¬ TreeSafe (mirTree SimLM3_3.storageDeadBody (SimLM3_3.childState perm true))) ∧
    (perm ≠ .cell →
      ((hooksTwoNodeTree perm).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected true).protectedTags).status ≠ Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) ∧
    (∃ s_dead : MachineState,
      stepMirFn SimLM3_3.storageDeadBody (SimLM3_3.childState perm false) = .step s_dead ∧
      s_dead.memory.borrows = [{ (SimLM3_3.entry 1 .disabled) with allocDead := true }] ∧
      TreeBorrowsRel s_dead.memory.borrows [] (basedNormalTree s_dead.memory.borrows []) ∧
      ((hooksTwoNodeTree perm).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected false).protectedTags).status = Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) ∧
    ((∃ s_cell : MachineState,
      stepMirFn SimLM3_3.storageDeadBody (SimLM3_3.childState .cell true) = .step s_cell) ∧
     ((hooksTwoNodeTree .cell).deallocateBorrowRange
        (.concrete (hooksAccessTag .foreignAccess))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
        (hooksForChildProtected true).protectedTags).status = Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocStatus.Deallocated) := by
  obtain ⟨hub_fn, hne_cell, ⟨s_dead, _, hs_dead, _, hb_dead, hrel_dead, _, _, _, _⟩, hdealloc_ok⟩ :=
    SimLM3_3.sim_lm3_3_storage_dead_and_live_protector_step perm
  obtain ⟨⟨s_cell, _, hs_cell, _, _, _⟩, hcell_dealloc⟩ :=
    SimLM3_3.sim_lm3_3_storage_dead_protected_cell_simulation
  exact ⟨fun hp => anneal_ub_of_coReach (.refl _) (hub_fn hp).1, hne_cell,
    ⟨s_dead, hs_dead, hb_dead, hrel_dead, hdealloc_ok⟩,
    ⟨⟨s_cell, hs_cell⟩, hcell_dealloc⟩⟩


end LeanMiriSpec.Correspondence.MiriDiffWitnesses
