/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.FloatCastLM

/-!
# Concrete two-sided float-cast execution witnesses (`LeanMiriSpec.WitFloatCastLM`)

Kernel-checked, concrete, **multi-step** non-vacuity witnesses for the float-cast
correspondence of `LeanMiriSpec.FloatCastLM`: Rust `as` casts `CastKind.floatToFloat`,
`CastKind.floatToInt`, and `CastKind.intToFloat` executed by Anneal's trusted `stepMirFn` and by
the vendored `lean-miri` interpreter's `Miri.Interpreter.Step.step` under the float-cast hook
overlay `annealStepHooksFloat` (which routes casts through `Miri.Interpreter.Cast.cast`).
Every lockstep step instantiates `FloatCastLM`'s general real-step simulation theorems
(`step_cast_float_{constant,copy,move}_simulation`, their `_anyLocal_preserves` compositionality
lemmas, the NaN-mode theorems, `step_terminator_goto_return_lm3_1_simulation` through
`step_float_eq_annealStepHooks_at_terminator`, and the `StorageLive` / `StorageDead`
simulations); Anneal's side is evaluated concretely by the kernel, and the `lean-miri` side is
read back from `StateRelLM3_1` (`wfc_miri_scalar`), so **both** machines are pinned
bit-for-bit after every step. No shadow evaluator is defined.

* **Part 0 (machinery)**: `wfc_stateRel_entry` (the program-entry states `initMachineState body []`
  and `wfcMiriEntry body` of **any** argument-free body are `StateRelLM3_1`-related: `_0` live,
  every other local dead), `wfc_stateRel_init` (post-`StorageLive`-prologue states, used for
  hand-built intermediate states), the lockstep-run closure `WfcRun`, the lockstep predicates
  `WfcLockstep` / `WfcReturns` /
  `WfcUB` (carrying explicit `StepRelLM3_1` over arbitrary `allocMap`) and read-backs
  `MiriHoldsScalar` / `MiriHoldsUninit` / `MiriHoldsIndirectScalar` / `MiriHoldsIndirectUninit` /
  `MiriPromotedFreed` (`wfc_miri_scalar_at`, `wfc_miri_uninit_at`, `wfc_miri_indirect_scalar`,
  `wfc_miri_promoted_scalar`, `wfc_miri_promoted_uninit`, `wfc_miri_promoted_freed`), and the
  packaged step lemmas `wfc_step_{constant,copy,move}` (+ mode-generic `WfcRunMode` /
  `WfcLockstepMode` / `WfcReturnsMode` and `wfc_step_{storageLive,constant,copy,move,return}_mode`),
  `wfc_ub_{copy,move}`,
  `wfc_step_return_any` / `wfc_step_return`, `wfc_step_storageLive` / `wfc_step_storageLive_mem`,
  `wfc_step_storageDead` / `wfc_step_storageDead_any`.
* **From program entry**: the (W1)–(W4) headline witnesses, the (W2) deterministic-mode, selector,
  and `copy` / `move` selector witnesses, and the (W5) uninitialized / moved-from / dead /
  `f16` / `f128` **and** `&raw`-promoted memory-backed (W5f-1a / W5f-1b) witnesses all start at
  `initMachineState body []` / `wfcMiriEntry` and run their `StorageLive` prologues in lockstep
  (`WfcRun`); only the unpromoted force-allocated `LocalRel.indirect` witness (W5f-2, plus
  single-step selector helpers) starts from a hand-built `StateRelLM3_1` state (no MIR statement
  without `&raw` produces an unpromoted `LocalRel.indirect` scalar local).
* **(W1)** `wfcW1_end_to_end` + `wfcW1_deterministic_end_to_end` (all 18 steps — `StorageLive`,
  9 `f32 ↔ f64` casts, and `return` — in lockstep under both `annealChooseQuietedNaN` and
  deterministic mode `floatNondeterministic := false` for every `chooseNaN`) and
  `wfcW1_convert_table` (two-sided `FloatBits.convert` + `evalFloatCast .floatToFloat` class table:
  signed zeros, gradual underflow incl. the `2⁻¹⁵⁰` tie to `+0.0`, subnormal ties, `f32::MAX` and
  its `±½ulp` overflow tie, `±∞`, NaNs, and every exact `f32 → f64` widening).
* **(W2)** `wfcW2_end_to_end` (6 NaN casts + `return`: `0x7F80_0001_f32 ↦ 0x7FF8_0000_2000_0000`,
  `0x7FF0_0000_0000_0001 ↦ 0x7FC0_0000`, `0x7FF0_0000_2000_0001 ↦ 0x7FC0_0001`, negative and
  round-trip payload NaNs), `wfcW2_deterministic_canonicalization` (from program entry of
  `wfcW2DetBody`: `floatNondeterministic := false` stores `preferredNaN`, simulation modulo
  canonicalization, provably no lockstep), `wfcW2_deterministic_lockstep_cases` (from program entry
  through `return`: deterministic mode steps in lockstep on non-NaNs, canonical NaNs, **and**
  signaling NaNs whose narrowed payload truncates to `preferredNaN`, while diverging on payload
  sNaNs in both directions), `wfcW2_selectors_exact` (`pure 0 .. pure 3`), `wfcW2_selectors_snan_4_5_and_out_of_range`
  (`pure 4` / `pure 5` signaling-NaN step outputs + `pure 6` / `pure 4` out-of-range
  `.invalidProgram` tightness), `wfcW2_selectors_copy_and_move` (`copy` & `move` NaN-selector
  simulations), and `wfcW2_nanChoices_exact` (exact 6-, 4-, and 6-element candidate lists and
  deterministic singleton).
* **(W3)** `wfcW3_end_to_end` (14 casts + `return` hitting all 12 integer targets: `NaN ↦ 0`,
  `±∞ ↦ MAX/MIN`, `-0.0 ↦ 0`, finite saturation, truncation toward zero),
  `wfcW3_toInteger_all_targets` (two-sided class table for every target and both formats), and
  `wfcW3_saturation_cliffs` (two-sided 1-ULP exact-inside vs saturated-outside cliffs across
  `u8`, `i8`, `i32`, `i64`, `u64`, `i128`, `u128`, including fractional `(MAX, MAX + 1)` and
  `(MIN - 1, MIN)` truncation into range).
* **(W4)** `wfcW4_end_to_end` + `wfcW4_deterministic_end_to_end` (all 18 steps + `return` in
  lockstep under both NaN modes), `wfcW4_fromInteger_all_sources` (two-sided
  `FloatBits.fromInteger` + `evalFloatCast .intToFloat` across all 12 integer source types and both
  formats), `wfcW4_signed_negative_ties` (signed negative `i32` / `i64` halfway ties and
  `i64::MIN + 1`), and `wfcW4_ties_all_wide_sources` (the `2²⁴ ± …` / `2⁵³ ± …` tie behaviour is
  the same for **every** source type wide enough to hold it).
* **`Cast.cast` level**: `wfc_cast_two_sided_mode`, `wfc_cast_two_sided`, and
  `wfcCast_two_sided_table` pin `Miri.Interpreter.Cast.cast` over **any** 64-bit `LayoutTable` to
  the `ScalarRel`-image of Anneal's `evalFloatCast` for **every** related source scalar across
  `.FloatToFloat`, `.FloatToInt`, and `.IntToFloat`; `wfcCast_deterministic_and_f16_f128_boundary`
  adds deterministic-mode (`floatNondeterministic := false`) NaN canonicalization vs. exact
  agreement (`cast_floatToFloat_deterministic_eq`) **and** mode-generic `f16` / `f128` fail-closed
  `.unsupported` (`cast_f16_f128_unsupported` + `evalFloatCast_f16_f128_none`).
  `wfcLockstep_eq_mode` / `wfcReturns_eq_mode` / `wfcRun_iff_mode` show the refinement-witness
  predicates are instances of the mode-generic ones.
* **(W5)** `wfcW5_uninit_source_ub`, `wfcW5_moved_from_ub`, `wfcW5_dead_source_ub` (from program
  entry, through `StorageLive` / `StorageDead`) fault with `.ub` in both machines
  (`StepRelLM3_1.ub`); `wfcW5_f16_f128_fail_closed` + `wfcW5_f16_f128_uninit_source_vs_target`
  (`.unsupported` fail-closed and uninit source-vs-target evaluation-order contrast);
  `wfcW5_bool_char_boundary` (`bool` and `char` Anneal fail-closed vs `lean-miri` `Cast.cast`);
  `wfcW5_promoted_raw_pipeline_end_to_end`, `wfcW5_promoted_uninit_ub`, and
  `wfcW5_rawPtr_dead_and_promoted_dead_ub` (from program entry: `StorageLive` + `&raw mut`
  promoted local over both `emptyLayoutTable` and non-empty 64-bit `wfcStage1Layouts` + float-cast
  memory reads/writes + Tree Borrows `.active`/`.unique ↦ .disabled` + `StorageDead` stack
  deallocation `MiriPromotedFreed` + `return` / UB); and `wfcW5_indirect_float_pipeline_end_to_end`
  (multi-step unpromoted stack-allocated `LocalRel.indirect` `f64` destination write + indirect
  `copy` + indirect `move` + `return`).

Every public theorem carries a `#guard_msgs (whitespace := lax) in #print axioms` guard (standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace LeanMiriSpec.Correspondence.WitFloatCast

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.Correspondence.Witness

/-! ## Part 0. Generic witness machinery -/

/-- `lean-miri`'s root frame on entry to `body`: every declared local is live and
uninitialized (`.live (.immediate .uninit)`, no cached layout). -/
def wfcFrame (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := Array.replicate body.localDecls.length
      { value := .live (.immediate .uninit), layout := none }
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri`'s entry state for `body`: the single root frame `wfcFrame` over the empty
`AnnealMachine`. -/
def wfcMiriInit (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[wfcFrame body retTy]⟩, machine := AnnealMachine.empty }

theorem wfcFrame_locals_getElem? (body : CapturedMir) (retTy : Ty) (i : Nat) :
    (wfcFrame body retTy).locals[i]? =
      if i < body.localDecls.length then
        some { value := .live (.immediate .uninit), layout := none }
      else none := by
  simp [wfcFrame, Array.getElem?_replicate]

/-- **All-live entry relation for any body**: an Anneal state at `bb0[0]` whose locals are all
live and `.uninit` and `wfcMiriInit body retTy` (every local `.live (.immediate .uninit)`) are
`StateRelLM3_1`-related with an empty `allocMap`. For a single-local body this *is* the program
entry state; for multi-local bodies it is a hand-built start state (program-entry witnesses use
`wfc_stateRel_entry` and run the `StorageLive` prologue instead). -/
theorem wfc_stateRel_init (body : CapturedMir) (retTy : Ty) (s : MachineState)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hframe0 : s.frame =
      { blockIdx := 0, stmtIdx := 0, locals := List.replicate body.localDecls.length .uninit }) :
    StateRelLM3_1 body s (wfcMiriInit body retTy) [] := by
  refine (StateRel.mk (wfcFrame body retTy) rfl rfl ⟨translateTy retTy, rfl⟩ ?_
    hcal hstack hbor hprot hcaller ?_).toLM3_1
  · refine
      { body_eq := rfl
        location_eq := by rw [hframe0]; rfl
        af_locals_len := by rw [hframe0]; simp
        mf_locals_size := by simp [wfcFrame]
        locals_rel := ?_ }
    intro i decl slot mls hdecl hslot hmls
    rw [hframe0] at hslot
    rw [wfcFrame_locals_getElem?] at hmls
    have hlt : i < body.localDecls.length := by
      refine Decidable.byContradiction fun h => ?_
      simp [h] at hmls
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hmls
    have hs : slot = .uninit := by
      simp only [get?_eq_getElem?, List.getElem?_replicate, hlt, ↓reduceIte,
        Option.some.injEq] at hslot
      exact hslot.symm
    subst hs hmls
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  · intro i j mp_i mp_j lay_i lay_j _ hi _
    rw [wfcFrame_locals_getElem?] at hi
    split at hi
    · simp at hi
    · cases hi

/-- Every local of the single `lean-miri` frame of `m` is immediate (`.dead` or
`.live (.immediate _)`), never memory-backed. -/
def WfcAllImm (m : AnnealStepState) : Prop :=
  ∀ tf, m.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k

theorem wfc_allImm_init (body : CapturedMir) (retTy : Ty) :
    WfcAllImm (wfcMiriInit body retTy) := by
  intro tf htf k mls hmls mp hmp
  injection htf with h₁
  injection h₁ with h₂
  subst h₂
  rw [wfcFrame_locals_getElem?] at hmls
  split at hmls
  · simp only [Option.some.injEq] at hmls
    subst hmls
    cases hmp
  · cases hmls

/-- `lean-miri` local state at program entry: the return place `_0` is live and uninitialized,
every other local is dead until its `StorageLive`. -/
def wfcEntryLocal (i : Nat) : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  if i = 0 then { value := .live (.immediate .uninit), layout := none }
  else { value := .dead, layout := none }

/-- `lean-miri`'s program-entry root frame for an argument-free `body`. -/
def wfcEntryFrame (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { wfcFrame body retTy with
    locals := Array.ofFn (n := body.localDecls.length) fun i => wfcEntryLocal i.val }

/-- `lean-miri`'s program-entry state for an argument-free `body`. -/
def wfcMiriEntry (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[wfcEntryFrame body retTy]⟩, machine := AnnealMachine.empty }

theorem wfcEntryFrame_locals_getElem? (body : CapturedMir) (retTy : Ty) (i : Nat) :
    (wfcEntryFrame body retTy).locals[i]? =
      if i < body.localDecls.length then some (wfcEntryLocal i) else none := by
  simp only [wfcEntryFrame, Array.getElem?_ofFn]
  split <;> rfl

/-- Anneal's program-entry locals of an argument-free body: `_0` uninitialized, the rest dead. -/
def wfcEntrySlots (n : Nat) : List LocalSlot := .uninit :: List.replicate (n - 1) .dead

theorem wfcEntrySlots_get? (n i : Nat) (hi : i < n) :
    get? (wfcEntrySlots n) i = some (if i = 0 then .uninit else .dead) := by
  rcases i with _ | i
  · rfl
  · simp only [wfcEntrySlots, get?_eq_getElem?, List.getElem?_cons_succ,
      List.getElem?_replicate]
    simp
    omega

/-- **Program-entry relation for any argument-free body**: Anneal's `initMachineState body []`
(`_0` uninitialized, every other local dead) and `lean-miri`'s entry state `wfcMiriEntry` are
`StateRelLM3_1`-related with an empty `allocMap`. -/
theorem wfc_stateRel_entry (body : CapturedMir) (retTy : Ty)
    (hcal : (initMachineState body []).memory.activeCallee = none)
    (hstack : (initMachineState body []).memory.callStack = .nil)
    (hbor : (initMachineState body []).memory.borrows = .nil)
    (hprot : (initMachineState body []).memory.activeProtectors = .nil)
    (hcaller : (initMachineState body []).memory.callerLocals = .nil)
    (hframe0 : (initMachineState body []).frame =
      { blockIdx := 0, stmtIdx := 0, locals := wfcEntrySlots body.localDecls.length })
    (hlen : 0 < body.localDecls.length) :
    StateRelLM3_1 body (initMachineState body []) (wfcMiriEntry body retTy) [] := by
  refine (StateRel.mk (wfcEntryFrame body retTy) rfl rfl ⟨translateTy retTy, rfl⟩ ?_
    hcal hstack hbor hprot hcaller ?_).toLM3_1
  · refine
      { body_eq := rfl
        location_eq := by rw [hframe0]; rfl
        af_locals_len := by rw [hframe0]; simp [wfcEntrySlots]; omega
        mf_locals_size := by simp [wfcEntryFrame]
        locals_rel := ?_ }
    intro i decl slot mls hdecl hslot hmls
    rw [hframe0] at hslot
    rw [wfcEntryFrame_locals_getElem?] at hmls
    have hlt : i < body.localDecls.length := by
      refine Decidable.byContradiction fun h => ?_
      simp [h] at hmls
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hmls
    rw [wfcEntrySlots_get? _ _ hlt] at hslot
    subst hmls
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at hslot
      subst hslot
      simp only [wfcEntryLocal, h0, ↓reduceIte]
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · simp only [h0, ↓reduceIte, Option.some.injEq] at hslot
      subst hslot
      simp only [wfcEntryLocal, h0, ↓reduceIte]
      exact .dead none (fun _ h => nomatch h)
  · intro i j mp_i mp_j lay_i lay_j _ hi _
    rw [wfcEntryFrame_locals_getElem?] at hi
    split at hi
    · simp only [wfcEntryLocal, Option.some.injEq] at hi
      split at hi <;> cases hi
    · cases hi

theorem wfc_allImm_entry (body : CapturedMir) (retTy : Ty) :
    WfcAllImm (wfcMiriEntry body retTy) := by
  intro tf htf k mls hmls mp hmp
  injection htf with h₁
  injection h₁ with h₂
  subst h₂
  rw [wfcEntryFrame_locals_getElem?] at hmls
  split at hmls
  · simp only [Option.some.injEq] at hmls
    subst hmls
    unfold wfcEntryLocal at hmp
    split at hmp <;> cases hmp
  · cases hmls

/-- **Lockstep multi-step run** under `annealStepHooksFloat`: both machines take the same number of
normal steps from `(s, m)` to `(s', m')`, every intermediate pair `StateRelLM3_1`-related with an
empty `allocMap` and every `lean-miri` step returning `.ok true`. -/
inductive WfcRun (b : CapturedMir) :
    MachineState → AnnealStepState → MachineState → AnnealStepState → Prop where
  | refl (s : MachineState) (m : AnnealStepState) : WfcRun b s m s m
  | step {s s₁ s' : MachineState} {m m₁ m' : AnnealStepState} :
      stepMirFn b s = .step s₁ →
      Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m₁, .ok true) →
      StateRelLM3_1 b s₁ m₁ [] →
      WfcRun b s₁ m₁ s' m' →
      WfcRun b s m s' m'

/-- `lean-miri` local `k` of the single frame of `m` immediately holds the scalar `msc`
with `ScalarRel sc msc` (`msc.data = BitVec.ofNat 128 sc.bits`,
`msc.size = translateSizeBytes sc.sizeBytes`). -/
def MiriHoldsScalar (m : AnnealStepState) (k : Nat) (sc : MirAst.ScalarInt) : Prop :=
  ∃ tf msc, m.stack.frames = #[tf] ∧
    (tf.locals[k]?).map Miri.Interpreter.LocalState.value =
      some (.live (.immediate (.scalar (.fromScalarInt msc)))) ∧
    ScalarRel sc msc

/-- `lean-miri` local `k` of the single frame of `m` is live and uninitialized. -/
def MiriHoldsUninit (m : AnnealStepState) (k : Nat) : Prop :=
  ∃ tf, m.stack.frames = #[tf] ∧
    (tf.locals[k]?).map Miri.Interpreter.LocalState.value = some (.live (.immediate .uninit))

/-- `lean-miri` local `k` of the single frame of `m` is memory-backed at `stackAllocPlace allocId`,
and the live stack allocation at `allocId` stores a `ScalarRel`-related scalar `msc`
(`inductive` so kernel `isDefEq` compares indices without unfolding `Allocation.readScalar`). -/
inductive MiriHoldsIndirectScalar (m : AnnealStepState) (k : Nat) (allocId : Miri.Memory.AllocId)
    (sc : MirAst.ScalarInt) : Prop where
  | mk (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout)
      (localAlloc :
        Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (msc : Miri.Memory.ScalarInt) :
      m.stack.frames = #[tf] →
      tf.locals[k]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩ →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (.fromScalarInt msc) →
      ScalarRel sc msc →
      MiriHoldsIndirectScalar m k allocId sc

/-- `lean-miri` local `k` of the single frame of `m` is memory-backed at `stackAllocPlace allocId`,
and the live stack allocation at `allocId` is not fully initialized across `sz`. -/
inductive MiriHoldsIndirectUninit (m : AnnealStepState) (k : Nat) (allocId : Miri.Memory.AllocId)
    (sz : Miri.ABI.Size) : Prop where
  | mk (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout)
      (localAlloc :
        Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind) :
      m.stack.frames = #[tf] →
      tf.locals[k]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩ →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) ≠ .ok (.ok ()) →
      MiriHoldsIndirectUninit m k allocId sz

/-- `lean-miri` local `k` of the single frame of `m` has been retired by `StorageDead`: `k` is
`.dead` in the frame and `allocId` is absent from `m.machine.memory.live` (`inductive` so kernel
`isDefEq` never unfolds `Array.find?` over symbolic `m`). -/
inductive MiriPromotedFreed (m : AnnealStepState) (k : Nat) (allocId : Miri.Memory.AllocId) :
    Prop where
  | mk (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
      m.stack.frames = #[tf] →
      (tf.locals[k]?).map Miri.Interpreter.LocalState.value = some .dead →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = none →
      MiriPromotedFreed m k allocId

/-- **Per-local immediate read-back**: in any `StateRelLM3_1`-related pair (with arbitrary
`allocMap`) where local `k` is immediate in `lean-miri`, an Anneal local `k` holding the float /
integer scalar `sc` is mirrored by an immediate `ScalarRel`-related `lean-miri` scalar. -/
theorem wfc_miri_scalar_at {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {k : Nat} (himm_k : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf k)
    {decl : LocalDecl} {sc : MirAst.ScalarInt}
    (hdecl : get? body.localDecls k = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals k = some (.init (.scalar sc))) :
    MiriHoldsScalar m k sc := by
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hslot] at hslot'
  cases hslot'
  rcases hloc.floatCast_immediate_cases hty (himm_k tf hframes mls hmls) with
    ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨sc', msc, hs, hrel, _, hm⟩
  · cases hs
  · cases hs
  · injection hs with hs₁
    injection hs₁ with hs₂
    subst hs₂
    exact ⟨tf, msc, hframes, by rw [hmls]; simp [hm], hrel⟩

/-- **Read-back** under `WfcAllImm`. -/
theorem wfc_miri_scalar {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (himm : WfcAllImm m)
    {k : Nat} {decl : LocalDecl} {sc : MirAst.ScalarInt}
    (hdecl : get? body.localDecls k = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals k = some (.init (.scalar sc))) :
    MiriHoldsScalar m k sc :=
  wfc_miri_scalar_at hstate (fun tf htf => himm tf htf k) hdecl hty hslot

/-- **Per-local uninit read-back**: in any `StateRelLM3_1`-related pair (with arbitrary `allocMap`)
where local `k` is immediate in `lean-miri`, an `.uninit` Anneal local `k` is mirrored by
`.live (.immediate .uninit)` in `lean-miri`. -/
theorem wfc_miri_uninit_at {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {k : Nat} (himm_k : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf k)
    {decl : LocalDecl}
    (hdecl : get? body.localDecls k = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals k = some .uninit) :
    MiriHoldsUninit m k := by
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hslot] at hslot'
  cases hslot'
  rcases hloc.floatCast_immediate_cases hty (himm_k tf hframes mls hmls) with
    ⟨hs, _⟩ | ⟨_, hm⟩ | ⟨sc', msc, hs, _, _, _⟩
  · cases hs
  · exact ⟨tf, hframes, by rw [hmls]; simp [hm]⟩
  · cases hs

/-- **Read-back** of an uninitialized (e.g. moved-from) immediate local under `WfcAllImm`. -/
theorem wfc_miri_uninit {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (himm : WfcAllImm m)
    {k : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls k = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals k = some .uninit) :
    MiriHoldsUninit m k :=
  wfc_miri_uninit_at hstate (fun tf htf => himm tf htf k) hdecl hty hslot

/-- **Read-back of a memory-backed (`LocalRel.indirect`) local**: in any `StateRelLM3_1`-related
pair, if `lean-miri` local `k` points to `stackAllocPlace allocId` with cached base address and
unique live allocation entry, and Anneal local `k` holds `.init (.scalar sc)`, then `lean-miri`'s
stack allocation at `allocId` decodes via `Allocation.readScalar` to a `ScalarRel`-related scalar. -/
theorem wfc_miri_indirect_scalar {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {k : Nat} {decl : LocalDecl} {sc : MirAst.ScalarInt}
    (hdecl : get? body.localDecls k = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals k = some (.init (.scalar sc)))
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hind : ∀ tf, m.stack.frames = #[tf] →
      ∃ lay, tf.locals[k]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩) :
    MiriHoldsIndirectScalar m k allocId sc := by
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨lay, hlay⟩ := hind tf hframes
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hslot] at hslot'
  cases hslot'
  have hmls_eq : mls = ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩ := by
    rw [hmls] at hlay; exact Option.some.inj hlay
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := k, allocId := allocId, perm := .active }
  obtain ⟨_, hsc⟩ := hloc.indirect_stackAllocPlace_spec (e := dummyEntry) hmls_eq hbase hfind huniq
    (hty.size_ne_zero body.layouts)
  obtain ⟨hsz, _, _, msc, hrel, hread⟩ := hsc sc rfl
  rw [hsz] at hread
  exact ⟨tf, lay, localAlloc, msc, hframes, hlay, hfind, hread, hrel⟩

/-- **Read-back of a promoted (`e ∈ allocMap`) scalar local**: `AllocMapRel` supplies the indirect
frame local, base-address lookup, live-allocation lookup, and key uniqueness automatically. -/
theorem wfc_miri_promoted_scalar {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    {decl : LocalDecl} {sc : MirAst.ScalarInt}
    (hdecl : get? body.localDecls e.localIdx = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals e.localIdx = some (.init (.scalar sc))) :
    MiriHoldsIndirectScalar m e.localIdx e.allocId sc := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨⟨lay, hlay⟩, _, hsh⟩ :=
    (halloc.local_alloc_sync tf hframes e he).1 (.init (.scalar sc)) hslot (by simp)
  obtain ⟨localAlloc, hfind, _, _, _⟩ := hsh decl hdecl
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  refine wfc_miri_indirect_scalar hstate hdecl hty hslot hbase hfind
    (halloc.live_key_unique e he) ?_
  intro tf' htf'
  rw [hframes] at htf'
  injection htf' with h₁; injection h₁ with h₂; subst h₂
  exact ⟨lay, hlay⟩

/-- **Read-back of an uninitialized promoted (`e ∈ allocMap`) local**: `lean-miri` local
`e.localIdx` points to `stackAllocPlace e.allocId` whose initialization mask is uninitialized. -/
theorem wfc_miri_promoted_uninit {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    {decl : LocalDecl}
    (hdecl : get? body.localDecls e.localIdx = some decl) (hty : IsFloatCastScalarTy decl.ty)
    (hslot : get? s.frame.locals e.localIdx = some .uninit) :
    MiriHoldsIndirectUninit m e.localIdx e.allocId (translateTy decl.ty body.layouts).layout.size := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨⟨lay, hlay⟩, _, hsh⟩ :=
    (halloc.local_alloc_sync tf hframes e he).1 .uninit hslot (by simp)
  obtain ⟨localAlloc, hfind, _, _, _⟩ := hsh decl hdecl
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hslot] at hslot'
  cases hslot'
  have hmls_eq : mls = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay⟩ := by
    rw [hmls] at hlay; exact Option.some.inj hlay
  obtain ⟨hun, _⟩ := hloc.indirect_stackAllocPlace_spec (e := e) hmls_eq hbase hfind
    (halloc.live_key_unique e he) (hty.size_ne_zero body.layouts)
  exact ⟨tf, lay, localAlloc, hframes, hlay, hfind, hun rfl⟩

/-- **Read-back of a retired (`StorageDead`) promoted (`e ∈ allocMap`) local**: `lean-miri` local
`e.localIdx` is `.dead` in the frame and `e.allocId` has been removed from `m.machine.memory.live`. -/
theorem wfc_miri_promoted_freed {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    (himm_e : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf e.localIdx)
    {decl : LocalDecl}
    (hdecl : get? body.localDecls e.localIdx = some decl)
    (hslot : get? s.frame.locals e.localIdx = some .dead) :
    MiriPromotedFreed m e.localIdx e.allocId := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hslot] at hslot'
  cases hslot'
  cases hloc with
  | base hb =>
    cases hb with
    | dead _ _ =>
      exact ⟨tf, hframes, by rw [hmls]; rfl, (halloc.local_alloc_sync tf hframes e he).2 hslot⟩
    | immediate _ _ _ _ hv => rcases hv with ⟨hs, _⟩ | ⟨_, hs, _⟩ <;> cases hs
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_e tf hframes _ hmls mp)

/-- **One lockstep float-cast step writing `⟨bits, w⟩` into local `k`** under the
refinement-witness hooks `annealStepHooksFloat b.localDecls b.layouts`: Anneal's
`stepMirFn` steps `s ↦ s'`, `lean-miri`'s `Step.step` steps `m ↦ m'` with `.ok true`,
the successors are `StateRelLM3_1`-related (empty `allocMap`), Anneal's local `k`
holds `⟨bits, w⟩`, and `lean-miri`'s local `k` immediately holds a `ScalarRel`-related
scalar. -/
def WfcLockstep (b : CapturedMir) (s s' : MachineState) (m m' : AnnealStepState)
    (k bits w : Nat) : Prop :=
  stepMirFn b s = .step s' ∧
  Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m = (m', .ok true) ∧
  StateRelLM3_1 b s' m' [] ∧
  get? s'.frame.locals k = some (.init (.scalar ⟨bits, w⟩)) ∧
  MiriHoldsScalar m' k ⟨bits, w⟩

/-- **Root-frame return lockstep**: Anneal's `stepMirFn` returns `v` from `s`, and
`lean-miri`'s `Step.step` pops the root frame of `m` (`.ok true`, empty stack) with the
immediate return operand `imm`, `ImmediateRel`-related to `v` at the return type. -/
def WfcReturns (b : CapturedMir) (s : MachineState) (m : AnnealStepState) (v : Value) :
    Prop :=
  (∃ mem, stepMirFn b s = .retNormal v mem) ∧
  Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
    ({ m with stack := ⟨#[]⟩ }, .ok true) ∧
  ∃ decl0 imm, get? b.localDecls 0 = some decl0 ∧
    annealControlHooks.returnOperand () m = (m, .ok (.immediate imm)) ∧
    ImmediateRel decl0.ty b.layouts v imm

/-- **Undefined-behavior lockstep**: Anneal's `stepMirFn` faults with `.ub` from `s`,
`lean-miri`'s `Step.step` reports `.undefinedBehavior` from `m`, and `StepRelLM3_1` relates the two
steps via `StepRelLM3_1.ub`. -/
def WfcUB (b : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry := []) : Prop :=
  stepMirFn b s = .fail .ub ∧
  StepRelLM3_1 b m allocMap (stepMirFn b s)
    (Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m) ∧
  ∃ m' msg, Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
    (m', .error (.undefinedBehavior msg))

theorem wfc_step_of_stepRel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes) (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases hsim with
  | step _ m' hrel =>
    cases ha
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

theorem wfc_ub_of_stepRel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes) (ha : aRes = .fail .ub) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩
  | step _ _ _ => cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha

theorem wfc_ret_of_stepRel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {v : Value} {mem : Memory}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes) (ha : aRes = .retNormal v mem) :
    mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) ∧
    ∃ decl0 imm, get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm)) ∧
      ImmediateRel decl0.ty body.layouts v imm := by
  cases hsim with
  | step _ _ _ => cases ha
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    cases ha
    subst hm'
    exact ⟨rfl, decl0, imm0, hdecl, hop, himm⟩
  | ub _ _ => cases ha

/-- **Constant-operand lockstep step** (`_d = const c as T`), packaging
`step_cast_float_constant_simulation`, `step_cast_float_constant_anyLocal_preserves`, and
the read-back `wfc_miri_scalar`. -/
theorem wfc_step_constant {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty b.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstep b s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hr := step_cast_float_constant_simulation hstate hphase hbb hstmt hdecl_dst hsig hdst_ty
    hval hsz hcan hlaysz (fun tf htf => himm tf htf dstIdx) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_constant_anyLocal_preserves hstate true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => nomatch h) (fun tf htf => Or.inl (himm tf htf dstIdx)) hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Copy-operand lockstep step** (`_d = copy _s as T`). -/
theorem wfc_step_copy {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstep b s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hr := step_cast_float_copy_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsig
    hdst_ty (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_copy_anyLocal_preserves hstate true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty (fun h => nomatch h)
    (fun tf htf => Or.inl (himm tf htf srcIdx)) (fun tf htf => Or.inl (himm tf htf dstIdx))
    hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Move-operand lockstep step** (`_d = move _s as T`, deinitializing `_s`). -/
theorem wfc_step_move {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstep b s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hr := step_cast_float_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsig
    hdst_ty (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_move_anyLocal_preserves hstate true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty (fun h => nomatch h)
    (fun tf htf => himm tf htf srcIdx) (fun tf htf => Or.inl (himm tf htf dstIdx)) hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Copy-operand UB lockstep** (`.dead` / `.uninit` / moved-from `_s`). -/
theorem wfc_ub_copy {b : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    (hs : stepMirFn b s = .fail .ub) : WfcUB b s m := by
  have hr := step_cast_float_copy_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsig
    hdst_ty (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  exact ⟨hs, hr, wfc_ub_of_stepRel hr hs⟩

/-- **Move-operand UB lockstep** (`.dead` / `.uninit` / moved-from `_s`). -/
theorem wfc_ub_move {b : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    (hs : stepMirFn b s = .fail .ub) : WfcUB b s m := by
  have hr := step_cast_float_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsig
    hdst_ty (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  exact ⟨hs, hr, wfc_ub_of_stepRel hr hs⟩

/-- **Root-frame `return` lockstep** under `annealStepHooksFloat` for **arbitrary `allocMap`**,
requiring immediacy only on the return place `_0`: transports
`step_terminator_goto_return_lm3_1_simulation` through `step_float_eq_annealStepHooks_at_terminator`. -/
theorem wfc_step_return_any {b : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 b s m allocMap)
    (himm0 : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf 0)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl} (hdecl0 : get? b.localDecls 0 = some decl0)
    (hty0 : IsFloatCastScalarTy decl0.ty)
    {v : Value} {mem : Memory} (hs : stepMirFn b s = .retNormal v mem) :
    WfcReturns b s m v := by
  have hr := step_terminator_goto_return_lm3_1_simulation hstate hphase hbb hstmt_none hstmt_len
    hcleanup (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hty0.not_rawPtr,
      hty0.size_ne_zero b.layouts, himm0⟩))
  rw [← step_float_eq_annealStepHooks_at_terminator hstate true annealChooseQuietedNaN hbb
    hstmt_none] at hr
  obtain ⟨hm, rest⟩ := wfc_ret_of_stepRel hr hs
  exact ⟨⟨mem, hs⟩, hm, rest⟩

/-- **Root-frame `return` lockstep** specialized to `allocMap = []` and `WfcAllImm`. -/
theorem wfc_step_return {b : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl} (hdecl0 : get? b.localDecls 0 = some decl0)
    (hty0 : IsFloatCastScalarTy decl0.ty)
    {v : Value} {mem : Memory} (hs : stepMirFn b s = .retNormal v mem) :
    WfcReturns b s m v :=
  wfc_step_return_any hstate (fun tf htf => himm tf htf 0) hphase hbb hstmt_none hstmt_len hcleanup
    hret hdecl0 hty0 hs

/-- **`StorageLive` lockstep step** under `annealStepHooksFloat` (conservative extension of
`step_storageLive_lm3_1_simulation`): `lean-miri` makes the local `.live (.immediate .uninit)`,
so every local stays immediate. -/
theorem wfc_step_storageLive {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? b.localDecls loc = some decl)
    (hs : stepMirFn b s = .step s') :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧ StateRelLM3_1 b s' m' [] ∧ WfcAllImm m' := by
  have heq := step_float_eq_annealStepHooks_at_stmt hstate true annealChooseQuietedNaN hbb hstmt
    trivial
  have hr := step_storageLive_lm3_1_simulation hstate hphase hbb hstmt hdecl (fun _ h => nomatch h)
  rw [← heq] at hr
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  refine ⟨m', hm', hrel', ?_⟩
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hty : ∃ ty, tf.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? b loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  rw [heq, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hm'
  injection hm' with hm'1 _
  subst hm'1
  intro tf' htf' k mls' hmls' mp hval
  injection htf' with h1
  injection h1 with h2 _
  subst h2
  simp only [Array.getElem?_set] at hmls'
  split at hmls'
  · injection hmls' with hmls''
    subst hmls''
    cases hval
  · exact himm tf hframes k mls' hmls' mp hval

/-- **`StorageLive` lockstep step preserving `m.machine`** under `WfcAllImm` (`deallocLocalMemory`
is the identity on `.dead` and `.live (.immediate _)`), so `AllocIdSupplyReady.empty` and
`nextAllocId = 1` survive any `StorageLive` prologue from `wfcMiriEntry`. -/
theorem wfc_step_storageLive_mem {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? b.localDecls loc = some decl)
    (hs : stepMirFn b s = .step s') :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧ StateRelLM3_1 b s' m' [] ∧ WfcAllImm m' ∧ m'.machine = m.machine := by
  have heq := step_float_eq_annealStepHooks_at_stmt hstate true annealChooseQuietedNaN hbb hstmt
    trivial
  have hr := step_storageLive_lm3_1_simulation hstate hphase hbb hstmt hdecl (fun _ h => nomatch h)
  rw [← heq] at hr
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hm'_eq := hm'
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hty : ∃ ty, tf.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? b loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  rw [heq, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hm'_eq
  injection hm'_eq with hm'1 _
  subst hm'1
  refine ⟨_, hm', hrel', ?_, ?_⟩
  · intro tf' htf' k mls' hmls' mp hval
    injection htf' with h1
    injection h1 with h2 _
    subst h2
    simp only [Array.getElem?_set] at hmls'
    split at hmls'
    · injection hmls' with hmls''
      subst hmls''
      cases hval
    · exact himm tf hframes k mls' hmls' mp hval
  · dsimp only []
    rw [hmls_eq]
    cases hv : mls.value with
    | dead => rfl
    | live op =>
      cases op with
      | immediate _ => rfl
      | indirect mp => exact False.elim (himm tf hframes loc mls hmls mp hv)

/-- **`StorageDead` lockstep step for arbitrary `allocMap`** (including `&raw`-promoted locals):
disables `allocMap` entries targeting `loc` (`disableAllocMapLocal`, setting `allocDead := true`),
frees any stack allocation owned by `loc` in `lean-miri`, makes `loc` immediate (`.dead`) in
`lean-miri`, and preserves immediacy of every other local. -/
theorem wfc_step_storageDead_any {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 b s m allocMap)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? b.localDecls loc = some decl) (hne0 : loc ≠ 0)
    (hs : stepMirFn b s = .step s') :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_1 b s' m' (disableAllocMapLocal allocMap loc) ∧
      (∀ tf', m'.stack.frames = #[tf'] → IsImmediateFrameLocal tf' loc) ∧
      (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  have heq := step_float_eq_annealStepHooks_at_stmt hstate true annealChooseQuietedNaN hbb hstmt
    trivial
  have hr := step_storageDead_lm3_1_simulation hstate hphase hbb hstmt hdecl hne0
  rw [← heq] at hr
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hm'_eq := hm'
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨_, _, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [heq, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hm'_eq
  injection hm'_eq with hm'1 _
  subst hm'1
  refine ⟨_, hm', hrel', ?_, ?_⟩
  · intro tf' htf' mls' hmls' mp hval
    injection htf' with h1
    injection h1 with h2 _
    subst h2
    simp only [Array.getElem?_set] at hmls'
    split at hmls'
    · injection hmls' with hmls''
      subst hmls''
      cases hval
    · contradiction
  · intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hval
    rw [hframes] at htf₀
    injection htf₀ with h0
    injection h0 with h0' _
    subst h0'
    injection htf' with h1
    injection h1 with h2 _
    subst h2
    simp only [Array.getElem?_set] at hmls'
    split at hmls'
    · injection hmls' with hmls''
      subst hmls''
      cases hval
    · exact hk mls' hmls' mp hval

/-- **`StorageDead` lockstep step** under `annealStepHooksFloat` (conservative extension of
`step_storageDead_lm3_1_simulation`): `lean-miri` makes the local `.dead`, so every local stays
immediate. -/
theorem wfc_step_storageDead {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? b.localDecls loc = some decl) (hne0 : loc ≠ 0)
    (hs : stepMirFn b s = .step s') :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧ StateRelLM3_1 b s' m' [] ∧ WfcAllImm m' := by
  have heq := step_float_eq_annealStepHooks_at_stmt hstate true annealChooseQuietedNaN hbb hstmt
    trivial
  have hr := step_storageDead_lm3_1_simulation hstate hphase hbb hstmt hdecl hne0
  rw [← heq] at hr
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  refine ⟨m', hm', hrel', ?_⟩
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [heq, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hm'
  injection hm' with hm'1 _
  subst hm'1
  intro tf' htf' k mls' hmls' mp hval
  injection htf' with h1
  injection h1 with h2 _
  subst h2
  simp only [Array.getElem?_set] at hmls'
  split at hmls'
  · injection hmls' with hmls''
    subst hmls''
    cases hval
  · exact himm tf hframes k mls' hmls' mp hval

/-! ### Mode-generic (`nondet`, `chooseNaN`) lockstep predicates and step helpers -/

/-- **Mode-generic lockstep multi-step run** under `annealStepHooksFloat b.localDecls b.layouts
nondet chooseNaN` (including deterministic mode `nondet = false` for arbitrary `chooseNaN`). -/
inductive WfcRunMode (b : CapturedMir) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    MachineState → AnnealStepState → MachineState → AnnealStepState → Prop where
  | refl (s : MachineState) (m : AnnealStepState) : WfcRunMode b nondet chooseNaN s m s m
  | step {s s₁ s' : MachineState} {m m₁ m' : AnnealStepState} :
      stepMirFn b s = .step s₁ →
      Miri.Interpreter.Step.step
        (annealStepHooksFloat b.localDecls b.layouts nondet chooseNaN) () m = (m₁, .ok true) →
      StateRelLM3_1 b s₁ m₁ [] →
      WfcRunMode b nondet chooseNaN s₁ m₁ s' m' →
      WfcRunMode b nondet chooseNaN s m s' m'

/-- **Mode-generic single float-cast lockstep step** writing `⟨bits, w⟩` into local `k`. -/
def WfcLockstepMode (b : CapturedMir) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (s s' : MachineState) (m m' : AnnealStepState) (k bits w : Nat) : Prop :=
  stepMirFn b s = .step s' ∧
  Miri.Interpreter.Step.step
    (annealStepHooksFloat b.localDecls b.layouts nondet chooseNaN) () m = (m', .ok true) ∧
  StateRelLM3_1 b s' m' [] ∧
  get? s'.frame.locals k = some (.init (.scalar ⟨bits, w⟩)) ∧
  MiriHoldsScalar m' k ⟨bits, w⟩

/-- **Mode-generic root-frame `return` lockstep**. -/
def WfcReturnsMode (b : CapturedMir) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (s : MachineState) (m : AnnealStepState) (v : Value) : Prop :=
  (∃ mem, stepMirFn b s = .retNormal v mem) ∧
  Miri.Interpreter.Step.step
    (annealStepHooksFloat b.localDecls b.layouts nondet chooseNaN) () m =
      ({ m with stack := ⟨#[]⟩ }, .ok true) ∧
  ∃ decl0 imm, get? b.localDecls 0 = some decl0 ∧
    annealControlHooks.returnOperand () m = (m, .ok (.immediate imm)) ∧
    ImmediateRel decl0.ty b.layouts v imm

/-- The refinement-witness lockstep step `WfcLockstep` *is* the `nondet := true`,
`chooseNaN := annealChooseQuietedNaN` instance of `WfcLockstepMode` (one specification, not two). -/
theorem wfcLockstep_eq_mode (b : CapturedMir) (s s' : MachineState) (m m' : AnnealStepState)
    (k bits w : Nat) :
    WfcLockstep b s s' m m' k bits w =
      WfcLockstepMode b true annealChooseQuietedNaN s s' m m' k bits w := rfl

/-- `WfcReturns` *is* the refinement-witness instance of `WfcReturnsMode`. -/
theorem wfcReturns_eq_mode (b : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (v : Value) : WfcReturns b s m v = WfcReturnsMode b true annealChooseQuietedNaN s m v := rfl

/-- `WfcRun` coincides with the refinement-witness instance of `WfcRunMode`. -/
theorem wfcRun_iff_mode {b : CapturedMir} {s s' : MachineState} {m m' : AnnealStepState} :
    WfcRun b s m s' m' ↔ WfcRunMode b true annealChooseQuietedNaN s m s' m' := by
  constructor
  · intro h
    induction h with
    | refl s m => exact .refl s m
    | step h₁ h₂ h₃ _ ih => exact .step h₁ h₂ h₃ ih
  · intro h
    induction h with
    | refl s m => exact .refl s m
    | step h₁ h₂ h₃ _ ih => exact .step h₁ h₂ h₃ ih

/-- `FloatCastDetAgrees` witness for `.floatToFloat` between concrete `srcTy` / `castTy`. -/
theorem wfc_detAgrees_f2f {srcTy castTy : Ty} {sf df : IeeeFormat} {bits : Nat}
    (hs : ieeeFormatOfTy? srcTy = some sf) (hd : ieeeFormatOfTy? castTy = some df)
    (h : Anneal.Mir.IeeeFloatCast.isNaNBits sf bits = false ∨
      evalFloatToFloatRoundTiesToEven sf df bits = preferredNaNBits df) :
    FloatCastDetAgrees .floatToFloat srcTy castTy bits := by
  intro src dst _ hs' hd'
  rw [hs] at hs'; injection hs' with hs''; subst hs''
  rw [hd] at hd'; injection hd' with hd''; subst hd''
  exact h

/-- **Mode-generic `StorageLive` lockstep step** (routes via `step_float_eq_annealStepHooks_at_stmt`). -/
theorem wfc_step_storageLive_mode {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? b.localDecls loc = some decl)
    (hs : stepMirFn b s = .step s') :
    ∃ m', Miri.Interpreter.Step.step
        (annealStepHooksFloat b.localDecls b.layouts nondet chooseNaN) () m =
      (m', .ok true) ∧ StateRelLM3_1 b s' m' [] ∧ WfcAllImm m' := by
  obtain ⟨m', hm', hrel', himm'⟩ := wfc_step_storageLive hstate himm hphase hbb hstmt hdecl hs
  rw [step_float_eq_annealStepHooks_at_stmt hstate true annealChooseQuietedNaN hbb hstmt trivial,
      ← step_float_eq_annealStepHooks_at_stmt hstate nondet chooseNaN hbb hstmt trivial] at hm'
  exact ⟨m', hm', hrel', himm'⟩

/-- **Mode-generic constant-operand lockstep step** (`_d = const c as T`). -/
theorem wfc_step_constant_mode {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty b.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstepMode b nondet chooseNaN s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hr := step_cast_float_constant_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz hagree
    (fun tf htf => himm tf htf dstIdx) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_constant_anyLocal_preserves hstate nondet chooseNaN hmode
    hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz hagree
    (fun tf htf => Or.inl (himm tf htf dstIdx)) hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Mode-generic copy-operand lockstep step** (`_d = copy _s as T`). -/
theorem wfc_step_copy_mode {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {srcBits srcW : Nat}
    (hsrc_slot : get? s.frame.locals srcIdx = some (.init (.scalar ⟨srcBits, srcW⟩)))
    (hagree : nondet = false → FloatCastDetAgrees kind srcDecl.ty castTy srcBits)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstepMode b nondet chooseNaN s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hag_all : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits := by
    intro hnd sc hsc
    rw [hsrc_slot] at hsc
    cases hsc
    exact hagree hnd
  have hr := step_cast_float_copy_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hag_all
    (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_copy_anyLocal_preserves hstate nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hag_all
    (fun tf htf => Or.inl (himm tf htf srcIdx)) (fun tf htf => Or.inl (himm tf htf dstIdx))
    hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Mode-generic move-operand lockstep step** (`_d = move _s as T`). -/
theorem wfc_step_move_mode {b : CapturedMir} {s s' : MachineState} {m : AnnealStepState}
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    (hstate : StateRelLM3_1 b s m []) (himm : WfcAllImm m)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {srcBits srcW : Nat}
    (hsrc_slot : get? s.frame.locals srcIdx = some (.init (.scalar ⟨srcBits, srcW⟩)))
    (hagree : nondet = false → FloatCastDetAgrees kind srcDecl.ty castTy srcBits)
    (hptr8 : layoutPointerBytes b.layouts = 8)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩))) :
    ∃ m', WfcLockstepMode b nondet chooseNaN s s' m m' dstIdx bits w ∧ WfcAllImm m' := by
  have hag_all : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits := by
    intro hnd sc hsc
    rw [hsrc_slot] at hsc
    cases hsc
    exact hagree hnd
  have hr := step_cast_float_move_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hag_all
    (fun tf htf => ⟨himm tf htf dstIdx, himm tf htf srcIdx⟩) hptr8
  obtain ⟨m', hm', hrel'⟩ := wfc_step_of_stepRel hr hs
  have hp := step_cast_float_move_anyLocal_preserves hstate nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hag_all
    (fun tf htf => himm tf htf srcIdx) (fun tf htf => Or.inl (himm tf htf dstIdx))
    hptr8 m' hm'
  have himm' : WfcAllImm m' := by
    intro tf' htf' k
    obtain ⟨tf, htf, _⟩ := id hstate
    exact hp.2 tf tf' htf htf' k (himm tf htf k)
  exact ⟨m', ⟨hs, hm', hrel', hslot,
    wfc_miri_scalar hrel' himm' hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) hslot⟩, himm'⟩

/-- **Mode-generic root-frame `return` lockstep** for arbitrary `allocMap` (routes via
`step_float_eq_annealStepHooks_at_terminator`). -/
theorem wfc_step_return_mode {b : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hstate : StateRelLM3_1 b s m allocMap)
    (himm0 : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf 0)
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl} (hdecl0 : get? b.localDecls 0 = some decl0)
    (hty0 : IsFloatCastScalarTy decl0.ty)
    {v : Value} {mem : Memory} (hs : stepMirFn b s = .retNormal v mem) :
    WfcReturnsMode b nondet chooseNaN s m v := by
  obtain ⟨hmem, hm, rest⟩ := wfc_step_return_any hstate himm0 hphase hbb hstmt_none hstmt_len
    hcleanup hret hdecl0 hty0 hs
  rw [step_float_eq_annealStepHooks_at_terminator hstate true annealChooseQuietedNaN hbb
        hstmt_none,
      ← step_float_eq_annealStepHooks_at_terminator hstate nondet chooseNaN hbb hstmt_none] at hm
  exact ⟨hmem, hm, rest⟩

/-- `ValidScalarBytes` witnesses. -/
theorem wfcVSB1 : ValidScalarBytes 1 := Or.inl rfl
theorem wfcVSB2 : ValidScalarBytes 2 := Or.inr (Or.inl rfl)
theorem wfcVSB4 : ValidScalarBytes 4 := Or.inr (Or.inr (Or.inl rfl))
theorem wfcVSB8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem wfcVSB16 : ValidScalarBytes 16 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ### Shared types, constants, and body builder -/

/-- `f16`. -/
def wfcF16Ty : Ty := { kind := .float .f16, layoutIdx := 0 }
/-- `f32`. -/
def wfcF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
/-- `f64`. -/
def wfcF64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
/-- `f128`. -/
def wfcF128Ty : Ty := { kind := .float .f128, layoutIdx := 0 }
/-- Signed integer type. -/
def wfcIntTy (it : IntTy) : Ty := { kind := .int it, layoutIdx := 0 }
/-- Unsigned integer type. -/
def wfcUintTy (ut : UintTy) : Ty := { kind := .uint ut, layoutIdx := 0 }
/-- Mutable local of type `ty`. -/
def wfcDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
/-- Scalar constant `⟨bits, sz⟩ : ty`. -/
def wfcConst (ty : Ty) (bits sz : Nat) : ConstOperand :=
  { ty := ty, val := .scalar (.int ⟨bits, sz⟩) }
/-- MIR type for an integer cast target/source `s`. -/
def wfcTargetTy : FloatIntTarget → Ty
  | .signed it => wfcIntTy it
  | .unsigned ut => wfcUintTy ut

/-- MIR type for an IEEE float format `f`. -/
def wfcFmtTy : IeeeFormat → Ty
  | .binary32 => wfcF32Ty
  | .binary64 => wfcF64Ty

/-- Primitive `sz`-byte return layout. -/
def wfcRetLayout (sz : Nat) : TypeLayout :=
  { size := { bytes := sz }, align := { bytes := sz }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Single-basic-block `Runtime(PostCleanup)` body `bb0: stmts; return` with no arguments. -/
def wfcBody (name : String) (decls : List LocalDecl) (retSz : Nat)
    (stmts : List StatementKind) : CapturedMir where
  defPath := name
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := decls
  basicBlocks := [
    { statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi (wfcRetLayout retSz)
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal state of `b` at statement `i` of `bb0` with locals `ls` (float casts never touch
memory, so every intermediate state keeps the entry memory). -/
def wfcAt (b : CapturedMir) (i : Nat) (ls : List LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := i, locals := ls }, memory := (initMachineState b []).memory }

/-! ## (W1) Normal & subnormal `f32 ↔ f64` round trips and halfway ties-to-even -/

/-- **(W1) body** (`_0 : f32` returned; `_1.._4, _8 : f32`; `_5.._7 : f64`):
```text
bb0: StorageLive(_1); …; StorageLive(_8)          // prologue: `_1.._8` live
     _1 = const 0x36A8_0000_0000_0000_f64 as f32  // 1.5·2⁻¹⁴⁹ tie (odd 1) ↦ even 2·2⁻¹⁴⁹
     _2 = const 0x36B4_0000_0000_0000_f64 as f32  // 2.5·2⁻¹⁴⁹ tie (even 2) ↦ 2·2⁻¹⁴⁹
     _3 = const 0x47EF_FFFF_F000_0000_f64 as f32  // f32::MAX + ½ulp ↦ +∞
     _4 = const 0x8000_0000_0000_0000_f64 as f32  // -0.0 ↦ -0.0 (sign kept)
     _5 = copy _1 as f64                          // 2·2⁻¹⁴⁹ = 2⁻¹⁴⁸ widened exactly
     _6 = move _4 as f64                          // -0.0_f32 ↦ -0.0_f64
     _7 = const 0x3DCC_CCCD_f32 as f64            // 0.1_f32 widened exactly
     _8 = move _7 as f32                          // ... and narrowed back exactly
     _0 = move _5 as f32                          // 2⁻¹⁴⁸ narrowed back to the subnormal 0x2
     return
``` -/
def wfcW1Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w1_roundtrip_ties"
    [wfcDecl wfcF32Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty,
     wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl wfcF32Ty] 4
    ([.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
      .storageLive 6, .storageLive 7, .storageLive 8] ++
     [.assign (local_ 1) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x36A8000000000000 8))
      wfcF32Ty),
      .assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x36B4000000000000 8))
      wfcF32Ty),
      .assign (local_ 3) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x47EFFFFFF0000000 8))
      wfcF32Ty),
      .assign (local_ 4) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x8000000000000000 8))
      wfcF32Ty),
      .assign (local_ 5) (.cast .floatToFloat (.copy (local_ 1)) wfcF64Ty),
      .assign (local_ 6) (.cast .floatToFloat (.move (local_ 4)) wfcF64Ty),
      .assign (local_ 7) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x3DCCCCCD 4)) wfcF64Ty),
      .assign (local_ 8) (.cast .floatToFloat (.move (local_ 7)) wfcF32Ty),
      .assign (local_ 0) (.cast .floatToFloat (.move (local_ 5)) wfcF32Ty)])

def wfcW1S0 : MachineState := wfcAt wfcW1Body 0
  [.uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW1S1 : MachineState := wfcAt wfcW1Body 1
  [.uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW1S2 : MachineState := wfcAt wfcW1Body 2
  [.uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW1S3 : MachineState := wfcAt wfcW1Body 3
  [.uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead]
def wfcW1S4 : MachineState := wfcAt wfcW1Body 4
  [.uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead]
def wfcW1S5 : MachineState := wfcAt wfcW1Body 5
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead]
def wfcW1S6 : MachineState := wfcAt wfcW1Body 6
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead]
def wfcW1S7 : MachineState := wfcAt wfcW1Body 7
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead]
def wfcW1S8 : MachineState := wfcAt wfcW1Body 8
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW1S9 : MachineState := wfcAt wfcW1Body 9
  [.uninit, .init (.scalar ⟨2, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW1S10 : MachineState := wfcAt wfcW1Body 10
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit]
def wfcW1S11 : MachineState := wfcAt wfcW1Body 11
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW1S12 : MachineState := wfcAt wfcW1Body 12
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .init (.scalar ⟨0x80000000, 4⟩), .uninit, .uninit, .uninit, .uninit]
def wfcW1S13 : MachineState := wfcAt wfcW1Body 13
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .init (.scalar ⟨0x80000000, 4⟩), .init (.scalar ⟨0x36B0000000000000, 8⟩), .uninit, .uninit,
   .uninit]
def wfcW1S14 : MachineState := wfcAt wfcW1Body 14
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .uninit, .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩),
   .uninit, .uninit]
def wfcW1S15 : MachineState := wfcAt wfcW1Body 15
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .uninit, .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩),
   .init (.scalar ⟨0x3FB99999A0000000, 8⟩), .uninit]
def wfcW1S16 : MachineState := wfcAt wfcW1Body 16
  [.uninit, .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .uninit, .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩),
   .uninit, .init (.scalar ⟨0x3DCCCCCD, 4⟩)]
def wfcW1S17 : MachineState := wfcAt wfcW1Body 17
  [.init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩), .init (.scalar ⟨2, 4⟩),
   .init (.scalar ⟨0x7F800000, 4⟩), .uninit, .uninit, .init (.scalar ⟨0x8000000000000000, 8⟩),
   .uninit, .init (.scalar ⟨0x3DCCCCCD, 4⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW1Body` from program entry (kernel evaluation of `stepMirFn`). -/
theorem wfcW1_anneal_run :
    initMachineState wfcW1Body [] = wfcW1S0 ∧
    stepMirFn wfcW1Body wfcW1S0 = .step wfcW1S1 ∧
    stepMirFn wfcW1Body wfcW1S1 = .step wfcW1S2 ∧
    stepMirFn wfcW1Body wfcW1S2 = .step wfcW1S3 ∧
    stepMirFn wfcW1Body wfcW1S3 = .step wfcW1S4 ∧
    stepMirFn wfcW1Body wfcW1S4 = .step wfcW1S5 ∧
    stepMirFn wfcW1Body wfcW1S5 = .step wfcW1S6 ∧
    stepMirFn wfcW1Body wfcW1S6 = .step wfcW1S7 ∧
    stepMirFn wfcW1Body wfcW1S7 = .step wfcW1S8 ∧
    stepMirFn wfcW1Body wfcW1S8 = .step wfcW1S9 ∧
    stepMirFn wfcW1Body wfcW1S9 = .step wfcW1S10 ∧
    stepMirFn wfcW1Body wfcW1S10 = .step wfcW1S11 ∧
    stepMirFn wfcW1Body wfcW1S11 = .step wfcW1S12 ∧
    stepMirFn wfcW1Body wfcW1S12 = .step wfcW1S13 ∧
    stepMirFn wfcW1Body wfcW1S13 = .step wfcW1S14 ∧
    stepMirFn wfcW1Body wfcW1S14 = .step wfcW1S15 ∧
    stepMirFn wfcW1Body wfcW1S15 = .step wfcW1S16 ∧
    stepMirFn wfcW1Body wfcW1S16 = .step wfcW1S17 ∧
    stepMirFn wfcW1Body wfcW1S17 = .retNormal (.scalar ⟨0x2, 4⟩) wfcW1S17.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW1_stateRel_entry :
    StateRelLM3_1 wfcW1Body wfcW1S0 (wfcMiriEntry wfcW1Body wfcF32Ty) [] := by
  rw [← wfcW1_anneal_run.1]
  exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W1) end-to-end two-sided witness from program entry**: from Anneal's
`initMachineState wfcW1Body []` and `lean-miri`'s entry state `wfcMiriEntry` (`_0` live, every other
local dead), the `StorageLive` prologue runs in `StateRelLM3_1` lockstep (`WfcRun`), and then
Anneal's `stepMirFn` and `lean-miri`'s `Step.step` (`annealStepHooksFloat`) run all nine
`floatToFloat` casts (`.constant` / `.copy` / `.move`) and the root `return` in lockstep, with both
machines holding the IEEE-754 `roundTiesToEven` results bit-for-bit after every step: both
subnormal halfway ties round to the even `0x0000_0002`, `f32::MAX + ½ulp` overflows to `+∞`,
`-0.0` keeps its sign through `f64 → f32 → f64`, and the subnormal `2⁻¹⁴⁸` and `0.1_f32` survive
`f32 → f64 → f32` round trips exactly; the function returns `0x0000_0002_f32` in both machines. -/
theorem wfcW1_end_to_end :
    initMachineState wfcW1Body [] = wfcW1S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcRun wfcW1Body wfcW1S0 (wfcMiriEntry wfcW1Body wfcF32Ty) wfcW1S8 mₚ ∧
      WfcLockstep wfcW1Body wfcW1S8 wfcW1S9 mₚ m₁ 1 2 4 ∧
      WfcLockstep wfcW1Body wfcW1S9 wfcW1S10 m₁ m₂ 2 2 4 ∧
      WfcLockstep wfcW1Body wfcW1S10 wfcW1S11 m₂ m₃ 3 0x7F800000 4 ∧
      WfcLockstep wfcW1Body wfcW1S11 wfcW1S12 m₃ m₄ 4 0x80000000 4 ∧
      WfcLockstep wfcW1Body wfcW1S12 wfcW1S13 m₄ m₅ 5 0x36B0000000000000 8 ∧
      WfcLockstep wfcW1Body wfcW1S13 wfcW1S14 m₅ m₆ 6 0x8000000000000000 8 ∧
      MiriHoldsUninit m₆ 4 ∧
      WfcLockstep wfcW1Body wfcW1S14 wfcW1S15 m₆ m₇ 7 0x3FB99999A0000000 8 ∧
      WfcLockstep wfcW1Body wfcW1S15 wfcW1S16 m₇ m₈ 8 0x3DCCCCCD 4 ∧
      MiriHoldsUninit m₈ 7 ∧
      WfcLockstep wfcW1Body wfcW1S16 wfcW1S17 m₈ m₉ 0 2 4 ∧
      MiriHoldsUninit m₉ 5 ∧
      WfcReturns wfcW1Body wfcW1S17 m₉ (.scalar ⟨0x2, 4⟩) := by
  have hph : ∀ p, wfcW1Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    hret⟩ := wfcW1_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive wfcW1_stateRel_entry (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ :=
    wfc_step_storageLive r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ :=
    wfc_step_storageLive r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ :=
    wfc_step_storageLive r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ :=
    wfc_step_storageLive r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨p₆, e₆, r₆, q₆⟩ :=
    wfc_step_storageLive r₅ q₅ hph rfl rfl rfl h6
  obtain ⟨p₇, e₇, r₇, q₇⟩ :=
    wfc_step_storageLive r₆ q₆ hph rfl rfl rfl h7
  obtain ⟨p₈, e₈, r₈, q₈⟩ :=
    wfc_step_storageLive r₇ q₇ hph rfl rfl rfl h8
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₈ q₈ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h9 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h10 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h11 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h12 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_copy l₄.2.2.1 i₄ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h13 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_move l₅.2.2.1 i₅ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h14 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h15 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_move l₇.2.2.1 i₇ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h16 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_move l₈.2.2.1 i₈ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h17 rfl
  have hrun : WfcRun wfcW1Body wfcW1S0 (wfcMiriEntry wfcW1Body wfcF32Ty) wfcW1S8 p₈ :=
    (.step h1 e₁ r₁
      (.step h2 e₂ r₂
      (.step h3 e₃ r₃
      (.step h4 e₄ r₄
      (.step h5 e₅ r₅
      (.step h6 e₆ r₆
      (.step h7 e₇ r₇
      (.step h8 e₈ r₈ (.refl _ _)))))))))
  exact ⟨h0, p₈, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, hrun, l₁, l₂, l₃, l₄, l₅, l₆,
    wfc_miri_uninit l₆.2.2.1 i₆ rfl (Or.inl ⟨_, rfl⟩) rfl, l₇, l₈,
    wfc_miri_uninit l₈.2.2.1 i₈ rfl (Or.inl ⟨_, rfl⟩) rfl, l₉,
    wfc_miri_uninit l₉.2.2.1 i₉ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₉.2.2.1 i₉ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-- **(W1) multi-step deterministic-mode (`floatNondeterministic := false`) lockstep witness from
program entry, for every `chooseNaN`**: because every float source in `wfcW1Body` is non-NaN, all
18 steps (`StorageLive(_1.._8)`, 9 `.constant` / `.copy` / `.move` `f32 ↔ f64` casts, and `return`)
execute in `StateRelLM3_1` lockstep under `annealStepHooksFloat ... false chooseNaN` regardless of
`chooseNaN`. -/
theorem wfcW1_deterministic_end_to_end
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    initMachineState wfcW1Body [] = wfcW1S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcRunMode wfcW1Body false chooseNaN wfcW1S0 (wfcMiriEntry wfcW1Body wfcF32Ty) wfcW1S8 mₚ ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S8 wfcW1S9 mₚ m₁ 1 2 4 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S9 wfcW1S10 m₁ m₂ 2 2 4 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S10 wfcW1S11 m₂ m₃ 3 0x7F800000 4 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S11 wfcW1S12 m₃ m₄ 4 0x80000000 4 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S12 wfcW1S13 m₄ m₅ 5 0x36B0000000000000 8 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S13 wfcW1S14 m₅ m₆ 6 0x8000000000000000 8 ∧
      MiriHoldsUninit m₆ 4 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S14 wfcW1S15 m₆ m₇ 7 0x3FB99999A0000000 8 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S15 wfcW1S16 m₇ m₈ 8 0x3DCCCCCD 4 ∧
      MiriHoldsUninit m₈ 7 ∧
      WfcLockstepMode wfcW1Body false chooseNaN wfcW1S16 wfcW1S17 m₈ m₉ 0 2 4 ∧
      MiriHoldsUninit m₉ 5 ∧
      WfcReturnsMode wfcW1Body false chooseNaN wfcW1S17 m₉ (.scalar ⟨0x2, 4⟩) := by
  have hph : ∀ p, wfcW1Body.phase ≠ .other p := fun _ h => nomatch h
  have hmd : FloatNaNModeOk false chooseNaN := Or.inr rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    hret⟩ := wfcW1_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive_mode false chooseNaN wfcW1_stateRel_entry (wfc_allImm_entry _ _) hph
      rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ := wfc_step_storageLive_mode false chooseNaN r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ := wfc_step_storageLive_mode false chooseNaN r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ := wfc_step_storageLive_mode false chooseNaN r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ := wfc_step_storageLive_mode false chooseNaN r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨p₆, e₆, r₆, q₆⟩ := wfc_step_storageLive_mode false chooseNaN r₅ q₅ hph rfl rfl rfl h6
  obtain ⟨p₇, e₇, r₇, q₇⟩ := wfc_step_storageLive_mode false chooseNaN r₆ q₆ hph rfl rfl rfl h7
  obtain ⟨p₈, e₈, r₈, q₈⟩ := wfc_step_storageLive_mode false chooseNaN r₇ q₇ hph rfl rfl rfl h8
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant_mode false chooseNaN hmd r₈ q₈ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h9 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant_mode false chooseNaN hmd l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h10 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant_mode false chooseNaN hmd l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h11 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant_mode false chooseNaN hmd l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h12 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_copy_mode false chooseNaN hmd l₄.2.2.1 i₄ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h13 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_move_mode false chooseNaN hmd l₅.2.2.1 i₅ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h14 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant_mode false chooseNaN hmd l₆.2.2.1 i₆ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h15 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_move_mode false chooseNaN hmd l₇.2.2.1 i₇ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h16 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_move_mode false chooseNaN hmd l₈.2.2.1 i₈ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl h17 rfl
  have hrun : WfcRunMode wfcW1Body false chooseNaN wfcW1S0 (wfcMiriEntry wfcW1Body wfcF32Ty)
      wfcW1S8 p₈ :=
    (.step h1 e₁ r₁ (.step h2 e₂ r₂ (.step h3 e₃ r₃ (.step h4 e₄ r₄
      (.step h5 e₅ r₅ (.step h6 e₆ r₆ (.step h7 e₇ r₇ (.step h8 e₈ r₈ (.refl _ _)))))))))
  exact ⟨h0, p₈, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, hrun, l₁, l₂, l₃, l₄, l₅, l₆,
    wfc_miri_uninit l₆.2.2.1 i₆ rfl (Or.inl ⟨_, rfl⟩) rfl, l₇, l₈,
    wfc_miri_uninit l₈.2.2.1 i₈ rfl (Or.inl ⟨_, rfl⟩) rfl, l₉,
    wfc_miri_uninit l₉.2.2.1 i₉ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return_mode false chooseNaN l₉.2.2.1 (fun tf htf => i₉ tf htf 0) hph
      rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-! ### (W1) Two-sided `f32 ↔ f64` conversion class table at the primitives -/

/-- **Two-sided** float-to-float bit pattern: `lean-miri`'s `FloatBits.convert` (the primitive
behind `Cast.cast .FloatToFloat`) and Anneal's `evalFloatCast .floatToFloat` both produce any closed
form `V` of `evalFloatToFloatRoundTiesToEven` (`floatBits_convert_eq`). -/
theorem wfc_convert (src dst : IeeeFormat) (bits : Nat) (h : bits < 2 ^ src.width) (V : Nat)
    (hv : evalFloatToFloatRoundTiesToEven src dst bits = V) :
    Miri.Interpreter.FloatBits.convert ⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩
        (ieeeFormatToMiri dst) = .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 V⟩ ∧
    evalFloatCast .floatToFloat (some (wfcFmtTy src)) (wfcFmtTy dst) emptyLayoutTable
        (.scalar ⟨bits, src.byteWidth⟩) = some (.scalar ⟨V, dst.byteWidth⟩) := by
  refine ⟨by rw [floatBits_convert_eq src dst bits h, hv], ?_⟩
  subst hv
  cases src <;> cases dst <;> rfl

/-- **(W1) two-sided `roundTiesToEven` `f64 → f32` / `f32 → f64` class table**: `lean-miri`'s
`FloatBits.convert` **and** Anneal's `evalFloatCast .floatToFloat` agree bit-for-bit on signed
zeros, gradual underflow (the least `f64` subnormal flushes to `+0.0`; `2⁻¹⁵⁰` is a tie that rounds
to the even `+0.0`, while one ulp above it rounds up to the least `f32` subnormal), the subnormal
ties `1.5·2⁻¹⁴⁹` / `2.5·2⁻¹⁴⁹ ↦ 0x2`, rounding the largest-subnormal neighbourhood up to the least
normal, `π`, `f32::MAX` exactly, the `f32::MAX + ½ulp` tie overflowing to `±∞` (sign-symmetric)
while one `f64` ulp below it stays at `f32::MAX`, `±∞`, and the quiet NaN; and on every exact
`f32 → f64` widening (signed zeros, least / largest subnormal, least normal, `1.0`, `f32::MAX`,
`±∞`, a signaling payload NaN quieted to `0x7FF8_0000_2000_0000`, and the negative quiet NaN). -/
theorem wfcW1_convert_table :
    let both (src dst : IeeeFormat) (bits V : Nat) :=
      Miri.Interpreter.FloatBits.convert ⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩
          (ieeeFormatToMiri dst) = .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 V⟩ ∧
        evalFloatCast .floatToFloat (some (wfcFmtTy src)) (wfcFmtTy dst) emptyLayoutTable
          (.scalar ⟨bits, src.byteWidth⟩) = some (.scalar ⟨V, dst.byteWidth⟩)
    both .binary64 .binary32 0x0000000000000000 0x00000000 ∧
    both .binary64 .binary32 0x8000000000000000 0x80000000 ∧
    both .binary64 .binary32 0x0000000000000001 0x00000000 ∧
    both .binary64 .binary32 0x3690000000000000 0x00000000 ∧
    both .binary64 .binary32 0x3690000000000001 0x00000001 ∧
    both .binary64 .binary32 0x36A0000000000000 0x00000001 ∧
    both .binary64 .binary32 0x36A8000000000000 0x00000002 ∧
    both .binary64 .binary32 0x36B4000000000000 0x00000002 ∧
    both .binary64 .binary32 0x380FFFFFE0000000 0x00800000 ∧
    both .binary64 .binary32 0x3FF0000000000000 0x3F800000 ∧
    both .binary64 .binary32 0x400921FB54442D18 0x40490FDB ∧
    both .binary64 .binary32 0x47EFFFFFE0000000 0x7F7FFFFF ∧
    both .binary64 .binary32 0x47EFFFFFEFFFFFFF 0x7F7FFFFF ∧
    both .binary64 .binary32 0x47EFFFFFF0000000 0x7F800000 ∧
    both .binary64 .binary32 0xC7EFFFFFF0000000 0xFF800000 ∧
    both .binary64 .binary32 0x7FF0000000000000 0x7F800000 ∧
    both .binary64 .binary32 0xFFF0000000000000 0xFF800000 ∧
    both .binary64 .binary32 0x7FF8000000000000 0x7FC00000 ∧
    both .binary32 .binary64 0x00000000 0x0000000000000000 ∧
    both .binary32 .binary64 0x80000000 0x8000000000000000 ∧
    both .binary32 .binary64 0x00000001 0x36A0000000000000 ∧
    both .binary32 .binary64 0x007FFFFF 0x380FFFFFC0000000 ∧
    both .binary32 .binary64 0x00800000 0x3810000000000000 ∧
    both .binary32 .binary64 0x3F800000 0x3FF0000000000000 ∧
    both .binary32 .binary64 0x7F7FFFFF 0x47EFFFFFE0000000 ∧
    both .binary32 .binary64 0x7F800000 0x7FF0000000000000 ∧
    both .binary32 .binary64 0xFF800000 0xFFF0000000000000 ∧
    both .binary32 .binary64 0x7F800001 0x7FF8000020000000 ∧
    both .binary32 .binary64 0xFFC00000 0xFFF8000000000000 := by
  intro both
  exact ⟨wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel),
    wfc_convert _ _ _ (by decide) _ (by decide +kernel)⟩

/-! ## (W2) Signaling-NaN quietization, `nanChoices` membership, and NaN-choice refinement -/

/-- **(W2) body** (`_0, _1 : f64`; `_2.._5 : f32`):
```text
bb0: StorageLive(_1); …; StorageLive(_5)           // prologue: `_1.._5` live
     _1 = const 0x7F80_0001_f32 as f64             // sNaN ↦ quiet 0x7FF8_0000_2000_0000
     _2 = const 0x7FF0_0000_0000_0001_f64 as f32   // sNaN, payload < bit 29 ↦ 0x7FC0_0000
     _3 = const 0x7FF0_0000_2000_0001_f64 as f32   // sNaN, payload kept ↦ 0x7FC0_0001
     _5 = const 0xFFF0_0000_2000_0001_f64 as f32   // negative sNaN ↦ 0xFFC0_0001
     _4 = copy _1 as f32                           // quiet payload NaN ↦ 0x7FC0_0001
     _0 = move _4 as f64                           // ... ↦ 0x7FF8_0000_2000_0000
     return
``` -/
def wfcW2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_nan_quietization"
    [wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty,
     wfcDecl wfcF32Ty] 8
    ([.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5] ++
     [.assign (local_ 1) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x7F800001 4)) wfcF64Ty),
      .assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000000000001 8))
      wfcF32Ty),
      .assign (local_ 3) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000020000001 8))
      wfcF32Ty),
      .assign (local_ 5) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0xFFF0000020000001 8))
      wfcF32Ty),
      .assign (local_ 4) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty),
      .assign (local_ 0) (.cast .floatToFloat (.move (local_ 4)) wfcF64Ty)])

def wfcW2S0 : MachineState := wfcAt wfcW2Body 0
  [.uninit, .dead, .dead, .dead, .dead, .dead]
def wfcW2S1 : MachineState := wfcAt wfcW2Body 1
  [.uninit, .uninit, .dead, .dead, .dead, .dead]
def wfcW2S2 : MachineState := wfcAt wfcW2Body 2
  [.uninit, .uninit, .uninit, .dead, .dead, .dead]
def wfcW2S3 : MachineState := wfcAt wfcW2Body 3
  [.uninit, .uninit, .uninit, .uninit, .dead, .dead]
def wfcW2S4 : MachineState := wfcAt wfcW2Body 4
  [.uninit, .uninit, .uninit, .uninit, .uninit, .dead]
def wfcW2S5 : MachineState := wfcAt wfcW2Body 5
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW2S6 : MachineState := wfcAt wfcW2Body 6
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .uninit, .uninit, .uninit, .uninit]
def wfcW2S7 : MachineState := wfcAt wfcW2Body 7
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩), .uninit,
   .uninit, .uninit]
def wfcW2S8 : MachineState := wfcAt wfcW2Body 8
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .uninit, .uninit]
def wfcW2S9 : MachineState := wfcAt wfcW2Body 9
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .uninit, .init (.scalar ⟨0xFFC00001, 4⟩)]
def wfcW2S10 : MachineState := wfcAt wfcW2Body 10
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .init (.scalar ⟨0x7FC00001, 4⟩),
   .init (.scalar ⟨0xFFC00001, 4⟩)]
def wfcW2S11 : MachineState := wfcAt wfcW2Body 11
  [.init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FF8000020000000, 8⟩),
   .init (.scalar ⟨0x7FC00000, 4⟩), .init (.scalar ⟨0x7FC00001, 4⟩), .uninit,
   .init (.scalar ⟨0xFFC00001, 4⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW2Body` from program entry (kernel evaluation of `stepMirFn`). -/
theorem wfcW2_anneal_run :
    initMachineState wfcW2Body [] = wfcW2S0 ∧
    stepMirFn wfcW2Body wfcW2S0 = .step wfcW2S1 ∧
    stepMirFn wfcW2Body wfcW2S1 = .step wfcW2S2 ∧
    stepMirFn wfcW2Body wfcW2S2 = .step wfcW2S3 ∧
    stepMirFn wfcW2Body wfcW2S3 = .step wfcW2S4 ∧
    stepMirFn wfcW2Body wfcW2S4 = .step wfcW2S5 ∧
    stepMirFn wfcW2Body wfcW2S5 = .step wfcW2S6 ∧
    stepMirFn wfcW2Body wfcW2S6 = .step wfcW2S7 ∧
    stepMirFn wfcW2Body wfcW2S7 = .step wfcW2S8 ∧
    stepMirFn wfcW2Body wfcW2S8 = .step wfcW2S9 ∧
    stepMirFn wfcW2Body wfcW2S9 = .step wfcW2S10 ∧
    stepMirFn wfcW2Body wfcW2S10 = .step wfcW2S11 ∧
    stepMirFn wfcW2Body wfcW2S11 = .retNormal (.scalar ⟨0x7FF8000020000000, 8⟩) wfcW2S11.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW2_stateRel_entry :
    StateRelLM3_1 wfcW2Body wfcW2S0 (wfcMiriEntry wfcW2Body wfcF64Ty) [] := by
  rw [← wfcW2_anneal_run.1]
  exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W2) end-to-end two-sided NaN witness from program entry**: after the `StorageLive`
prologue (`WfcRun` from `initMachineState` / `wfcMiriEntry`), Anneal's `stepMirFn` and
`lean-miri`'s `Step.step` (`annealStepHooksFloat`, nondeterministic NaN mode with the refinement
selector `annealChooseQuietedNaN`) run `wfcW2Body` in `StateRelLM3_1` lockstep: the signaling
`0x7F80_0001_f32` is quieted to `0x7FF8_0000_2000_0000_f64` (payload kept), the signaling
`0x7FF0_0000_0000_0001_f64` narrows to the canonical quiet `0x7FC0_0000_f32` (payload below bit
29 dropped), the payload-preserving `0x7FF0_0000_2000_0001_f64` narrows to `0x7FC0_0001_f32`, the
negative `0xFFF0_0000_2000_0001_f64` keeps its sign (`0xFFC0_0001_f32`), and the quiet payload NaN
round-trips `f64 → f32 → f64`; the function returns `0x7FF8_0000_2000_0000_f64` in both
machines. -/
theorem wfcW2_end_to_end :
    initMachineState wfcW2Body [] = wfcW2S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState,
      WfcRun wfcW2Body wfcW2S0 (wfcMiriEntry wfcW2Body wfcF64Ty) wfcW2S5 mₚ ∧
      WfcLockstep wfcW2Body wfcW2S5 wfcW2S6 mₚ m₁ 1 0x7FF8000020000000 8 ∧
      WfcLockstep wfcW2Body wfcW2S6 wfcW2S7 m₁ m₂ 2 0x7FC00000 4 ∧
      WfcLockstep wfcW2Body wfcW2S7 wfcW2S8 m₂ m₃ 3 0x7FC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S8 wfcW2S9 m₃ m₄ 5 0xFFC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S9 wfcW2S10 m₄ m₅ 4 0x7FC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S10 wfcW2S11 m₅ m₆ 0 0x7FF8000020000000 8 ∧
      MiriHoldsUninit m₆ 4 ∧
      WfcReturns wfcW2Body wfcW2S11 m₆ (.scalar ⟨0x7FF8000020000000, 8⟩) := by
  have hph : ∀ p, wfcW2Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hret⟩ := wfcW2_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive wfcW2_stateRel_entry (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ :=
    wfc_step_storageLive r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ :=
    wfc_step_storageLive r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ :=
    wfc_step_storageLive r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ :=
    wfc_step_storageLive r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₅ q₅ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h6 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h7 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h8 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h9 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_copy l₄.2.2.1 i₄ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h10 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_move l₅.2.2.1 i₅ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h11 rfl
  have hrun : WfcRun wfcW2Body wfcW2S0 (wfcMiriEntry wfcW2Body wfcF64Ty) wfcW2S5 p₅ :=
    (.step h1 e₁ r₁
      (.step h2 e₂ r₂
      (.step h3 e₃ r₃
      (.step h4 e₄ r₄
      (.step h5 e₅ r₅ (.refl _ _))))))
  exact ⟨h0, p₅, m₁, m₂, m₃, m₄, m₅, m₆, hrun, l₁, l₂, l₃, l₄, l₅, l₆,
    wfc_miri_uninit l₆.2.2.1 i₆ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₆.2.2.1 i₆ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-! ### (W2) Deterministic NaN mode, explicit NaN-choice selectors, and exact candidate lists -/

/-- **(W2) deterministic-mode body** `bb0: _0 = const 0x7F80_0001_f32 as f64; return`
(`_0 : f64` is its only local, so its program-entry state needs no `StorageLive` prologue). -/
def wfcW2DetBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_nan_deterministic" [wfcDecl wfcF64Ty] 8
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x7F800001 4)) wfcF64Ty)]

def wfcW2DetS0 : MachineState := wfcAt wfcW2DetBody 0 [.uninit]
def wfcW2DetS1 : MachineState := wfcAt wfcW2DetBody 1 [.init (.scalar ⟨0x7FF8000020000000, 8⟩)]

theorem wfcW2Det_stateRel_entry :
    StateRelLM3_1 wfcW2DetBody wfcW2DetS0 (wfcMiriEntry wfcW2DetBody wfcF64Ty) [] :=
  wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W2) deterministic-mode (`floatNondeterministic := false`) canonicalization from program
entry** on `wfcW2DetBody` (`_0 = const 0x7F80_0001_f32 as f64`), for **every** `chooseNaN`: Anneal
steps to `wfcW2DetS1` (storing the quieted `0x7FF8_0000_2000_0000`), while `lean-miri` steps and
stores the canonical `preferredNaNBits .binary64 = 0x7FF8_0000_0000_0000` in `_0`; the Anneal
successor storing that canonical NaN is `StepRelLM3_1`-related to `lean-miri`'s step (simulation
modulo NaN canonicalization), and **no** `StepRelLM3_1` relates the real Anneal step to it. In
contrast, `wfcW2_end_to_end` keeps both machines in lockstep under the refinement selector
`annealChooseQuietedNaN`. -/
theorem wfcW2_deterministic_canonicalization
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    let hooksDet := annealStepHooksFloat wfcW2DetBody.localDecls wfcW2DetBody.layouts false chooseNaN
    let m₀ := wfcMiriEntry wfcW2DetBody wfcF64Ty
    initMachineState wfcW2DetBody [] = wfcW2DetS0 ∧
    stepMirFn wfcW2DetBody wfcW2DetS0 = .step wfcW2DetS1 ∧
    (∃ m', Miri.Interpreter.Step.step hooksDet () m₀ = (m', .ok true) ∧
      MiriHoldsScalar m' 0 ⟨0x7FF8000000000000, 8⟩) ∧
    StepRelLM3_1 wfcW2DetBody m₀ []
      (.step (wfcAt wfcW2DetBody 1 [.init (.scalar ⟨0x7FF8000000000000, 8⟩)]))
      (Miri.Interpreter.Step.step hooksDet () m₀) ∧
    ¬ StepRelLM3_1 wfcW2DetBody m₀ [] (stepMirFn wfcW2DetBody wfcW2DetS0)
      (Miri.Interpreter.Step.step hooksDet () m₀) := by
  intro hooksDet m₀
  have himm₀ : ∀ tf, m₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => wfc_allImm_entry _ _ tf htf 0
  have hnan : Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7F800001 = true := rfl
  have hev : evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7F800001 =
      0x7FF8000020000000 := rfl
  have hpref : preferredNaNBits .binary64 = 0x7FF8000000000000 := rfl
  have hspec := step_cast_floatToFloat_constant_deterministic_spec wfcW2Det_stateRel_entry
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀
  dsimp only at hspec
  simp only [hev, hnan, ↓reduceIte, hpref] at hspec
  obtain ⟨m', tf', msc', hrel', _, hm', htf', hval'⟩ := hspec
  have hsim := (step_cast_floatToFloat_constant_deterministic_simulation wfcW2Det_stateRel_entry
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀).2
  simp only [hnan, ↓reduceIte, hpref] at hsim
  refine ⟨rfl, rfl, ⟨m', hm', tf', msc', htf', hval', hrel'⟩, hsim, fun hstep => ?_⟩
  have hag := (step_cast_floatToFloat_constant_deterministic_lockstep_iff wfcW2Det_stateRel_entry
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀).mp hstep
  rw [hnan, hev, hpref] at hag
  rcases hag with h | h
  · cases h
  · exact absurd h (by decide)

/-- **(W2) deterministic-mode lockstep bodies** (single local `_0`, so no prologue):
* `wfcW2DetNBody`: `_0 = const 1.5_f32 as f64; return` (non-NaN).
* `wfcW2DetQBody`: `_0 = const 0x7FC0_0000_f32 as f64; return` (canonical quiet NaN).
* `wfcW2DetSNaNTruncBody`: `_0 = const 0x7FF0_0000_0000_0001_f64 as f32; return` (a **signaling
  payload NaN** — NOT `preferredNaN` in `f64`! — whose quieted `f32` conversion drops bit `0` below
  bit 29 and lands on `preferredNaNBits .binary32 = 0x7FC0_0000`, satisfying `FloatCastDetAgrees`'s
  second disjunct!). -/
def wfcW2DetNBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_det_non_nan" [wfcDecl wfcF64Ty] 8
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x3FC00000 4)) wfcF64Ty)]

/-- See `wfcW2DetNBody`. -/
def wfcW2DetQBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_det_canonical_nan" [wfcDecl wfcF64Ty] 8
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x7FC00000 4)) wfcF64Ty)]

/-- See `wfcW2DetNBody`. -/
def wfcW2DetSNaNTruncBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_det_snan_trunc_canonical" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat
      (.constant (wfcConst wfcF64Ty 0x7FF0000000000001 8)) wfcF32Ty)]

/-- Contrast for `wfcW2DetSNaNTruncBody`: `_0 = const 0x7FF0_0000_2000_0001_f64 as f32; return`
(payload bit `29` survives narrowing to `0x7FC0_0001 ≠ preferredNaNBits .binary32`). -/
def wfcW2DetSNaNKeepBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_det_snan_keep_payload" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat
      (.constant (wfcConst wfcF64Ty 0x7FF0000020000001 8)) wfcF32Ty)]

/-- **(W2) tightness of deterministic-mode lockstep from program entry through `return`, for every
`chooseNaN`**: under `floatNondeterministic := false`, both machines step in `StateRelLM3_1`
lockstep **and** return the identical scalar (`WfcReturnsMode`) on:
1. non-NaNs (`1.5_f32 ↦ 0x3FF8_0000_0000_0000_f64`),
2. canonical quiet NaNs (`0x7FC0_0000_f32 ↦ 0x7FF8_0000_0000_0000_f64`), and
3. signaling payload NaNs whose narrowed payload truncates away to `preferredNaNBits`
   (`0x7FF0_0000_0000_0001_f64 ↦ 0x7FC0_0000_f32`, with `isSignaling = .ok true` on the input);
whereas payload-preserving sNaNs in **both** directions (`0x7F80_0001_f32 as f64` in `wfcW2DetBody`
and `0x7FF0_0000_2000_0001_f64 as f32` in `wfcW2DetSNaNKeepBody`) break `StepRelLM3_1` lockstep. -/
theorem wfcW2_deterministic_lockstep_cases
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    let hd (b : CapturedMir) := annealStepHooksFloat b.localDecls b.layouts false chooseNaN
    (∃ m',
      WfcLockstepMode wfcW2DetNBody false chooseNaN
        (initMachineState wfcW2DetNBody [])
        (wfcAt wfcW2DetNBody 1 [.init (.scalar ⟨0x3FF8000000000000, 8⟩)])
        (wfcMiriEntry wfcW2DetNBody wfcF64Ty) m' 0 0x3FF8000000000000 8 ∧
      WfcReturnsMode wfcW2DetNBody false chooseNaN
        (wfcAt wfcW2DetNBody 1 [.init (.scalar ⟨0x3FF8000000000000, 8⟩)]) m'
        (.scalar ⟨0x3FF8000000000000, 8⟩)) ∧
    (∃ m',
      WfcLockstepMode wfcW2DetQBody false chooseNaN
        (initMachineState wfcW2DetQBody [])
        (wfcAt wfcW2DetQBody 1 [.init (.scalar ⟨0x7FF8000000000000, 8⟩)])
        (wfcMiriEntry wfcW2DetQBody wfcF64Ty) m' 0 0x7FF8000000000000 8 ∧
      WfcReturnsMode wfcW2DetQBody false chooseNaN
        (wfcAt wfcW2DetQBody 1 [.init (.scalar ⟨0x7FF8000000000000, 8⟩)]) m'
        (.scalar ⟨0x7FF8000000000000, 8⟩)) ∧
    Miri.Interpreter.FloatBits.isSignaling
        ⟨ieeeFormatToMiri .binary64, BitVec.ofNat 128 0x7FF0000000000001⟩ = .ok true ∧
    (∃ m',
      WfcLockstepMode wfcW2DetSNaNTruncBody false chooseNaN
        (initMachineState wfcW2DetSNaNTruncBody [])
        (wfcAt wfcW2DetSNaNTruncBody 1 [.init (.scalar ⟨0x7FC00000, 4⟩)])
        (wfcMiriEntry wfcW2DetSNaNTruncBody wfcF32Ty) m' 0 0x7FC00000 4 ∧
      WfcReturnsMode wfcW2DetSNaNTruncBody false chooseNaN
        (wfcAt wfcW2DetSNaNTruncBody 1 [.init (.scalar ⟨0x7FC00000, 4⟩)]) m'
        (.scalar ⟨0x7FC00000, 4⟩)) ∧
    ¬ StepRelLM3_1 wfcW2DetBody (wfcMiriEntry wfcW2DetBody wfcF64Ty) []
        (stepMirFn wfcW2DetBody (initMachineState wfcW2DetBody []))
        (Miri.Interpreter.Step.step (hd wfcW2DetBody) () (wfcMiriEntry wfcW2DetBody wfcF64Ty)) ∧
    ¬ StepRelLM3_1 wfcW2DetSNaNKeepBody (wfcMiriEntry wfcW2DetSNaNKeepBody wfcF32Ty) []
        (stepMirFn wfcW2DetSNaNKeepBody (initMachineState wfcW2DetSNaNKeepBody []))
        (Miri.Interpreter.Step.step (hd wfcW2DetSNaNKeepBody) ()
          (wfcMiriEntry wfcW2DetSNaNKeepBody wfcF32Ty)) := by
  intro hd
  have hmd : FloatNaNModeOk false chooseNaN := Or.inr rfl
  have hrelN : StateRelLM3_1 wfcW2DetNBody (initMachineState wfcW2DetNBody [])
      (wfcMiriEntry wfcW2DetNBody wfcF64Ty) [] :=
    wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrelQ : StateRelLM3_1 wfcW2DetQBody (initMachineState wfcW2DetQBody [])
      (wfcMiriEntry wfcW2DetQBody wfcF64Ty) [] :=
    wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrelS : StateRelLM3_1 wfcW2DetSNaNTruncBody (initMachineState wfcW2DetSNaNTruncBody [])
      (wfcMiriEntry wfcW2DetSNaNTruncBody wfcF32Ty) [] :=
    wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrelK : StateRelLM3_1 wfcW2DetSNaNKeepBody (initMachineState wfcW2DetSNaNKeepBody [])
      (wfcMiriEntry wfcW2DetSNaNKeepBody wfcF32Ty) [] :=
    wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hphN : ∀ p, wfcW2DetNBody.phase ≠ .other p := fun _ h => nomatch h
  have hphQ : ∀ p, wfcW2DetQBody.phase ≠ .other p := fun _ h => nomatch h
  have hphS : ∀ p, wfcW2DetSNaNTruncBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨mN, lN, iN⟩ := wfc_step_constant_mode false chooseNaN hmd hrelN (wfc_allImm_entry _ _)
    hphN rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl rfl rfl
  obtain ⟨mQ, lQ, iQ⟩ := wfc_step_constant_mode false chooseNaN hmd hrelQ (wfc_allImm_entry _ _)
    hphQ rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inr rfl)) rfl rfl rfl
  obtain ⟨mS, lS, iS⟩ := wfc_step_constant_mode false chooseNaN hmd hrelS (wfc_allImm_entry _ _)
    hphS rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl
    (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inr rfl)) rfl rfl rfl
  refine ⟨⟨mN, lN, wfc_step_return_mode false chooseNaN lN.2.2.1 (fun tf htf => iN tf htf 0) hphN
      rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) rfl⟩,
    ⟨mQ, lQ, wfc_step_return_mode false chooseNaN lQ.2.2.1 (fun tf htf => iQ tf htf 0) hphQ
      rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) rfl⟩,
    rfl,
    ⟨mS, lS, wfc_step_return_mode false chooseNaN lS.2.2.1 (fun tf htf => iS tf htf 0) hphS
      rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) rfl⟩,
    (wfcW2_deterministic_canonicalization chooseNaN).2.2.2.2, fun hstep => ?_⟩
  have hag := (step_cast_floatToFloat_constant_deterministic_lockstep_iff hrelK
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) (fun tf htf => wfc_allImm_entry _ _ tf htf 0)).mp hstep
  have hnanK : Anneal.Mir.IeeeFloatCast.isNaNBits .binary64 0x7FF0000020000001 = true := rfl
  have hevK : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x7FF0000020000001 =
      0x7FC00001 := rfl
  have hprefK : preferredNaNBits .binary32 = 0x7FC00000 := rfl
  rw [hnanK, hevK, hprefK] at hag
  rcases hag with h | h
  · cases h
  · exact absurd h (by decide)

/-- **(W2) selector body** `bb0: _0 = const 0x7FF0_0000_2000_0001_f64 as f32; return`
(`_0 : f32`): a signaling `f64` NaN whose quieted `f32` conversion keeps payload bit `0`, so
its nondeterministic candidate list has all **6** entries. -/
def wfcW2SelBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_nan_selector" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000020000001 8))
      wfcF32Ty)]

def wfcW2SelS0 : MachineState := wfcAt wfcW2SelBody 0 [.uninit]

/-- `wfcW2SelBody` has the single local `_0`, so `wfcW2SelS0` *is* its program-entry state. -/
theorem wfcW2Sel_stateRel_init :
    StateRelLM3_1 wfcW2SelBody wfcW2SelS0 (wfcMiriEntry wfcW2SelBody wfcF32Ty) [] :=
  wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W2) universal 4-candidate NaN-choice selectors (`pure 0 .. pure 3`) at the step level** on
`wfcW2SelBody`: Anneal always stores the quieted conversion `0x7FC0_0001`, and for the four quiet
selectors `pure 0 .. pure 3` (`floatNondeterministic := true`) `lean-miri`'s step is
`StepRelLM3_1`-simulated by the Anneal successor storing `0x7FC0_0000` (`preferredNaN`),
`0xFFC0_0000` (its negation), `0x7FC0_0001` (the quieted conversion, i.e. Anneal's own result),
and `0xFFC0_0001` (its negation), instantiating `step_cast_floatToFloat_constant_pure_index_simulation`.
See `wfcW2_selectors_snan_4_5_and_out_of_range` below for the remaining signaling-NaN selectors
`pure 4` and `pure 5` and out-of-range selector failure! -/
theorem wfcW2_selectors_exact :
    let m₀ := wfcMiriEntry wfcW2SelBody wfcF32Ty
    let sel (i : Nat) :=
      annealStepHooksFloat wfcW2SelBody.localDecls wfcW2SelBody.layouts true (fun _ _ => pure i)
    stepMirFn wfcW2SelBody wfcW2SelS0 =
        .step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0x7FC00001, 4⟩)]) ∧
      StepRelLM3_1 wfcW2SelBody m₀ []
        (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0x7FC00000, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 0) () m₀) ∧
      StepRelLM3_1 wfcW2SelBody m₀ []
        (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0xFFC00000, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 1) () m₀) ∧
      StepRelLM3_1 wfcW2SelBody m₀ []
        (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0x7FC00001, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 2) () m₀) ∧
      StepRelLM3_1 wfcW2SelBody m₀ []
        (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0xFFC00001, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 3) () m₀) := by
  intro m₀ sel
  have himm₀ : ∀ tf, m₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => wfc_allImm_entry _ _ tf htf 0
  have hph : ∀ p, wfcW2SelBody.phase ≠ .other p := fun _ h => nomatch h
  have h0 := step_cast_floatToFloat_constant_pure_index_simulation wfcW2Sel_stateRel_init hph
    (fun _ _ => pure 0) 0 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (fun h => nomatch h) himm₀
  have h1 := step_cast_floatToFloat_constant_pure_index_simulation wfcW2Sel_stateRel_init hph
    (fun _ _ => pure 1) 1 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (fun h => nomatch h) himm₀
  have h2 := step_cast_floatToFloat_constant_pure_index_simulation wfcW2Sel_stateRel_init hph
    (fun _ _ => pure 2) 2 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (fun h => nomatch h) himm₀
  have h3 := step_cast_floatToFloat_constant_pure_index_simulation wfcW2Sel_stateRel_init hph
    (fun _ _ => pure 3) 3 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (fun h => nomatch h) himm₀
  have e0 : floatToFloatPureIndexBits .binary64 .binary32 0x7FF0000020000001 0 = 0x7FC00000 := rfl
  have e1 : floatToFloatPureIndexBits .binary64 .binary32 0x7FF0000020000001 1 = 0xFFC00000 := rfl
  have e2 : floatToFloatPureIndexBits .binary64 .binary32 0x7FF0000020000001 2 = 0x7FC00001 := rfl
  have e3 : floatToFloatPureIndexBits .binary64 .binary32 0x7FF0000020000001 3 = 0xFFC00001 := rfl
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  exact ⟨h0.1, h0.2, h1.2, h2.2, h3.2⟩

/-- **Signaling-NaN 6-candidate step-level simulation (`i < 6`)**: lifts
`floatOps_adjustNaN_pure_snan_index` through `Cast.cast` and `finish_write_immediate_split_hooks`
so selectors `pure 4` and `pure 5` (which select positive/negative **signaling** `dst` NaNs when the
scaled lower payload bits are non-zero) are also pinned bit-for-bit at `Step.step`. -/
theorem wfc_step_constant_snan_index
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (i : Nat) (hi : i < 6)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    {neg : Bool} {payload : Nat} (hnan : decodeBits src sc.bits = .nan neg false payload)
    (hlow_ne : evalFloatToFloatRoundTiesToEven src dst sc.bits % 2 ^ dst.fractionBits %
      2 ^ (dst.fractionBits - 1) ≠ 0)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    let convBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let convPay := convBits % 2 ^ dst.fractionBits
    let lower := convPay % 2 ^ (dst.fractionBits - 1)
    let outBits :=
      [preferredNaNBits dst,
       encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
       convBits,
       encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) convPay,
       encodeBits dst neg (2 ^ dst.exponentBits - 1) lower,
       encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) lower][i]'(by simpa using hi)
    outBits < 2 ^ dst.width →
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true (fun _ _ => pure i)) () m) ∧
      (i = 4 ∨ i = 5 →
        Miri.Interpreter.FloatBits.isSignaling ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 outBits⟩ =
          .ok true) := by
  intro convBits convPay lower outBits hout_lt
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    (fun _ _ => pure i) ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (caseVal := outBits)
    (by rw [scalarModulus_byteWidth]; exact hout_lt)
  rw [translateSizeBytes_byteWidth] at hfrom
  have hadj_pair := floatOps_adjustNaN_pure_snan_index
    (annealFloatOpsHooks true (fun _ _ => pure i)) () rfl i hi (fun _ _ => rfl) src dst sc.bits
    hbits neg payload hnan hlow_ne { m with stack := ⟨#[tfa]⟩ }
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc body.layouts
  have hdstT' := translateTy_of_ieeeFormatOfTy? hdst body.layouts
  have henc : encodeTyId castTy = floatTyIdOf dst := congrArg (·.ty) hdstT'
  have hcast :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts true (fun _ _ => pure i)) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ .FloatToFloat
          (encodeTyId castTy) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfa]⟩ } =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfa]⟩ } := by
    rw [hdstT, hsrcT, hdstT', henc]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_scalar, floatOps_readBits_annealFloat true (fun _ _ => pure i) src hrel hsz,
      floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false]
    rw [EStateM.bind_eq_ok hadj_pair.1]
    have hfrom' :
        Miri.Memory.Scalar.fromUInt
          (BitVec.ofNat 128
            ([preferredNaNBits dst,
              encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
              evalFloatToFloatRoundTiesToEven src dst sc.bits,
              encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
                (evalFloatToFloatRoundTiesToEven src dst sc.bits % 2 ^ dst.fractionBits),
              encodeBits dst neg (2 ^ dst.exponentBits - 1)
                (evalFloatToFloatRoundTiesToEven src dst sc.bits % 2 ^ dst.fractionBits %
                  2 ^ (dst.fractionBits - 1)),
              encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
                (evalFloatToFloatRoundTiesToEven src dst sc.bits % 2 ^ dst.fractionBits %
                  2 ^ (dst.fractionBits - 1))][i]'(by simpa using hi)))
          (ieeeFormatToMiri dst).size =
        .ok (.fromScalarInt msc') := hfrom
    rw [hfrom']
    rfl
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts true (fun _ _ => pure i)) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨convBits, dst.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]; rfl
  obtain ⟨_, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
    hfr.location_eq hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hlive_dst
    hrv_a hm_write
    (floatCast_dst_localRel hdst_scalar hrel' (floatToFloat_dst_size body.layouts hdst hdst_ty _))
  exact ⟨hsim, hadj_pair.2⟩

/-- **(W2) 4-candidate selector body** `bb0: _0 = const 0x7FF0_0000_0000_0001_f64 as f32; return`
(`_0 : f32`): a signaling `f64` NaN whose scaled `f32` payload vanishes, so its nondeterministic
`nanChoices` list has only **4** entries (`pure 4` is already out of range). -/
def wfcW2Sel4Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_nan_selector_4" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000000000001 8))
      wfcF32Ty)]

def wfcW2Sel4S0 : MachineState := wfcAt wfcW2Sel4Body 0 [.uninit]

/-- `wfcW2Sel4Body` has the single local `_0`, so `wfcW2Sel4S0` *is* its program-entry state. -/
theorem wfcW2Sel4_stateRel_init :
    StateRelLM3_1 wfcW2Sel4Body wfcW2Sel4S0 (wfcMiriEntry wfcW2Sel4Body wfcF32Ty) [] :=
  wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W2) signaling-NaN selectors `pure 4` & `pure 5` and out-of-range selector tightness**:
* on `wfcW2SelBody` (`0x7FF0_0000_2000_0001_f64 as f32`, 6 candidates), selectors `pure 4` and
  `pure 5` succeed and store the **signaling** `f32` NaNs `0x7F80_0001` and `0xFF80_0001`
  (`FloatBits.isSignaling = .ok true`), while `pure 6` fails with
  `.invalidProgram "invalid floating NaN choice index"` (`¬ StepRelLM3_1`);
* on `wfcW2Sel4Body` (`0x7FF0_0000_0000_0001_f64 as f32`, 4 candidates because the scaled payload
  vanishes), already `pure 4` fails with `.invalidProgram "invalid floating NaN choice index"`
  (`¬ StepRelLM3_1`). -/
theorem wfcW2_selectors_snan_4_5_and_out_of_range :
    let m₀ := wfcMiriEntry wfcW2SelBody wfcF32Ty
    let sel (i : Nat) :=
      annealStepHooksFloat wfcW2SelBody.localDecls wfcW2SelBody.layouts true (fun _ _ => pure i)
    let m₄₀ := wfcMiriEntry wfcW2Sel4Body wfcF32Ty
    let sel4 :=
      annealStepHooksFloat wfcW2Sel4Body.localDecls wfcW2Sel4Body.layouts true (fun _ _ => pure 4)
    StepRelLM3_1 wfcW2SelBody m₀ []
      (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0x7F800001, 4⟩)]))
      (Miri.Interpreter.Step.step (sel 4) () m₀) ∧
    Miri.Interpreter.FloatBits.isSignaling ⟨ieeeFormatToMiri .binary32, BitVec.ofNat 128 0x7F800001⟩ =
      .ok true ∧
    StepRelLM3_1 wfcW2SelBody m₀ []
      (.step (wfcAt wfcW2SelBody 1 [.init (.scalar ⟨0xFF800001, 4⟩)]))
      (Miri.Interpreter.Step.step (sel 5) () m₀) ∧
    Miri.Interpreter.FloatBits.isSignaling ⟨ieeeFormatToMiri .binary32, BitVec.ofNat 128 0xFF800001⟩ =
      .ok true ∧
    (∃ m', Miri.Interpreter.Step.step (sel 6) () m₀ =
        (m', .error (.invalidProgram "invalid floating NaN choice index"))) ∧
    ¬ StepRelLM3_1 wfcW2SelBody m₀ [] (stepMirFn wfcW2SelBody wfcW2SelS0)
      (Miri.Interpreter.Step.step (sel 6) () m₀) ∧
    (∃ m', Miri.Interpreter.Step.step sel4 () m₄₀ =
        (m', .error (.invalidProgram "invalid floating NaN choice index"))) ∧
    ¬ StepRelLM3_1 wfcW2Sel4Body m₄₀ [] (stepMirFn wfcW2Sel4Body wfcW2Sel4S0)
      (Miri.Interpreter.Step.step sel4 () m₄₀) := by
  intro m₀ sel m₄₀ sel4
  have himm₀ : ∀ tf, m₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => wfc_allImm_entry _ _ tf htf 0
  have himm₄₀ : ∀ tf, m₄₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => wfc_allImm_entry _ _ tf htf 0
  have hph : ∀ p, wfcW2SelBody.phase ≠ .other p := fun _ h => nomatch h
  have hph4 : ∀ p, wfcW2Sel4Body.phase ≠ .other p := fun _ h => nomatch h
  have hnan6 : decodeBits .binary64 0x7FF0000020000001 = .nan false false 0x20000001 := rfl
  have hnan4 : decodeBits .binary64 0x7FF0000000000001 = .nan false false 1 := rfl
  have h4 := wfc_step_constant_snan_index wfcW2Sel_stateRel_init 4 (by decide) rfl rfl rfl
    rfl rfl rfl rfl rfl (by decide) hnan6 (by decide) (fun h => nomatch h) himm₀ (by decide)
  have h5 := wfc_step_constant_snan_index wfcW2Sel_stateRel_init 5 (by decide) rfl rfl rfl
    rfl rfl rfl rfl rfl (by decide) hnan6 (by decide) (fun h => nomatch h) himm₀ (by decide)
  have hcs6 := floatBits_nanChoices_nondet_list_eq .binary64 .binary32 0x7FF0000020000001
    (by decide) false false 0x20000001 hnan6
  have hcs4 := floatBits_nanChoices_nondet_list_eq .binary64 .binary32 0x7FF0000000000001
    (by decide) false false 1 hnan4
  have hout6 := step_cast_floatToFloat_constant_pure_out_of_range wfcW2Sel_stateRel_init hph
    (fun _ _ => pure 6) 6 (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    hnan6 hcs6 (by decide) (fun h => nomatch h) himm₀
  have hout4 := step_cast_floatToFloat_constant_pure_out_of_range wfcW2Sel4_stateRel_init hph4
    (fun _ _ => pure 4) 4 (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    hnan4 hcs4 (by decide) (fun h => nomatch h) himm₄₀
  exact ⟨h4.1, h4.2 (Or.inl rfl), h5.1, h5.2 (Or.inr rfl), hout6.2.1, hout6.2.2, hout4.2.1,
    hout4.2.2⟩

/-- **(W2) `copy` and `move` NaN-choice selector body** (`_0 : f64`, `_1 : f64`, `_2 : f32`):
`bb0: StorageLive(_1); StorageLive(_2); _2 = const 0x7FF8_0000_2000_0000_f64 as f32;
_1 = copy _2 as f64; _0 = move _2 as f64; return`. -/
def wfcW2CopyMoveSelBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_copy_move_selector"
    [wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl wfcF32Ty] 8
    [.storageLive 1, .storageLive 2,
     .assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF8000020000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.copy (local_ 2)) wfcF64Ty),
     .assign (local_ 0) (.cast .floatToFloat (.move (local_ 2)) wfcF64Ty)]

def wfcW2CMS0 : MachineState := wfcAt wfcW2CopyMoveSelBody 0 [.uninit, .dead, .dead]
def wfcW2CMP1 : MachineState := wfcAt wfcW2CopyMoveSelBody 1 [.uninit, .uninit, .dead]
def wfcW2CMP2 : MachineState := wfcAt wfcW2CopyMoveSelBody 2 [.uninit, .uninit, .uninit]
def wfcW2CMS1 : MachineState := wfcAt wfcW2CopyMoveSelBody 3
  [.uninit, .uninit, .init (.scalar ⟨0x7FC00001, 4⟩)]
def wfcW2CMS2 : MachineState := wfcAt wfcW2CopyMoveSelBody 4
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00001, 4⟩)]

/-- **(W2) concrete `copy` and `move` NaN-choice selector simulations, from program entry**
(`step_cast_floatToFloat_copy_pure_index_simulation` and
`step_cast_floatToFloat_move_pure_index_simulation`): along the lockstep run
`entry ↦ … ↦ mₚ ↦ m₁ ↦ m₂` of `wfcW2CopyMoveSelBody` (after the `StorageLive` prologue), at `m₁`
`_1 = copy _2 as f64` under selector `pure 1` stores the negative canonical `f64` NaN
`0xFFF8_0000_0000_0000` (while Anneal stores `0x7FF8_0000_2000_0000`), and at `m₂`
`_0 = move _2 as f64` under selector `pure 3` deinitializes `_2` and stores the negative payload NaN
`0xFFF8_0000_2000_0000`. -/
theorem wfcW2_selectors_copy_and_move :
    initMachineState wfcW2CopyMoveSelBody [] = wfcW2CMS0 ∧
    ∃ mₚ m₁ m₂ : AnnealStepState,
      let b := wfcW2CopyMoveSelBody
      let sel (i : Nat) := annealStepHooksFloat b.localDecls b.layouts true (fun _ _ => pure i)
      WfcRun b wfcW2CMS0 (wfcMiriEntry b wfcF64Ty) wfcW2CMP2 mₚ ∧
      WfcLockstep b wfcW2CMP2 wfcW2CMS1 mₚ m₁ 2 0x7FC00001 4 ∧
      StepRelLM3_1 b m₁ []
        (.step (wfcAt b 4
          [.uninit, .init (.scalar ⟨0xFFF8000000000000, 8⟩), .init (.scalar ⟨0x7FC00001, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 1) () m₁) ∧
      WfcLockstep b wfcW2CMS1 wfcW2CMS2 m₁ m₂ 1 0x7FF8000020000000 8 ∧
      StepRelLM3_1 b m₂ []
        (.step (wfcAt b 5
          [.init (.scalar ⟨0xFFF8000020000000, 8⟩),
           .init (.scalar ⟨0x7FF8000020000000, 8⟩), .uninit]))
        (Miri.Interpreter.Step.step (sel 3) () m₂) := by
  have hph : ∀ p, wfcW2CopyMoveSelBody.phase ≠ .other p := fun _ h => nomatch h
  have h0 : initMachineState wfcW2CopyMoveSelBody [] = wfcW2CMS0 := rfl
  have hp1 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMS0 = .step wfcW2CMP1 := rfl
  have hp2 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMP1 = .step wfcW2CMP2 := rfl
  have hs1 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMP2 = .step wfcW2CMS1 := rfl
  have hs2 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMS1 = .step wfcW2CMS2 := rfl
  have hrel₀ : StateRelLM3_1 wfcW2CopyMoveSelBody wfcW2CMS0
      (wfcMiriEntry wfcW2CopyMoveSelBody wfcF64Ty) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p₁, e₁, r₁, q₁⟩ := wfc_step_storageLive hrel₀ (wfc_allImm_entry _ _) hph rfl rfl rfl hp1
  obtain ⟨p₂, e₂, r₂, q₂⟩ := wfc_step_storageLive r₁ q₁ hph rfl rfl rfl hp2
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₂ q₂ hph rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl
    wfcVSB8 (by decide) rfl rfl hs1 rfl
  have hcopy := step_cast_floatToFloat_copy_pure_index_simulation l₁.2.2.1 hph
    (fun _ _ => pure 1) 1 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (fun h => nomatch h) (fun tf htf => ⟨i₁ tf htf 1, i₁ tf htf 2⟩)
  have ec1 : floatToFloatPureIndexBits .binary32 .binary64 0x7FC00001 1 = 0xFFF8000000000000 := rfl
  rw [ec1] at hcopy
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_copy l₁.2.2.1 i₁ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl hs2 rfl
  have hmove := step_cast_floatToFloat_move_pure_index_simulation l₂.2.2.1 hph
    (fun _ _ => pure 3) 3 (by decide) (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (fun h => nomatch h) (fun tf htf => ⟨i₂ tf htf 0, i₂ tf htf 2⟩)
  have em3 : floatToFloatPureIndexBits .binary32 .binary64 0x7FC00001 3 = 0xFFF8000020000000 := rfl
  rw [em3] at hmove
  exact ⟨h0, p₂, m₁, m₂, .step hp1 e₁ r₁ (.step hp2 e₂ r₂ (.refl _ _)), l₁, hcopy.2, l₂,
    hmove.2⟩

/-- **(W2) exact `lean-miri` candidate lists and `preferredNaN` membership**
(`floatBits_nanChoices_nondet_list_eq`, `floatBits_preferredNaN_mem_nanChoices`):
* the signaling `0x7FF0_0000_2000_0001_f64 → f32` has the **6** candidates
  `[0x7FC0_0000, 0xFFC0_0000, 0x7FC0_0001, 0xFFC0_0001, 0x7F80_0001, 0xFF80_0001]`
  (`preferredNaN`, its negation, the quieted conversion, its negation, and the signaling
  `f32` NaN with the scaled payload and its negation);
* the signaling `0x7FF0_0000_0000_0001_f64 → f32` has only **4** candidates
  `[0x7FC0_0000, 0xFFC0_0000, 0x7FC0_0000, 0xFFC0_0000]` (its scaled payload vanishes, so the
  signaling candidate, which would be `+∞`, is suppressed);
* the signaling `0x7F80_0001_f32 → f64` has the **6** candidates
  `[0x7FF8…0, 0xFFF8…0, 0x7FF8_0000_2000_0000, 0xFFF8_0000_2000_0000, 0x7FF0_0000_2000_0000,
  0xFFF0_0000_2000_0000]`;
* deterministic mode collapses the list to `[preferredNaN] = [0x7FC0_0000]`. -/
theorem wfcW2_nanChoices_exact :
    let fb32 (b : Nat) : Miri.Interpreter.FloatBits := ⟨ieeeFormatToMiri .binary32, BitVec.ofNat 128 b⟩
    let fb64 (b : Nat) : Miri.Interpreter.FloatBits := ⟨ieeeFormatToMiri .binary64, BitVec.ofNat 128 b⟩
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri .binary32) [fb64 0x7FF0000020000001]
        true =
      .ok [fb32 0x7FC00000, fb32 0xFFC00000, fb32 0x7FC00001, fb32 0xFFC00001, fb32 0x7F800001,
        fb32 0xFF800001] ∧
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri .binary32) [fb64 0x7FF0000000000001]
        true =
      .ok [fb32 0x7FC00000, fb32 0xFFC00000, fb32 0x7FC00000, fb32 0xFFC00000] ∧
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri .binary64) [fb32 0x7F800001] true =
      .ok [fb64 0x7FF8000000000000, fb64 0xFFF8000000000000, fb64 0x7FF8000020000000,
        fb64 0xFFF8000020000000, fb64 0x7FF0000020000000, fb64 0xFFF0000020000000] ∧
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri .binary32) [fb64 0x7FF0000020000001]
        false = .ok [fb32 0x7FC00000] := by
  intro fb32 fb64
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact floatBits_nanChoices_nondet_list_eq .binary64 .binary32 0x7FF0000020000001 (by decide)
      false false 0x20000001 rfl
  · exact floatBits_nanChoices_nondet_list_eq .binary64 .binary32 0x7FF0000000000001 (by decide)
      false false 1 rfl
  · exact floatBits_nanChoices_nondet_list_eq .binary32 .binary64 0x7F800001 (by decide)
      false false 1 rfl
  · obtain ⟨c, hc, _, hdet⟩ := floatBits_preferredNaN_mem_nanChoices .binary64 .binary32
      0x7FF0000020000001 (by decide) false false 0x20000001 rfl false
    rw [hdet rfl] at hc
    exact hc

/-! ## (W3) Saturating `f32` / `f64 → i8..i128, isize, u8..u128, usize` -/

/-- **(W3) body** (`_0 : i8` returned, `_1 : i16`, `_2 : i32`, `_3 : i64`, `_4 : i128`,
`_5 : isize`, `_6 : u8`, `_7 : u16`, `_8 : u32`, `_9 : u64`, `_10 : u128`, `_11 : usize`,
`_12 : f32`, `_13 : f64`):
```text
bb0: StorageLive(_1); …; StorageLive(_13)        // prologue: `_1.._13` live
     _13 = const -1.5_f32 as f64          _12 = const 1e23_f64 as f32
     _0  = const +∞_f32 as i8             _1  = const -∞_f64 as i16
     _2  = const 3e9_f64 as i32           _3  = const -2.9_f64 as i64
     _4  = const NaN_f64 as i128          _5  = const -0.0_f32 as isize
     _6  = copy _13 as u8                 _7  = const 65535.5_f32 as u16
     _8  = const 2³²_f64 as u32           _9  = const 2⁶⁴_f32 as u64
     _10 = const f32::MAX as u128         _11 = move _12 as usize
     return
``` -/
def wfcW3Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w3_saturating_float_to_int"
    [wfcDecl (wfcIntTy .i8), wfcDecl (wfcIntTy .i16), wfcDecl (wfcIntTy .i32),
     wfcDecl (wfcIntTy .i64), wfcDecl (wfcIntTy .i128), wfcDecl (wfcIntTy .isize),
     wfcDecl (wfcUintTy .u8), wfcDecl (wfcUintTy .u16), wfcDecl (wfcUintTy .u32),
     wfcDecl (wfcUintTy .u64), wfcDecl (wfcUintTy .u128), wfcDecl (wfcUintTy .usize),
     wfcDecl wfcF32Ty, wfcDecl wfcF64Ty] 1
    ([.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
      .storageLive 6, .storageLive 7, .storageLive 8, .storageLive 9, .storageLive 10,
      .storageLive 11, .storageLive 12, .storageLive 13] ++
     [.assign (local_ 13) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0xBFC00000 4))
      wfcF64Ty),
      .assign (local_ 12) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x44B52D02C7E14AF6 8))
      wfcF32Ty),
      .assign (local_ 0) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x7F800000 4))
      (wfcIntTy .i8)),
      .assign (local_ 1) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0xFFF0000000000000 8))
      (wfcIntTy .i16)),
      .assign (local_ 2) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0x41E65A0BC0000000 8))
      (wfcIntTy .i32)),
      .assign (local_ 3) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0xC007333333333333 8))
      (wfcIntTy .i64)),
      .assign (local_ 4) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0x7FF8000000000000 8))
      (wfcIntTy .i128)),
      .assign (local_ 5) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x80000000 4))
      (wfcIntTy .isize)),
      .assign (local_ 6) (.cast .floatToInt (.copy (local_ 13)) (wfcUintTy .u8)),
      .assign (local_ 7) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x477FFF80 4))
      (wfcUintTy .u16)),
      .assign (local_ 8) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0x41F0000000000000 8))
      (wfcUintTy .u32)),
      .assign (local_ 9) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x5F800000 4))
      (wfcUintTy .u64)),
      .assign (local_ 10) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x7F7FFFFF 4))
      (wfcUintTy .u128)),
      .assign (local_ 11) (.cast .floatToInt (.move (local_ 12)) (wfcUintTy .usize))])

def wfcW3S0 : MachineState := wfcAt wfcW3Body 0
  [.uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead]
def wfcW3S1 : MachineState := wfcAt wfcW3Body 1
  [.uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead]
def wfcW3S2 : MachineState := wfcAt wfcW3Body 2
  [.uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead]
def wfcW3S3 : MachineState := wfcAt wfcW3Body 3
  [.uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead, .dead]
def wfcW3S4 : MachineState := wfcAt wfcW3Body 4
  [.uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead, .dead]
def wfcW3S5 : MachineState := wfcAt wfcW3Body 5
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead,
   .dead, .dead]
def wfcW3S6 : MachineState := wfcAt wfcW3Body 6
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead,
   .dead, .dead]
def wfcW3S7 : MachineState := wfcAt wfcW3Body 7
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead,
   .dead, .dead, .dead]
def wfcW3S8 : MachineState := wfcAt wfcW3Body 8
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead,
   .dead, .dead, .dead]
def wfcW3S9 : MachineState := wfcAt wfcW3Body 9
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead,
   .dead, .dead, .dead]
def wfcW3S10 : MachineState := wfcAt wfcW3Body 10
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .dead, .dead, .dead]
def wfcW3S11 : MachineState := wfcAt wfcW3Body 11
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .dead, .dead]
def wfcW3S12 : MachineState := wfcAt wfcW3Body 12
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .dead]
def wfcW3S13 : MachineState := wfcAt wfcW3Body 13
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit]
def wfcW3S14 : MachineState := wfcAt wfcW3Body 14
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S15 : MachineState := wfcAt wfcW3Body 15
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S16 : MachineState := wfcAt wfcW3Body 16
  [.init (.scalar ⟨0x7F, 1⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S17 : MachineState := wfcAt wfcW3Body 17
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S18 : MachineState := wfcAt wfcW3Body 18
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩), .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S19 : MachineState := wfcAt wfcW3Body 19
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S20 : MachineState := wfcAt wfcW3Body 20
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S21 : MachineState := wfcAt wfcW3Body 21
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S22 : MachineState := wfcAt wfcW3Body 22
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S23 : MachineState := wfcAt wfcW3Body 23
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S24 : MachineState := wfcAt wfcW3Body 24
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩), .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S25 : MachineState := wfcAt wfcW3Body 25
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩), .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S26 : MachineState := wfcAt wfcW3Body 26
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩),
   .init (.scalar ⟨0xFFFFFF00000000000000000000000000, 16⟩), .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S27 : MachineState := wfcAt wfcW3Body 27
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩),
   .init (.scalar ⟨0xFFFFFF00000000000000000000000000, 16⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩), .uninit, .init (.scalar ⟨0xBFF8000000000000, 8⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW3Body` from program entry (kernel evaluation of `stepMirFn`). -/
theorem wfcW3_anneal_run :
    initMachineState wfcW3Body [] = wfcW3S0 ∧
    stepMirFn wfcW3Body wfcW3S0 = .step wfcW3S1 ∧
    stepMirFn wfcW3Body wfcW3S1 = .step wfcW3S2 ∧
    stepMirFn wfcW3Body wfcW3S2 = .step wfcW3S3 ∧
    stepMirFn wfcW3Body wfcW3S3 = .step wfcW3S4 ∧
    stepMirFn wfcW3Body wfcW3S4 = .step wfcW3S5 ∧
    stepMirFn wfcW3Body wfcW3S5 = .step wfcW3S6 ∧
    stepMirFn wfcW3Body wfcW3S6 = .step wfcW3S7 ∧
    stepMirFn wfcW3Body wfcW3S7 = .step wfcW3S8 ∧
    stepMirFn wfcW3Body wfcW3S8 = .step wfcW3S9 ∧
    stepMirFn wfcW3Body wfcW3S9 = .step wfcW3S10 ∧
    stepMirFn wfcW3Body wfcW3S10 = .step wfcW3S11 ∧
    stepMirFn wfcW3Body wfcW3S11 = .step wfcW3S12 ∧
    stepMirFn wfcW3Body wfcW3S12 = .step wfcW3S13 ∧
    stepMirFn wfcW3Body wfcW3S13 = .step wfcW3S14 ∧
    stepMirFn wfcW3Body wfcW3S14 = .step wfcW3S15 ∧
    stepMirFn wfcW3Body wfcW3S15 = .step wfcW3S16 ∧
    stepMirFn wfcW3Body wfcW3S16 = .step wfcW3S17 ∧
    stepMirFn wfcW3Body wfcW3S17 = .step wfcW3S18 ∧
    stepMirFn wfcW3Body wfcW3S18 = .step wfcW3S19 ∧
    stepMirFn wfcW3Body wfcW3S19 = .step wfcW3S20 ∧
    stepMirFn wfcW3Body wfcW3S20 = .step wfcW3S21 ∧
    stepMirFn wfcW3Body wfcW3S21 = .step wfcW3S22 ∧
    stepMirFn wfcW3Body wfcW3S22 = .step wfcW3S23 ∧
    stepMirFn wfcW3Body wfcW3S23 = .step wfcW3S24 ∧
    stepMirFn wfcW3Body wfcW3S24 = .step wfcW3S25 ∧
    stepMirFn wfcW3Body wfcW3S25 = .step wfcW3S26 ∧
    stepMirFn wfcW3Body wfcW3S26 = .step wfcW3S27 ∧
    stepMirFn wfcW3Body wfcW3S27 = .retNormal (.scalar ⟨0x7F, 1⟩) wfcW3S27.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW3_stateRel_entry :
    StateRelLM3_1 wfcW3Body wfcW3S0 (wfcMiriEntry wfcW3Body (wfcIntTy .i8)) [] := by
  rw [← wfcW3_anneal_run.1]
  exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W3) end-to-end two-sided saturating float-to-int witness from program entry** over all
twelve integer targets: after the `StorageLive` prologue (`WfcRun` from `initMachineState` /
`wfcMiriEntry`), both machines run `wfcW3Body` in `StateRelLM3_1` lockstep (`.constant` / `.copy` /
`.move` operands, `f32` and `f64` sources) with bit-identical results after every step:
`+∞ as i8 = i8::MAX`, `-∞ as i16 = i16::MIN`, `3e9 as i32 = i32::MAX`, `-2.9 as i64 = -2`
(truncation toward zero), `NaN as i128 = 0`, `-0.0_f32 as isize = 0`, `-1.5 as u8 = 0` (negative
saturates to `u8::MIN`), `65535.5_f32 as u16 = u16::MAX`, `2³² as u32 = u32::MAX`,
`2⁶⁴_f32 as u64 = u64::MAX`, `f32::MAX as u128` exact (it is below `u128::MAX`), and
`1e23_f32 as usize = usize::MAX`; the function returns `127_i8`. -/
theorem wfcW3_end_to_end :
    initMachineState wfcW3Body [] = wfcW3S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ : AnnealStepState,
      WfcRun wfcW3Body wfcW3S0 (wfcMiriEntry wfcW3Body (wfcIntTy .i8)) wfcW3S13 mₚ ∧
      WfcLockstep wfcW3Body wfcW3S13 wfcW3S14 mₚ m₁ 13 0xBFF8000000000000 8 ∧
      WfcLockstep wfcW3Body wfcW3S14 wfcW3S15 m₁ m₂ 12 0x65A96816 4 ∧
      WfcLockstep wfcW3Body wfcW3S15 wfcW3S16 m₂ m₃ 0 0x7F 1 ∧
      WfcLockstep wfcW3Body wfcW3S16 wfcW3S17 m₃ m₄ 1 0x8000 2 ∧
      WfcLockstep wfcW3Body wfcW3S17 wfcW3S18 m₄ m₅ 2 0x7FFFFFFF 4 ∧
      WfcLockstep wfcW3Body wfcW3S18 wfcW3S19 m₅ m₆ 3 0xFFFFFFFFFFFFFFFE 8 ∧
      WfcLockstep wfcW3Body wfcW3S19 wfcW3S20 m₆ m₇ 4 0 16 ∧
      WfcLockstep wfcW3Body wfcW3S20 wfcW3S21 m₇ m₈ 5 0 8 ∧
      WfcLockstep wfcW3Body wfcW3S21 wfcW3S22 m₈ m₉ 6 0 1 ∧
      WfcLockstep wfcW3Body wfcW3S22 wfcW3S23 m₉ m₁₀ 7 0xFFFF 2 ∧
      WfcLockstep wfcW3Body wfcW3S23 wfcW3S24 m₁₀ m₁₁ 8 0xFFFFFFFF 4 ∧
      WfcLockstep wfcW3Body wfcW3S24 wfcW3S25 m₁₁ m₁₂ 9 0xFFFFFFFFFFFFFFFF 8 ∧
      WfcLockstep wfcW3Body wfcW3S25 wfcW3S26 m₁₂ m₁₃ 10 0xFFFFFF00000000000000000000000000 16 ∧
      WfcLockstep wfcW3Body wfcW3S26 wfcW3S27 m₁₃ m₁₄ 11 0xFFFFFFFFFFFFFFFF 8 ∧
      MiriHoldsUninit m₁₄ 12 ∧
      WfcReturns wfcW3Body wfcW3S27 m₁₄ (.scalar ⟨0x7F, 1⟩) := by
  have hph : ∀ p, wfcW3Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, hret⟩ := wfcW3_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive wfcW3_stateRel_entry (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ :=
    wfc_step_storageLive r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ :=
    wfc_step_storageLive r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ :=
    wfc_step_storageLive r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ :=
    wfc_step_storageLive r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨p₆, e₆, r₆, q₆⟩ :=
    wfc_step_storageLive r₅ q₅ hph rfl rfl rfl h6
  obtain ⟨p₇, e₇, r₇, q₇⟩ :=
    wfc_step_storageLive r₆ q₆ hph rfl rfl rfl h7
  obtain ⟨p₈, e₈, r₈, q₈⟩ :=
    wfc_step_storageLive r₇ q₇ hph rfl rfl rfl h8
  obtain ⟨p₉, e₉, r₉, q₉⟩ :=
    wfc_step_storageLive r₈ q₈ hph rfl rfl rfl h9
  obtain ⟨p₁₀, e₁₀, r₁₀, q₁₀⟩ :=
    wfc_step_storageLive r₉ q₉ hph rfl rfl rfl h10
  obtain ⟨p₁₁, e₁₁, r₁₁, q₁₁⟩ :=
    wfc_step_storageLive r₁₀ q₁₀ hph rfl rfl rfl h11
  obtain ⟨p₁₂, e₁₂, r₁₂, q₁₂⟩ :=
    wfc_step_storageLive r₁₁ q₁₁ hph rfl rfl rfl h12
  obtain ⟨p₁₃, e₁₃, r₁₃, q₁₃⟩ :=
    wfc_step_storageLive r₁₂ q₁₂ hph rfl rfl rfl h13
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₁₃ q₁₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h14 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h15 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h16 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h17 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_constant l₄.2.2.1 i₄ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h18 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_constant l₅.2.2.1 i₅ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h19 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h20 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_constant l₇.2.2.1 i₇ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h21 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_copy l₈.2.2.1 i₈ hph rfl rfl rfl rfl
    (.floatToInt rfl rfl) rfl rfl h22 rfl
  obtain ⟨m₁₀, l₁₀, i₁₀⟩ := wfc_step_constant l₉.2.2.1 i₉ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h23 rfl
  obtain ⟨m₁₁, l₁₁, i₁₁⟩ := wfc_step_constant l₁₀.2.2.1 i₁₀ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h24 rfl
  obtain ⟨m₁₂, l₁₂, i₁₂⟩ := wfc_step_constant l₁₁.2.2.1 i₁₁ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h25 rfl
  obtain ⟨m₁₃, l₁₃, i₁₃⟩ := wfc_step_constant l₁₂.2.2.1 i₁₂ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h26 rfl
  obtain ⟨m₁₄, l₁₄, i₁₄⟩ := wfc_step_move l₁₃.2.2.1 i₁₃ hph rfl rfl rfl rfl
    (.floatToInt rfl rfl) rfl rfl h27 rfl
  have hrun : WfcRun wfcW3Body wfcW3S0 (wfcMiriEntry wfcW3Body (wfcIntTy .i8)) wfcW3S13 p₁₃ :=
    (.step h1 e₁ r₁
      (.step h2 e₂ r₂
      (.step h3 e₃ r₃
      (.step h4 e₄ r₄
      (.step h5 e₅ r₅
      (.step h6 e₆ r₆
      (.step h7 e₇ r₇
      (.step h8 e₈ r₈
      (.step h9 e₉ r₉
      (.step h10 e₁₀ r₁₀
      (.step h11 e₁₁ r₁₁
      (.step h12 e₁₂ r₁₂
      (.step h13 e₁₃ r₁₃ (.refl _ _))))))))))))))
  exact ⟨h0, p₁₃, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, m₁₀, m₁₁, m₁₂, m₁₃, m₁₄, hrun, l₁, l₂, l₃, l₄,
    l₅, l₆, l₇, l₈, l₉, l₁₀, l₁₁, l₁₂, l₁₃, l₁₄,
    wfc_miri_uninit l₁₄.2.2.1 i₁₄ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₁₄.2.2.1 i₁₄ hph rfl rfl rfl rfl rfl rfl (Or.inr ⟨_, rfl⟩) hret⟩

/-! ### (W3) All twelve integer targets × both source formats at the `lean-miri` primitive -/

/-- **Two-sided** float-to-int value: `lean-miri`'s `FloatBits.toInteger` and the integer value of
Anneal's `evalFloatToIntSaturating` result both equal any closed form `V` of `floatToIntValue`
(`floatBits_toInteger_eq` and `Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound`). -/
theorem wfc_toInteger (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) (t : FloatIntTarget)
    (V : Int)
    (hv : floatToIntValue (decodeBits f bits) (t.minValue .bits64) (t.maxValue .bits64) = V) :
    Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
        (t.bitWidth .bits64) t.isSigned = .ok V ∧
      intValueOfBits t.isSigned (t.bitWidth .bits64)
        (evalFloatToIntSaturating f bits t .bits64).bits = V := by
  refine ⟨by rw [floatBits_toInteger_eq f bits h t .bits64, hv], ?_⟩
  rw [(Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound f bits t .bits64).2.2.1, hv]

/-- **(W3) two-sided saturating float-to-int for every one of the twelve integer targets** (64-bit
`isize` / `usize`) and both source formats: `lean-miri`'s `FloatBits.toInteger` (the primitive
behind `Cast.cast .FloatToInt`) **and** the integer value of Anneal's `evalFloatToIntSaturating`
agree on `NaN ↦ 0`, `+∞ ↦ MAX`, `-∞ ↦ MIN`, `-0.0 ↦ 0`, out-of-range finite saturation
(`1e300_f64 ↦ MAX`, `-f32::MAX ↦ MIN`), and in-range truncation toward zero (`1.75 ↦ 1`;
`-1.75 ↦ -1` on signed targets, saturating to `0 = MIN` on unsigned ones). -/
theorem wfcW3_toInteger_all_targets (t : FloatIntTarget) :
    let both (f : IeeeFormat) (bits : Nat) (V : Int) :=
      Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
          (t.bitWidth .bits64) t.isSigned = .ok V ∧
        intValueOfBits t.isSigned (t.bitWidth .bits64)
          (evalFloatToIntSaturating f bits t .bits64).bits = V
    both .binary32 0x7FC00000 0 ∧ both .binary64 0x7FF8000000000000 0 ∧
    both .binary32 0x7F800000 (t.maxValue .bits64) ∧
    both .binary64 0x7FF0000000000000 (t.maxValue .bits64) ∧
    both .binary32 0xFF800000 (t.minValue .bits64) ∧
    both .binary64 0xFFF0000000000000 (t.minValue .bits64) ∧
    both .binary32 0x80000000 0 ∧ both .binary64 0x8000000000000000 0 ∧
    both .binary64 0x7E37E43C8800759C (t.maxValue .bits64) ∧
    both .binary32 0xFF7FFFFF (t.minValue .bits64) ∧
    both .binary32 0x3FE00000 1 ∧ both .binary64 0x3FFC000000000000 1 ∧
    both .binary32 0xBFE00000 (if t.isSigned then -1 else 0) ∧
    both .binary64 0xBFFC000000000000 (if t.isSigned then -1 else 0) := by
  intro both
  refine ⟨wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_⟩ <;>
    (cases t <;> rename_i w <;> cases w <;> decide +kernel)

/-- **(W3) two-sided 1-ULP exact-inside vs. saturated-outside cliffs** (`FloatBits.toInteger` and
`evalFloatToIntSaturating`, **zero** `Classical.choice`):
* **`u8` / `i8` fractional boundary (`(MAX, MAX + 1)` and `(MIN - 1, MIN)`)**:
  `255.9999847_f32` (`0x437F_FFFF = 256 - 2⁻¹⁶ > 255`) truncates toward zero to `255` without
  saturating while `256.0_f32` (`0x4380_0000`) saturates to `255`; `-128.9999847_f32`
  (`0xC300_FFFF = -(128 + 1 - 2⁻¹⁶) < -128`) truncates toward zero to `-128` while `-129.0_f32`
  (`0xC301_0000`) saturates to `-128`; and `-(1 - 2⁻²⁴)_f32` (`0xBF7F_FFFF`) truncates to `0`.
* **`i32` (`f32`)**: `2³¹ - 128 = 2147483520` (`0x4EFF_FFFF`) exact vs `2³¹` (`0x4F00_0000`)
  `↦ i32::MAX`; `-2³¹` (`0xCF00_0000`) exact `i32::MIN` vs `-(2³¹ + 128)` (`0xCF00_0001`) saturated.
* **`i64` & `u64` (`f64`)**: `2⁶³ - 1024` (`0x43DF_FFFF_FFFF_FFFF`) exact vs `2⁶³`
  (`0x43E0_0000_0000_0000`) `↦ i64::MAX`; `-2⁶³` (`0xC3E0_0000_0000_0000`) exact vs
  `-(2⁶³ + 2048)` (`0xC3E0_0000_0000_0001`) saturated; `2⁶⁴ - 2048` (`0x43EF_FFFF_FFFF_FFFF`)
  exact vs `2⁶⁴` (`0x43F0_0000_0000_0000`) `↦ u64::MAX`.
* **`i128` & `u128`**: `2¹²⁷ - 2¹⁰³` (`0x7EFF_FFFF_f32`) exact vs `2¹²⁷` (`0x7F00_0000_f32`)
  `↦ i128::MAX`, `-2¹²⁷` (`0xFF00_0000_f32`) exact `i128::MIN`, and `2¹²⁸ - 2⁷⁵`
  (`0x47EF_FFFF_FFFF_FFFF_f64`) exact vs `2¹²⁸` (`0x47F0_0000_0000_0000_f64`) `↦ u128::MAX`. -/
theorem wfcW3_saturation_cliffs :
    let both (f : IeeeFormat) (bits : Nat) (t : FloatIntTarget) (V : Int) :=
      Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
          (t.bitWidth .bits64) t.isSigned = .ok V ∧
        intValueOfBits t.isSigned (t.bitWidth .bits64)
          (evalFloatToIntSaturating f bits t .bits64).bits = V
    both .binary32 0x437FFFFF (.unsigned .u8) 255 ∧
    both .binary32 0x43800000 (.unsigned .u8) 255 ∧
    both .binary32 0xC300FFFF (.signed .i8) (-128) ∧
    both .binary32 0xC3010000 (.signed .i8) (-128) ∧
    both .binary32 0xBF7FFFFF (.signed .i8) 0 ∧
    both .binary32 0x4EFFFFFF (.signed .i32) 2147483520 ∧
    both .binary32 0x4F000000 (.signed .i32) (2 ^ 31 - 1) ∧
    both .binary32 0xCF000000 (.signed .i32) (-(2 ^ 31)) ∧
    both .binary32 0xCF000001 (.signed .i32) (-(2 ^ 31)) ∧
    both .binary64 0x43DFFFFFFFFFFFFF (.signed .i64) (2 ^ 63 - 1024) ∧
    both .binary64 0x43E0000000000000 (.signed .i64) (2 ^ 63 - 1) ∧
    both .binary64 0xC3E0000000000000 (.signed .i64) (-(2 ^ 63)) ∧
    both .binary64 0xC3E0000000000001 (.signed .i64) (-(2 ^ 63)) ∧
    both .binary64 0x43EFFFFFFFFFFFFF (.unsigned .u64) (2 ^ 64 - 2048) ∧
    both .binary64 0x43F0000000000000 (.unsigned .u64) (2 ^ 64 - 1) ∧
    both .binary32 0x7EFFFFFF (.signed .i128) (2 ^ 127 - 2 ^ 103) ∧
    both .binary32 0x7F000000 (.signed .i128) (2 ^ 127 - 1) ∧
    both .binary32 0xFF000000 (.signed .i128) (-(2 ^ 127)) ∧
    both .binary64 0x47EFFFFFFFFFFFFF (.unsigned .u128) (2 ^ 128 - 2 ^ 75) ∧
    both .binary64 0x47F0000000000000 (.unsigned .u128) (2 ^ 128 - 1) := by
  intro both
  exact ⟨wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel),
    wfc_toInteger _ _ (by decide) _ _ (by decide +kernel)⟩


/-! ## (W4) Integer-to-float ties-to-even and overflow -/

/-- **(W4) body** (`_0, _1, _3, _4, _5 : f32` with `_0` returned; `_2, _6, _7 : f64`;
`_8 : u128`):
```text
bb0: StorageLive(_1); …; StorageLive(_8)  // prologue: `_1.._8` live
     _8 = const +∞_f32 as u128            // u128::MAX (saturation)
     _1 = copy _8 as f32                  // u128::MAX ↦ +∞ (overflow)
     _2 = move _8 as f64                  // u128::MAX ↦ 2¹²⁸
     _3 = const i128::MIN as f32          // -2¹²⁷ exactly
     _4 = const (2²⁴ + 1)_i32 as f32      // tie ↦ even 2²⁴
     _5 = const (2²⁴ + 3)_i32 as f32      // tie ↦ even 2²⁴ + 4
     _6 = const (2⁵³ + 1)_u64 as f64      // tie ↦ even 2⁵³
     _7 = const (2⁵³ + 3)_u64 as f64      // tie ↦ even 2⁵³ + 4
     _0 = const i8::MIN as f32            // -128.0
     return
``` -/
def wfcW4Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w4_int_to_float_ties_overflow"
    [wfcDecl wfcF32Ty, wfcDecl wfcF32Ty, wfcDecl wfcF64Ty, wfcDecl wfcF32Ty, wfcDecl wfcF32Ty,
     wfcDecl wfcF32Ty, wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl (wfcUintTy .u128)] 4
    ([.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
      .storageLive 6, .storageLive 7, .storageLive 8] ++
     [.assign (local_ 8) (.cast .floatToInt (.constant (wfcConst wfcF32Ty 0x7F800000 4))
      (wfcUintTy .u128)),
      .assign (local_ 1) (.cast .intToFloat (.copy (local_ 8)) wfcF32Ty),
      .assign (local_ 2) (.cast .intToFloat (.move (local_ 8)) wfcF64Ty),
      .assign (local_ 3) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i128) (2 ^ 127) 16))
      wfcF32Ty),
      .assign (local_ 4) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i32) (2 ^ 24 + 1) 4))
      wfcF32Ty),
      .assign (local_ 5) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i32) (2 ^ 24 + 3) 4))
      wfcF32Ty),
      .assign (local_ 6) (.cast .intToFloat (.constant (wfcConst (wfcUintTy .u64) (2 ^ 53 + 1) 8))
      wfcF64Ty),
      .assign (local_ 7) (.cast .intToFloat (.constant (wfcConst (wfcUintTy .u64) (2 ^ 53 + 3) 8))
      wfcF64Ty),
      .assign (local_ 0) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i8) 0x80 1)) wfcF32Ty)])

def wfcW4S0 : MachineState := wfcAt wfcW4Body 0
  [.uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW4S1 : MachineState := wfcAt wfcW4Body 1
  [.uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW4S2 : MachineState := wfcAt wfcW4Body 2
  [.uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead]
def wfcW4S3 : MachineState := wfcAt wfcW4Body 3
  [.uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead]
def wfcW4S4 : MachineState := wfcAt wfcW4Body 4
  [.uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead, .dead]
def wfcW4S5 : MachineState := wfcAt wfcW4Body 5
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead, .dead]
def wfcW4S6 : MachineState := wfcAt wfcW4Body 6
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead, .dead]
def wfcW4S7 : MachineState := wfcAt wfcW4Body 7
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .dead]
def wfcW4S8 : MachineState := wfcAt wfcW4Body 8
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S9 : MachineState := wfcAt wfcW4Body 9
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 16⟩)]
def wfcW4S10 : MachineState := wfcAt wfcW4Body 10
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 16⟩)]
def wfcW4S11 : MachineState := wfcAt wfcW4Body 11
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩), .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S12 : MachineState := wfcAt wfcW4Body 12
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S13 : MachineState := wfcAt wfcW4Body 13
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩), .uninit, .uninit, .uninit,
   .uninit]
def wfcW4S14 : MachineState := wfcAt wfcW4Body 14
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .uninit, .uninit, .uninit]
def wfcW4S15 : MachineState := wfcAt wfcW4Body 15
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .init (.scalar ⟨0x4340000000000000, 8⟩), .uninit, .uninit]
def wfcW4S16 : MachineState := wfcAt wfcW4Body 16
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .init (.scalar ⟨0x4340000000000000, 8⟩),
   .init (.scalar ⟨0x4340000000000002, 8⟩), .uninit]
def wfcW4S17 : MachineState := wfcAt wfcW4Body 17
  [.init (.scalar ⟨0xC3000000, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .init (.scalar ⟨0x47F0000000000000, 8⟩), .init (.scalar ⟨0xFF000000, 4⟩),
   .init (.scalar ⟨0x4B800000, 4⟩), .init (.scalar ⟨0x4B800002, 4⟩),
   .init (.scalar ⟨0x4340000000000000, 8⟩), .init (.scalar ⟨0x4340000000000002, 8⟩), .uninit]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW4Body` from program entry (kernel evaluation of `stepMirFn`). -/
theorem wfcW4_anneal_run :
    initMachineState wfcW4Body [] = wfcW4S0 ∧
    stepMirFn wfcW4Body wfcW4S0 = .step wfcW4S1 ∧
    stepMirFn wfcW4Body wfcW4S1 = .step wfcW4S2 ∧
    stepMirFn wfcW4Body wfcW4S2 = .step wfcW4S3 ∧
    stepMirFn wfcW4Body wfcW4S3 = .step wfcW4S4 ∧
    stepMirFn wfcW4Body wfcW4S4 = .step wfcW4S5 ∧
    stepMirFn wfcW4Body wfcW4S5 = .step wfcW4S6 ∧
    stepMirFn wfcW4Body wfcW4S6 = .step wfcW4S7 ∧
    stepMirFn wfcW4Body wfcW4S7 = .step wfcW4S8 ∧
    stepMirFn wfcW4Body wfcW4S8 = .step wfcW4S9 ∧
    stepMirFn wfcW4Body wfcW4S9 = .step wfcW4S10 ∧
    stepMirFn wfcW4Body wfcW4S10 = .step wfcW4S11 ∧
    stepMirFn wfcW4Body wfcW4S11 = .step wfcW4S12 ∧
    stepMirFn wfcW4Body wfcW4S12 = .step wfcW4S13 ∧
    stepMirFn wfcW4Body wfcW4S13 = .step wfcW4S14 ∧
    stepMirFn wfcW4Body wfcW4S14 = .step wfcW4S15 ∧
    stepMirFn wfcW4Body wfcW4S15 = .step wfcW4S16 ∧
    stepMirFn wfcW4Body wfcW4S16 = .step wfcW4S17 ∧
    stepMirFn wfcW4Body wfcW4S17 = .retNormal (.scalar ⟨0xC3000000, 4⟩) wfcW4S17.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW4_stateRel_entry :
    StateRelLM3_1 wfcW4Body wfcW4S0 (wfcMiriEntry wfcW4Body wfcF32Ty) [] := by
  rw [← wfcW4_anneal_run.1]
  exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)

/-- **(W4) end-to-end two-sided integer-to-float witness from program entry**: after the
`StorageLive` prologue (`WfcRun` from `initMachineState` / `wfcMiriEntry`), both machines run
`wfcW4Body` in `StateRelLM3_1` lockstep with bit-identical `roundTiesToEven` results:
`+∞_f32 as u128 = u128::MAX`, then `u128::MAX as f32 = +∞` (it exceeds `f32::MAX + ½ulp`) and
`u128::MAX as f64 = 2¹²⁸`, `i128::MIN as f32 = -2¹²⁷` exactly, the `2²⁴ + 1` / `2²⁴ + 3` ties round
to the even `2²⁴` / `2²⁴ + 4` in `f32`, the `2⁵³ + 1` / `2⁵³ + 3` ties round to the even `2⁵³` /
`2⁵³ + 4` in `f64`, and `i8::MIN as f32 = -128.0`; the function returns `-128.0_f32`. -/
theorem wfcW4_end_to_end :
    initMachineState wfcW4Body [] = wfcW4S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcRun wfcW4Body wfcW4S0 (wfcMiriEntry wfcW4Body wfcF32Ty) wfcW4S8 mₚ ∧
      WfcLockstep wfcW4Body wfcW4S8 wfcW4S9 mₚ m₁ 8 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 16 ∧
      WfcLockstep wfcW4Body wfcW4S9 wfcW4S10 m₁ m₂ 1 0x7F800000 4 ∧
      WfcLockstep wfcW4Body wfcW4S10 wfcW4S11 m₂ m₃ 2 0x47F0000000000000 8 ∧
      MiriHoldsUninit m₃ 8 ∧
      WfcLockstep wfcW4Body wfcW4S11 wfcW4S12 m₃ m₄ 3 0xFF000000 4 ∧
      WfcLockstep wfcW4Body wfcW4S12 wfcW4S13 m₄ m₅ 4 0x4B800000 4 ∧
      WfcLockstep wfcW4Body wfcW4S13 wfcW4S14 m₅ m₆ 5 0x4B800002 4 ∧
      WfcLockstep wfcW4Body wfcW4S14 wfcW4S15 m₆ m₇ 6 0x4340000000000000 8 ∧
      WfcLockstep wfcW4Body wfcW4S15 wfcW4S16 m₇ m₈ 7 0x4340000000000002 8 ∧
      WfcLockstep wfcW4Body wfcW4S16 wfcW4S17 m₈ m₉ 0 0xC3000000 4 ∧
      WfcReturns wfcW4Body wfcW4S17 m₉ (.scalar ⟨0xC3000000, 4⟩) := by
  have hph : ∀ p, wfcW4Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    hret⟩ := wfcW4_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive wfcW4_stateRel_entry (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ :=
    wfc_step_storageLive r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ :=
    wfc_step_storageLive r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ :=
    wfc_step_storageLive r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ :=
    wfc_step_storageLive r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨p₆, e₆, r₆, q₆⟩ :=
    wfc_step_storageLive r₅ q₅ hph rfl rfl rfl h6
  obtain ⟨p₇, e₇, r₇, q₇⟩ :=
    wfc_step_storageLive r₆ q₆ hph rfl rfl rfl h7
  obtain ⟨p₈, e₈, r₈, q₈⟩ :=
    wfc_step_storageLive r₇ q₇ hph rfl rfl rfl h8
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₈ q₈ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h9 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_copy l₁.2.2.1 i₁ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl h10 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_move l₂.2.2.1 i₂ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl h11 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB16 (by decide) rfl rfl h12 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_constant l₄.2.2.1 i₄ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h13 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_constant l₅.2.2.1 i₅ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h14 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h15 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_constant l₇.2.2.1 i₇ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h16 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_constant l₈.2.2.1 i₈ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB1 (by decide) rfl rfl h17 rfl
  have hrun : WfcRun wfcW4Body wfcW4S0 (wfcMiriEntry wfcW4Body wfcF32Ty) wfcW4S8 p₈ :=
    (.step h1 e₁ r₁
      (.step h2 e₂ r₂
      (.step h3 e₃ r₃
      (.step h4 e₄ r₄
      (.step h5 e₅ r₅
      (.step h6 e₆ r₆
      (.step h7 e₇ r₇
      (.step h8 e₈ r₈ (.refl _ _)))))))))
  exact ⟨h0, p₈, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, hrun, l₁, l₂, l₃,
    wfc_miri_uninit l₃.2.2.1 i₃ rfl (Or.inr ⟨_, rfl⟩) rfl, l₄, l₅, l₆, l₇, l₈, l₉,
    wfc_step_return l₉.2.2.1 i₉ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-- **(W4) multi-step deterministic-mode (`floatNondeterministic := false`) lockstep witness from
program entry, for every `chooseNaN`**: because `floatToInt` and `intToFloat` never invoke
`adjustNaN`, all 18 steps of `wfcW4Body` (`StorageLive(_1.._8)`, 9 casts, and `return`) execute in
`StateRelLM3_1` lockstep under `annealStepHooksFloat ... false chooseNaN` for arbitrary `chooseNaN`. -/
theorem wfcW4_deterministic_end_to_end
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    initMachineState wfcW4Body [] = wfcW4S0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcRunMode wfcW4Body false chooseNaN wfcW4S0 (wfcMiriEntry wfcW4Body wfcF32Ty) wfcW4S8 mₚ ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S8 wfcW4S9 mₚ m₁
        8 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 16 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S9 wfcW4S10 m₁ m₂ 1 0x7F800000 4 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S10 wfcW4S11 m₂ m₃ 2 0x47F0000000000000 8 ∧
      MiriHoldsUninit m₃ 8 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S11 wfcW4S12 m₃ m₄ 3 0xFF000000 4 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S12 wfcW4S13 m₄ m₅ 4 0x4B800000 4 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S13 wfcW4S14 m₅ m₆ 5 0x4B800002 4 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S14 wfcW4S15 m₆ m₇ 6 0x4340000000000000 8 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S15 wfcW4S16 m₇ m₈ 7 0x4340000000000002 8 ∧
      WfcLockstepMode wfcW4Body false chooseNaN wfcW4S16 wfcW4S17 m₈ m₉ 0 0xC3000000 4 ∧
      WfcReturnsMode wfcW4Body false chooseNaN wfcW4S17 m₉ (.scalar ⟨0xC3000000, 4⟩) := by
  have hph : ∀ p, wfcW4Body.phase ≠ .other p := fun _ h => nomatch h
  have hmd : FloatNaNModeOk false chooseNaN := Or.inr rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    hret⟩ := wfcW4_anneal_run
  obtain ⟨p₁, e₁, r₁, q₁⟩ :=
    wfc_step_storageLive_mode false chooseNaN wfcW4_stateRel_entry (wfc_allImm_entry _ _) hph
      rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ := wfc_step_storageLive_mode false chooseNaN r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨p₃, e₃, r₃, q₃⟩ := wfc_step_storageLive_mode false chooseNaN r₂ q₂ hph rfl rfl rfl h3
  obtain ⟨p₄, e₄, r₄, q₄⟩ := wfc_step_storageLive_mode false chooseNaN r₃ q₃ hph rfl rfl rfl h4
  obtain ⟨p₅, e₅, r₅, q₅⟩ := wfc_step_storageLive_mode false chooseNaN r₄ q₄ hph rfl rfl rfl h5
  obtain ⟨p₆, e₆, r₆, q₆⟩ := wfc_step_storageLive_mode false chooseNaN r₅ q₅ hph rfl rfl rfl h6
  obtain ⟨p₇, e₇, r₇, q₇⟩ := wfc_step_storageLive_mode false chooseNaN r₆ q₆ hph rfl rfl rfl h7
  obtain ⟨p₈, e₈, r₈, q₈⟩ := wfc_step_storageLive_mode false chooseNaN r₇ q₇ hph rfl rfl rfl h8
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant_mode false chooseNaN hmd r₈ q₈ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h9 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_copy_mode false chooseNaN hmd l₁.2.2.1 i₁ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl (fun _ _ _ hk _ _ => nomatch hk) rfl h10 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_move_mode false chooseNaN hmd l₂.2.2.1 i₂ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl (fun _ _ _ hk _ _ => nomatch hk) rfl h11 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant_mode false chooseNaN hmd l₃.2.2.1 i₃ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB16 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h12 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_constant_mode false chooseNaN hmd l₄.2.2.1 i₄ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h13 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_constant_mode false chooseNaN hmd l₅.2.2.1 i₅ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h14 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant_mode false chooseNaN hmd l₆.2.2.1 i₆ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h15 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_constant_mode false chooseNaN hmd l₇.2.2.1 i₇ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h16 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_constant_mode false chooseNaN hmd l₈.2.2.1 i₈ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB1 (by decide) rfl (fun _ _ _ hk _ _ => nomatch hk)
    rfl h17 rfl
  have hrun : WfcRunMode wfcW4Body false chooseNaN wfcW4S0 (wfcMiriEntry wfcW4Body wfcF32Ty)
      wfcW4S8 p₈ :=
    (.step h1 e₁ r₁ (.step h2 e₂ r₂ (.step h3 e₃ r₃ (.step h4 e₄ r₄
      (.step h5 e₅ r₅ (.step h6 e₆ r₆ (.step h7 e₇ r₇ (.step h8 e₈ r₈ (.refl _ _)))))))))
  exact ⟨h0, p₈, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, hrun, l₁, l₂, l₃,
    wfc_miri_uninit l₃.2.2.1 i₃ rfl (Or.inr ⟨_, rfl⟩) rfl, l₄, l₅, l₆, l₇, l₈, l₉,
    wfc_step_return_mode false chooseNaN l₉.2.2.1 (fun tf htf => i₉ tf htf 0) hph
      rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-! ### (W4) All twelve integer sources × both target formats at the `lean-miri` primitive -/

/-- Closed-form `f32` bit pattern of the all-ones integer `2^w - 1` (`-1 ↦ -1.0` on signed sources;
`MAX` on unsigned sources: exact on `u8`/`u16`, rounded up to `2³²` / `2⁶⁴` on `u32`/`u64`/`usize`,
and overflowing `f32::MAX + ½ulp` to `+∞` on `u128`). -/
def wfcAllOnesToF32 (s : FloatIntTarget) : Nat :=
  if s.isSigned then 0xBF800000
  else match s.bitWidth .bits64 with
    | 8 => 0x437F0000
    | 16 => 0x477FFF00
    | 32 => 0x4F800000
    | 64 => 0x5F800000
    | _ => 0x7F800000

/-- Closed-form `f64` bit pattern of the all-ones integer `2^w - 1` (`-1 ↦ -1.0` on signed sources;
`MAX` on unsigned sources: exact on `u8`/`u16`/`u32` and rounded up to `2⁶⁴` / `2¹²⁸` on
`u64`/`usize`/`u128`). -/
def wfcAllOnesToF64 (s : FloatIntTarget) : Nat :=
  if s.isSigned then 0xBFF0000000000000
  else match s.bitWidth .bits64 with
    | 8 => 0x406FE00000000000
    | 16 => 0x40EFFFE000000000
    | 32 => 0x41EFFFFFFFE00000
    | 64 => 0x43F0000000000000
    | _ => 0x47F0000000000000

/-- **Two-sided** int-to-float bit pattern: `lean-miri`'s `FloatBits.fromInteger` and Anneal's
`evalFloatCast .intToFloat` both produce any closed form `V` of `evalIntToFloatRoundTiesToEven`
(`floatBits_fromInteger_intValueOfBits`). -/
theorem wfc_fromInteger (s : FloatIntTarget) (bits : Nat) (f : IeeeFormat) (V : Nat)
    (hv : evalIntToFloatRoundTiesToEven s.isSigned (s.bitWidth .bits64) bits f = V) :
    Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f)
        (intValueOfBits s.isSigned (s.bitWidth .bits64) bits) =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 V⟩ ∧
    evalFloatCast .intToFloat (some (wfcTargetTy s)) (wfcFmtTy f) emptyLayoutTable
        (.scalar ⟨bits, s.bitWidth .bits64 / 8⟩) = some (.scalar ⟨V, f.byteWidth⟩) := by
  refine ⟨by rw [floatBits_fromInteger_intValueOfBits, hv], ?_⟩
  subst hv
  cases s with
  | signed w => cases w <;> cases f <;> rfl
  | unsigned w => cases w <;> cases f <;> rfl

/-- **(W4) two-sided `roundTiesToEven` int-to-float for every one of the twelve integer source
types** (64-bit `isize` / `usize`) and both target formats: `lean-miri`'s `FloatBits.fromInteger`
(the primitive behind `Cast.cast .IntToFloat`) **and** Anneal's `evalFloatCast .intToFloat` agree on
`0 ↦ +0.0`, `1 ↦ 1.0`, the all-ones bit pattern `2^w - 1` (`-1 ↦ -1.0` on signed sources; `MAX` on
unsigned sources through `u128::MAX ↦ +∞_f32` / `2¹²⁸_f64`), and the top-bit power of two
`2^(w - 1)` (`MIN = -2^(w - 1)` exact on signed sources including `i128::MIN = -2¹²⁷_f32`,
`+2^(w - 1)` exact on unsigned sources). -/
theorem wfcW4_fromInteger_all_sources (s : FloatIntTarget) :
    let w := s.bitWidth .bits64
    let both (bits : Nat) (f : IeeeFormat) (V : Nat) :=
      Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f)
          (intValueOfBits s.isSigned w bits) = .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 V⟩ ∧
      evalFloatCast .intToFloat (some (wfcTargetTy s)) (wfcFmtTy f) emptyLayoutTable
          (.scalar ⟨bits, w / 8⟩) = some (.scalar ⟨V, f.byteWidth⟩)
    both 0 .binary32 0 ∧ both 0 .binary64 0 ∧
    both 1 .binary32 0x3F800000 ∧ both 1 .binary64 0x3FF0000000000000 ∧
    both (2 ^ w - 1) .binary32 (wfcAllOnesToF32 s) ∧
    both (2 ^ w - 1) .binary64 (wfcAllOnesToF64 s) ∧
    both (2 ^ (w - 1)) .binary32
      ((if s.isSigned then 382 + w else 126 + w) * 2 ^ 23) ∧
    both (2 ^ (w - 1)) .binary64
      ((if s.isSigned then 3070 + w else 1022 + w) * 2 ^ 52) := by
  intro w both
  refine ⟨wfc_fromInteger s 0 .binary32 0 ?_, wfc_fromInteger s 0 .binary64 0 ?_,
    wfc_fromInteger s 1 .binary32 0x3F800000 ?_,
    wfc_fromInteger s 1 .binary64 0x3FF0000000000000 ?_,
    wfc_fromInteger s (2 ^ w - 1) .binary32 (wfcAllOnesToF32 s) ?_,
    wfc_fromInteger s (2 ^ w - 1) .binary64 (wfcAllOnesToF64 s) ?_,
    wfc_fromInteger s (2 ^ (w - 1)) .binary32 _ ?_,
    wfc_fromInteger s (2 ^ (w - 1)) .binary64 _ ?_⟩ <;>
    (cases s <;> rename_i it <;> cases it <;> decide +kernel)

/-- **(W4) two-sided signed negative halfway ties and `i64::MIN + 1` rounding**: complements
`wfcW4Body`'s positive ties with negative signed `i32 -> f32` ties `-(2²⁴ + 1) ↦ -2²⁴`
(`0xCB80_0000`) and `-(2²⁴ + 3) ↦ -(2²⁴ + 4)` (`0xCB80_0002`), negative signed `i64 -> f64` ties
`-(2⁵³ + 1) ↦ -2⁵³` (`0xC340_0000_0000_0000`) and `-(2⁵³ + 3) ↦ -(2⁵³ + 4)`
(`0xC340_0000_0000_0002`), and `i64::MIN + 1 = -(2⁶³ - 1) ↦ -2⁶³` in both `f32` (`0xDF00_0000`) and
`f64` (`0xC3E0_0000_0000_0000`). -/
theorem wfcW4_signed_negative_ties :
    let both (s : FloatIntTarget) (bits : Nat) (f : IeeeFormat) (V : Nat) :=
      Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f)
          (intValueOfBits s.isSigned (s.bitWidth .bits64) bits) =
        .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 V⟩ ∧
      evalFloatCast .intToFloat (some (wfcTargetTy s)) (wfcFmtTy f) emptyLayoutTable
          (.scalar ⟨bits, s.bitWidth .bits64 / 8⟩) = some (.scalar ⟨V, f.byteWidth⟩)
    both (.signed .i32) (2 ^ 32 - (2 ^ 24 + 1)) .binary32 0xCB800000 ∧
    both (.signed .i32) (2 ^ 32 - (2 ^ 24 + 3)) .binary32 0xCB800002 ∧
    both (.signed .i64) (2 ^ 64 - (2 ^ 53 + 1)) .binary64 0xC340000000000000 ∧
    both (.signed .i64) (2 ^ 64 - (2 ^ 53 + 3)) .binary64 0xC340000000000002 ∧
    both (.signed .i64) 0x8000000000000001 .binary32 0xDF000000 ∧
    both (.signed .i64) 0x8000000000000001 .binary64 0xC3E0000000000000 :=
  ⟨wfc_fromInteger _ _ _ _ rfl, wfc_fromInteger _ _ _ _ rfl,
   wfc_fromInteger _ _ _ _ rfl, wfc_fromInteger _ _ _ _ rfl,
   wfc_fromInteger _ _ _ _ rfl, wfc_fromInteger _ _ _ _ rfl⟩

/-- **(W4) two-sided ties-to-even for every wide integer source type**: for **every** source type
of width `≥ 32` (`i32, u32, i64, u64, i128, u128, isize, usize`), `lean-miri`'s
`FloatBits.fromInteger` and Anneal's `evalFloatCast .intToFloat` agree that `2²⁴ + 1` and `2²⁴ + 3`
round to the even neighbours `2²⁴` / `2²⁴ + 4` in `f32` while `2²⁴ + 2` is exact, and that all three
are exact in `f64`; and for every source type of width `≥ 64` (`i64, u64, i128, u128, isize, usize`)
that `2⁵³ + 1` / `2⁵³ + 3` round to the even `2⁵³` / `2⁵³ + 4` in `f64` while `2⁵³ + 2` is exact and
`2⁵³ + 1` rounds to `2⁵³` in `f32`. The tie behaviour is thus independent of the source type. -/
theorem wfcW4_ties_all_wide_sources (s : FloatIntTarget) :
    let w := s.bitWidth .bits64
    let both (bits : Nat) (f : IeeeFormat) (V : Nat) :=
      Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f)
          (intValueOfBits s.isSigned w bits) = .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 V⟩ ∧
      evalFloatCast .intToFloat (some (wfcTargetTy s)) (wfcFmtTy f) emptyLayoutTable
          (.scalar ⟨bits, w / 8⟩) = some (.scalar ⟨V, f.byteWidth⟩)
    (32 ≤ w →
      both (2 ^ 24 + 1) .binary32 0x4B800000 ∧ both (2 ^ 24 + 2) .binary32 0x4B800001 ∧
      both (2 ^ 24 + 3) .binary32 0x4B800002 ∧ both (2 ^ 24 + 1) .binary64 0x4170000010000000 ∧
      both (2 ^ 24 + 3) .binary64 0x4170000030000000) ∧
    (64 ≤ w →
      both (2 ^ 53 + 1) .binary64 0x4340000000000000 ∧
      both (2 ^ 53 + 2) .binary64 0x4340000000000001 ∧
      both (2 ^ 53 + 3) .binary64 0x4340000000000002 ∧
      both (2 ^ 53 + 1) .binary32 0x5A000000) := by
  intro w both
  cases s <;> rename_i it <;> cases it <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    first
    | exact absurd h (by decide)
    | exact ⟨wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel)⟩
    | exact ⟨wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel),
        wfc_fromInteger _ _ _ _ (by decide +kernel)⟩

/-! ## Two-sided `Miri.Interpreter.Cast.cast` witnesses across layouts, NaN modes, and `f16`/`f128` -/

/-- `evalFloatCast` depends on `layouts` only through `floatPtrWidthOfLayouts layouts`. -/
theorem wfc_evalFloatCast_layouts_eq {layouts : LayoutTable}
    (hpw : floatPtrWidthOfLayouts layouts = .bits64)
    {kind : CastKind} {srcTy dstTy : Ty} (sc : MirAst.ScalarInt) :
    evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) =
      evalFloatCast kind (some srcTy) dstTy emptyLayoutTable (.scalar sc) := by
  simp only [evalFloatCast, hpw, show floatPtrWidthOfLayouts emptyLayoutTable = .bits64 from rfl]

/-- `translateTy` on any modeled float- or integer-scalar type is independent of `layouts`. -/
theorem wfc_translateTy_floatCast_eq {ty : Ty} (h : IsFloatCastScalarTy ty)
    (layouts : LayoutTable) :
    translateTy ty layouts = translateTy ty emptyLayoutTable := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf layouts,
        translateTy_of_ieeeFormatOfTy? hf emptyLayoutTable]
  · rw [translateTy_of_floatIntTargetOfTy? ht layouts,
        translateTy_of_floatIntTargetOfTy? ht emptyLayoutTable]

/-- **Mode-generic, layout-parametric two-sided `Cast.cast` instance**: over **any** 64-bit
`LayoutTable` and either NaN mode (`FloatNaNModeOk nondet chooseNaN`), if Anneal's `evalFloatCast`
maps `sc` to `⟨V, w⟩` (with `FloatCastDetAgrees` when `nondet = false`), then for **every**
`ScalarRel`-related `lean-miri` source scalar, `Miri.Interpreter.Cast.cast` writes a
`ScalarRel`-image of `⟨V, w⟩` (`floatCast_result_spec_mode`). -/
theorem wfc_cast_two_sided_mode (layouts : LayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64 := by rfl)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {kind : CastKind} {srcTy dstTy : Ty} (hsig : FloatCastSig kind srcTy dstTy)
    {sc : MirAst.ScalarInt} {V w : Nat}
    (hsz : (translateTy srcTy emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind srcTy dstTy sc.bits)
    (hev : evalFloatCast kind (some srcTy) dstTy emptyLayoutTable (.scalar sc) =
      some (.scalar ⟨V, w⟩))
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) = some (.scalar ⟨V, w⟩) ∧
    ∀ msc, ScalarRel sc msc → ∃ msc', ScalarRel ⟨V, w⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId dstTy) ⟨destRef, translateTy dstTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy dstTy layouts⟩ := by
  have hevL : evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) =
      some (.scalar ⟨V, w⟩) :=
    (wfc_evalFloatCast_layouts_eq hpw sc).trans hev
  have hszL : (translateTy srcTy layouts).layout.size = translateSizeBytes sc.sizeBytes := by
    rw [wfc_translateTy_floatCast_eq hsig.src_scalar layouts]; exact hsz
  refine ⟨hevL, fun msc hrel => ?_⟩
  obtain ⟨sc', msc', hev', hrel', _, hcast⟩ :=
    floatCast_result_spec_mode layouts hpw nondet chooseNaN hmode hsig hrel hszL hagree destRef
  rw [hevL] at hev'
  cases hev'
  exact ⟨msc', hrel', hcast⟩

/-- **Layout-parametric two-sided `Cast.cast` instance** under the refinement-witness hooks
(`nondet = true`, `chooseNaN = annealChooseQuietedNaN`). -/
theorem wfc_cast_two_sided (layouts : LayoutTable := emptyLayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64 := by rfl)
    {kind : CastKind} {srcTy dstTy : Ty} (hsig : FloatCastSig kind srcTy dstTy)
    {sc : MirAst.ScalarInt} {V w : Nat}
    (hsz : (translateTy srcTy emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes)
    (hev : evalFloatCast kind (some srcTy) dstTy emptyLayoutTable (.scalar sc) =
      some (.scalar ⟨V, w⟩))
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) = some (.scalar ⟨V, w⟩) ∧
    ∀ msc, ScalarRel sc msc → ∃ msc', ScalarRel ⟨V, w⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId dstTy) ⟨destRef, translateTy dstTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy dstTy layouts⟩ :=
  wfc_cast_two_sided_mode layouts hpw true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩) hsig hsz
    (fun h => nomatch h) hev destRef

/-- **Two-sided `Miri.Interpreter.Cast.cast` table for `.FloatToFloat`, `.FloatToInt`, and
`.IntToFloat` over ANY 64-bit `LayoutTable`** (including both `emptyLayoutTable` and
`wfcStage1Layouts`): for every `ScalarRel`-related source, `lean-miri`'s `Cast.cast` writes the
image of Anneal's `evalFloatCast` result: the subnormal tie `1.5·2⁻¹⁴⁹_f64 ↦ 0x0000_0002_f32`,
`-0.0_f64 ↦ -0.0_f32`, the signaling `0x7F80_0001_f32 ↦ 0x7FF8_0000_2000_0000_f64`,
`+∞_f32 ↦ i8::MAX`, `NaN_f64 ↦ 0_u128`, `-2.9_f64 ↦ -2_i64`, `u128::MAX ↦ +∞_f32`,
`(2⁵³ + 1)_u64 ↦ 2⁵³_f64` (tie to even), and `i128::MIN ↦ -2¹²⁷_f32`. -/
theorem wfcCast_two_sided_table (layouts : LayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    let castOK (kind : CastKind) (srcTy dstTy : Ty) (sc : MirAst.ScalarInt) (V w : Nat) :=
      evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) = some (.scalar ⟨V, w⟩) ∧
      ∀ msc, ScalarRel sc msc → ∃ msc', ScalarRel ⟨V, w⟩ msc' ∧
        Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts) () 16
            ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
            (translateCastKind kind) (encodeTyId dstTy) ⟨destRef, translateTy dstTy layouts⟩ =
          annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨destRef, translateTy dstTy layouts⟩
    castOK .floatToFloat wfcF64Ty wfcF32Ty ⟨0x36A8000000000000, 8⟩ 0x2 4 ∧
    castOK .floatToFloat wfcF64Ty wfcF32Ty ⟨0x8000000000000000, 8⟩ 0x80000000 4 ∧
    castOK .floatToFloat wfcF32Ty wfcF64Ty ⟨0x7F800001, 4⟩ 0x7FF8000020000000 8 ∧
    castOK .floatToInt wfcF32Ty (wfcIntTy .i8) ⟨0x7F800000, 4⟩ 0x7F 1 ∧
    castOK .floatToInt wfcF64Ty (wfcUintTy .u128) ⟨0x7FF8000000000000, 8⟩ 0 16 ∧
    castOK .floatToInt wfcF64Ty (wfcIntTy .i64) ⟨0xC007333333333333, 8⟩ 0xFFFFFFFFFFFFFFFE 8 ∧
    castOK .intToFloat (wfcUintTy .u128) wfcF32Ty ⟨2 ^ 128 - 1, 16⟩ 0x7F800000 4 ∧
    castOK .intToFloat (wfcUintTy .u64) wfcF64Ty ⟨2 ^ 53 + 1, 8⟩ 0x4340000000000000 8 ∧
    castOK .intToFloat (wfcIntTy .i128) wfcF32Ty ⟨2 ^ 127, 16⟩ 0xFF000000 4 := by
  intro castOK
  exact ⟨wfc_cast_two_sided layouts hpw (.floatToFloat rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.floatToFloat rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.floatToFloat rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.floatToInt rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.floatToInt rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.floatToInt rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.intToFloat rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.intToFloat rfl rfl) rfl rfl destRef,
    wfc_cast_two_sided layouts hpw (.intToFloat rfl rfl) rfl rfl destRef⟩

/-- **Deterministic-mode `Cast.cast` NaN canonicalization vs. exact agreement & mode-generic
`f16`/`f128` fail-closed `Cast.cast` boundary** over **any** 64-bit `LayoutTable`:
1. Under `floatNondeterministic := false` (`annealCastHooksFloat layouts false chooseNaN`), payload
   sNaNs `0x7F80_0001_f32 -> f64` and `0x7FF0_0000_2000_0001_f64 -> f32` write canonical
   `preferredNaNBits` (`0x7FF8_0000_0000_0000` and `0x7FC0_0000`) whereas Anneal's `evalFloatCast`
   preserves payload (`0x7FF8_0000_2000_0000` and `0x7FC0_0001`), while truncating sNaN
   `0x7FF0_0000_0000_0001_f64 -> f32` (`0x7FC0_0000`), finite `1.5·2⁻¹⁴⁹_f64 -> f32`,
   `+∞_f32 -> i8`, and `u128::MAX -> f32` agree bit-for-bit (`wfc_cast_two_sided_mode`).
2. Under **any** `nondet : Bool` and `chooseNaN`, `f16` and `f128` sources and targets return `none`
   in `evalFloatCast` (`evalFloatCast_f16_f128_none`) **and** `.error (.unsupported msg)` in
   `Miri.Interpreter.Cast.cast` (`cast_f16_f128_unsupported`). -/
theorem wfcCast_deterministic_and_f16_f128_boundary (layouts : LayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat)
    (srcOp : Miri.Interpreter.Operand AnnealProv)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    let castDetEq (kind : CastKind) (srcTy dstTy : Ty) (sc : MirAst.ScalarInt) (V w : Nat) :=
      evalFloatCast kind (some srcTy) dstTy layouts (.scalar sc) = some (.scalar ⟨V, w⟩) ∧
      ∀ msc, ScalarRel sc msc → ∃ msc', ScalarRel ⟨V, w⟩ msc' ∧
        Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts false chooseNaN) () 16
            ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
            (translateCastKind kind) (encodeTyId dstTy) ⟨destRef, translateTy dstTy layouts⟩ =
          annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨destRef, translateTy dstTy layouts⟩
    (evalFloatCast .floatToFloat (some wfcF32Ty) wfcF64Ty layouts (.scalar ⟨0x7F800001, 4⟩) =
        some (.scalar ⟨0x7FF8000020000000, 8⟩) ∧
      ∀ msc, ScalarRel ⟨0x7F800001, 4⟩ msc → ∃ msc', ScalarRel ⟨0x7FF8000000000000, 8⟩ msc' ∧
        Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts false chooseNaN) () 16
            ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy wfcF32Ty layouts⟩
            .FloatToFloat (encodeTyId wfcF64Ty) ⟨destRef, translateTy wfcF64Ty layouts⟩ =
          annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨destRef, translateTy wfcF64Ty layouts⟩) ∧
    (evalFloatCast .floatToFloat (some wfcF64Ty) wfcF32Ty layouts
          (.scalar ⟨0x7FF0000020000001, 8⟩) = some (.scalar ⟨0x7FC00001, 4⟩) ∧
      ∀ msc, ScalarRel ⟨0x7FF0000020000001, 8⟩ msc → ∃ msc', ScalarRel ⟨0x7FC00000, 4⟩ msc' ∧
        Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts false chooseNaN) () 16
            ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy wfcF64Ty layouts⟩
            .FloatToFloat (encodeTyId wfcF32Ty) ⟨destRef, translateTy wfcF32Ty layouts⟩ =
          annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨destRef, translateTy wfcF32Ty layouts⟩) ∧
    castDetEq .floatToFloat wfcF64Ty wfcF32Ty ⟨0x7FF0000000000001, 8⟩ 0x7FC00000 4 ∧
    castDetEq .floatToFloat wfcF64Ty wfcF32Ty ⟨0x36A8000000000000, 8⟩ 0x2 4 ∧
    castDetEq .floatToInt wfcF32Ty (wfcIntTy .i8) ⟨0x7F800000, 4⟩ 0x7F 1 ∧
    castDetEq .intToFloat (wfcUintTy .u128) wfcF32Ty ⟨2 ^ 128 - 1, 16⟩ 0x7F800000 4 ∧
    evalFloatCast .floatToFloat (some wfcF16Ty) wfcF32Ty layouts (.scalar ⟨0x3C00, 2⟩) = none ∧
    evalFloatCast .floatToFloat (some wfcF32Ty) wfcF128Ty layouts (.scalar ⟨0x3F800000, 4⟩) =
      none ∧
    (∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨srcOp, translateTy wfcF16Ty layouts⟩ .FloatToFloat (encodeTyId wfcF32Ty)
        ⟨destRef, translateTy wfcF32Ty layouts⟩ st = .error (.unsupported msg) st) ∧
    (∀ msc, ScalarRel ⟨0x3F800000, 4⟩ msc →
      ∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy wfcF32Ty layouts⟩
          .FloatToFloat (encodeTyId wfcF128Ty) ⟨destRef, translateTy wfcF128Ty layouts⟩ st =
        .error (.unsupported msg) st) := by
  intro castDetEq
  have hmd : FloatNaNModeOk false chooseNaN := Or.inr rfl
  have hf16_f128 := cast_f16_f128_unsupported layouts nondet chooseNaN destRef st
  refine ⟨⟨(wfc_evalFloatCast_layouts_eq hpw _).trans rfl, fun msc hrel => ?_⟩,
    ⟨(wfc_evalFloatCast_layouts_eq hpw _).trans rfl, fun msc hrel => ?_⟩,
    wfc_cast_two_sided_mode layouts hpw false chooseNaN hmd (.floatToFloat rfl rfl) rfl
      (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inr rfl)) rfl destRef,
    wfc_cast_two_sided_mode layouts hpw false chooseNaN hmd (.floatToFloat rfl rfl) rfl
      (fun _ => wfc_detAgrees_f2f rfl rfl (Or.inl rfl)) rfl destRef,
    wfc_cast_two_sided_mode layouts hpw false chooseNaN hmd (.floatToInt rfl rfl) rfl
      (fun _ _ _ hk _ _ => nomatch hk) rfl destRef,
    wfc_cast_two_sided_mode layouts hpw false chooseNaN hmd (.intToFloat rfl rfl) rfl
      (fun _ _ _ hk _ _ => nomatch hk) rfl destRef,
    (evalFloatCast_f16_f128_none .floatToFloat wfcF32Ty layouts _ (Or.inl rfl)).1,
    (evalFloatCast_f16_f128_none .floatToFloat wfcF32Ty layouts _ (Or.inr rfl)).2,
    hf16_f128.1 (kind := .floatToFloat) rfl (Or.inl rfl) srcOp,
    fun msc hrel => hf16_f128.2 (kind := .floatToFloat) rfl
      (Or.inr ⟨Or.inl rfl, .binary32, rfl⟩) hrel
      (by rw [wfc_translateTy_floatCast_eq (Or.inl ⟨.binary32, rfl⟩) layouts]; rfl) (Or.inr rfl)⟩
  · simpa [show Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7F800001 = true from rfl,
      show preferredNaNBits .binary64 = 0x7FF8000000000000 from rfl,
      show IeeeFormat.binary64.byteWidth = 8 from rfl] using
      cast_floatToFloat_deterministic_eq layouts chooseNaN (srcTy := wfcF32Ty)
        (targetTy := wfcF64Ty) rfl rfl hrel rfl destRef
  · simpa [show Anneal.Mir.IeeeFloatCast.isNaNBits .binary64 0x7FF0000020000001 = true from rfl,
      show preferredNaNBits .binary32 = 0x7FC00000 from rfl,
      show IeeeFormat.binary32.byteWidth = 4 from rfl] using
      cast_floatToFloat_deterministic_eq layouts chooseNaN (srcTy := wfcF64Ty)
        (targetTy := wfcF32Ty) rfl rfl hrel rfl destRef

/-! ## (W5) Negative controls: UB, fail-closed boundaries, and memory-backed locals -/

/-- **(W5a) uninitialized-source body** `bb0: StorageLive(_1); _0 = copy _1 as u32; return`
(`_0 : u32`, `_1 : f64` live but never written). -/
def wfcW5UBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_copy" [wfcDecl (wfcUintTy .u32), wfcDecl wfcF64Ty] 4
    [.storageLive 1, .assign (local_ 0) (.cast .floatToInt (.copy (local_ 1)) (wfcUintTy .u32))]

def wfcW5US0 : MachineState := wfcAt wfcW5UBody 0 [.uninit, .dead]
def wfcW5US1 : MachineState := wfcAt wfcW5UBody 1 [.uninit, .uninit]

/-- **(W5a') uninitialized integer-source body**
`bb0: StorageLive(_1); _0 = move _1 as f32; return` (`_0 : f32`, `_1 : i64` live but never
written). -/
def wfcW5U2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_move" [wfcDecl wfcF32Ty, wfcDecl (wfcIntTy .i64)] 4
    [.storageLive 1, .assign (local_ 0) (.cast .intToFloat (.move (local_ 1)) wfcF32Ty)]

def wfcW5U2S0 : MachineState := wfcAt wfcW5U2Body 0 [.uninit, .dead]
def wfcW5U2S1 : MachineState := wfcAt wfcW5U2Body 1 [.uninit, .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5U_anneal_run :
    initMachineState wfcW5UBody [] = wfcW5US0 ∧
    stepMirFn wfcW5UBody wfcW5US0 = .step wfcW5US1 ∧
    stepMirFn wfcW5UBody wfcW5US1 = .fail .ub ∧
    initMachineState wfcW5U2Body [] = wfcW5U2S0 ∧
    stepMirFn wfcW5U2Body wfcW5U2S0 = .step wfcW5U2S1 ∧
    stepMirFn wfcW5U2Body wfcW5U2S1 = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5a) uninitialized sources fault in both machines, from program entry**: after
`StorageLive(_1)` runs in lockstep from `initMachineState` / `wfcMiriEntry` (`_1` live and
`.uninit` in both machines), reading the never-written `_1` (by `copy` in a float-to-int cast and
by `move` in an int-to-float cast) makes Anneal's `stepMirFn` fail with `.ub` and `lean-miri`'s
`Step.step` report `.undefinedBehavior` (`StepRelLM3_1.ub`). -/
theorem wfcW5_uninit_source_ub :
    initMachineState wfcW5UBody [] = wfcW5US0 ∧
    initMachineState wfcW5U2Body [] = wfcW5U2S0 ∧
    ∃ m₁ m₁' : AnnealStepState,
      WfcRun wfcW5UBody wfcW5US0 (wfcMiriEntry wfcW5UBody (wfcUintTy .u32)) wfcW5US1 m₁ ∧
      MiriHoldsUninit m₁ 1 ∧
      WfcUB wfcW5UBody wfcW5US1 m₁ ∧
      WfcRun wfcW5U2Body wfcW5U2S0 (wfcMiriEntry wfcW5U2Body wfcF32Ty) wfcW5U2S1 m₁' ∧
      MiriHoldsUninit m₁' 1 ∧
      WfcUB wfcW5U2Body wfcW5U2S1 m₁' := by
  obtain ⟨h0, h1, h2, h0', h1', h2'⟩ := wfcW5U_anneal_run
  have hph : ∀ p, wfcW5UBody.phase ≠ .other p := fun _ h => nomatch h
  have hph' : ∀ p, wfcW5U2Body.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRelLM3_1 wfcW5UBody wfcW5US0 (wfcMiriEntry wfcW5UBody (wfcUintTy .u32)) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrel₀' : StateRelLM3_1 wfcW5U2Body wfcW5U2S0 (wfcMiriEntry wfcW5U2Body wfcF32Ty) [] := by
    rw [← h0']; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨m₁, e₁, r₁, q₁⟩ := wfc_step_storageLive hrel₀ (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨m₁', e₁', r₁', q₁'⟩ :=
    wfc_step_storageLive hrel₀' (wfc_allImm_entry _ _) hph' rfl rfl rfl h1'
  exact ⟨h0, h0', m₁, m₁', .step h1 e₁ r₁ (.refl _ _),
    wfc_miri_uninit r₁ q₁ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_ub_copy r₁ q₁ hph rfl rfl rfl rfl (.floatToInt rfl rfl) rfl rfl h2,
    .step h1' e₁' r₁' (.refl _ _), wfc_miri_uninit r₁' q₁' rfl (Or.inr ⟨_, rfl⟩) rfl,
    wfc_ub_move r₁' q₁' hph' rfl rfl rfl rfl (.intToFloat rfl rfl) rfl rfl h2'⟩

/-- **(W5b) moved-from-source body** (`_0 : i32`, `_1 : f64`, `_2 : f32`):
```text
bb0: StorageLive(_1); StorageLive(_2)
     _2 = const 2.5_f64 as f32     // 0x4020_0000
     _1 = move _2 as f64           // 0x4004_0000_0000_0000, `_2` deinitialized
     _0 = move _2 as i32           // read of moved-from `_2`: UB
     return
``` -/
def wfcW5MBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_moved_from"
    [wfcDecl (wfcIntTy .i32), wfcDecl wfcF64Ty, wfcDecl wfcF32Ty] 4
    [.storageLive 1, .storageLive 2,
     .assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x4004000000000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.move (local_ 2)) wfcF64Ty),
     .assign (local_ 0) (.cast .floatToInt (.move (local_ 2)) (wfcIntTy .i32))]

def wfcW5MS0 : MachineState := wfcAt wfcW5MBody 0 [.uninit, .dead, .dead]
def wfcW5MP1 : MachineState := wfcAt wfcW5MBody 1 [.uninit, .uninit, .dead]
def wfcW5MP2 : MachineState := wfcAt wfcW5MBody 2 [.uninit, .uninit, .uninit]
def wfcW5MS1 : MachineState := wfcAt wfcW5MBody 3
  [.uninit, .uninit, .init (.scalar ⟨0x40200000, 4⟩)]
def wfcW5MS2 : MachineState := wfcAt wfcW5MBody 4
  [.uninit, .init (.scalar ⟨0x4004000000000000, 8⟩), .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5M_anneal_run :
    initMachineState wfcW5MBody [] = wfcW5MS0 ∧
    stepMirFn wfcW5MBody wfcW5MS0 = .step wfcW5MP1 ∧
    stepMirFn wfcW5MBody wfcW5MP1 = .step wfcW5MP2 ∧
    stepMirFn wfcW5MBody wfcW5MP2 = .step wfcW5MS1 ∧
    stepMirFn wfcW5MBody wfcW5MS1 = .step wfcW5MS2 ∧
    stepMirFn wfcW5MBody wfcW5MS2 = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5b) moved-from sources fault in both machines, from program entry**: after the
`StorageLive` prologue (`WfcRun`) and two lockstep casts (the second deinitializes `_2` in both
machines), `move _2` makes Anneal fail with `.ub` and `lean-miri` report `.undefinedBehavior`. -/
theorem wfcW5_moved_from_ub :
    initMachineState wfcW5MBody [] = wfcW5MS0 ∧
    ∃ mₚ m₁ m₂ : AnnealStepState,
      WfcRun wfcW5MBody wfcW5MS0 (wfcMiriEntry wfcW5MBody (wfcIntTy .i32)) wfcW5MP2 mₚ ∧
      WfcLockstep wfcW5MBody wfcW5MP2 wfcW5MS1 mₚ m₁ 2 0x40200000 4 ∧
      WfcLockstep wfcW5MBody wfcW5MS1 wfcW5MS2 m₁ m₂ 1 0x4004000000000000 8 ∧
      MiriHoldsUninit m₂ 2 ∧
      WfcUB wfcW5MBody wfcW5MS2 m₂ := by
  have hph : ∀ p, wfcW5MBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := wfcW5M_anneal_run
  have hrel₀ : StateRelLM3_1 wfcW5MBody wfcW5MS0 (wfcMiriEntry wfcW5MBody (wfcIntTy .i32)) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p₁, e₁, r₁, q₁⟩ := wfc_step_storageLive hrel₀ (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂⟩ := wfc_step_storageLive r₁ q₁ hph rfl rfl rfl h2
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₂ q₂ hph rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl
    wfcVSB8 (by decide) rfl rfl h3 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_move l₁.2.2.1 i₁ hph rfl rfl rfl rfl (.floatToFloat rfl rfl)
    rfl rfl h4 rfl
  exact ⟨h0, p₂, m₁, m₂, .step h1 e₁ r₁ (.step h2 e₂ r₂ (.refl _ _)), l₁, l₂,
    wfc_miri_uninit l₂.2.2.1 i₂ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_ub_move l₂.2.2.1 i₂ hph rfl rfl rfl rfl (.floatToInt rfl rfl) rfl rfl h5⟩

/-! ### (W5c) Dead (`StorageDead` / never-`StorageLive`) sources, run from program entry -/

/-- **(W5c) dead-source body, run from program entry** (`_0 : f32`, `_1 : f64`):
```text
bb0: StorageLive(_1)
     _1 = const 3_i32 as f64       // 0x4008_0000_0000_0000
     _0 = copy _1 as f32           // 0x4040_0000
     StorageDead(_1)
     _0 = copy _1 as f32           // read of dead `_1`: UB
     return
``` -/
def wfcW5DBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_dead_source" [wfcDecl wfcF32Ty, wfcDecl wfcF64Ty] 4
    [.storageLive 1,
     .assign (local_ 1) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i32) 3 4)) wfcF64Ty),
     .assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty),
     .storageDead 1,
     .assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty)]

/-- **(W5c') never-live-source body, run from program entry**
`bb0: _0 = move _1 as f32; return` (`_0 : f32`, `_1 : f64` whose storage never became live). -/
def wfcW5D2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_never_live_source" [wfcDecl wfcF32Ty, wfcDecl wfcF64Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.move (local_ 1)) wfcF32Ty)]

/-- `lean-miri`'s program-entry frame for a two-local body: the return place `_0` is live and
uninitialized, `_1` is dead (its storage has not been made live). -/
def wfcEntryFrame2 (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { wfcFrame body retTy with
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }] }

/-- `lean-miri`'s program-entry state for a two-local body. -/
def wfcMiriEntry2 (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[wfcEntryFrame2 body retTy]⟩, machine := AnnealMachine.empty }

/-- **Program-entry relation for a two-local body**: Anneal's `initMachineState body []`
(`_0` uninitialized, `_1` dead) and `wfcMiriEntry2` are `StateRelLM3_1`-related. -/
theorem wfc_stateRel_entry2 (body : CapturedMir) (retTy : Ty) (d₀ d₁ : LocalDecl)
    (hdecls : body.localDecls = [d₀, d₁])
    (hcal : (initMachineState body []).memory.activeCallee = none)
    (hstack : (initMachineState body []).memory.callStack = .nil)
    (hbor : (initMachineState body []).memory.borrows = .nil)
    (hprot : (initMachineState body []).memory.activeProtectors = .nil)
    (hcaller : (initMachineState body []).memory.callerLocals = .nil)
    (hframe0 : (initMachineState body []).frame =
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] }) :
    StateRelLM3_1 body (initMachineState body []) (wfcMiriEntry2 body retTy) [] := by
  refine (StateRel.mk (wfcEntryFrame2 body retTy) rfl rfl ⟨translateTy retTy, rfl⟩ ?_
    hcal hstack hbor hprot hcaller ?_).toLM3_1
  · refine
      { body_eq := rfl
        location_eq := by rw [hframe0]; rfl
        af_locals_len := by rw [hframe0, hdecls]; rfl
        mf_locals_size := by rw [hdecls]; rfl
        locals_rel := ?_ }
    intro i decl slot mls hdecl hslot hmls
    rw [hframe0] at hslot
    match i with
    | 0 =>
      have hs : slot = .uninit := by simpa [get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [wfcEntryFrame2] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hs : slot = .dead := by simpa [get?] using hslot.symm
      have hm : mls = { value := .dead, layout := none } := by
        simpa [wfcEntryFrame2] using hmls.symm
      subst hs hm
      exact .dead none (fun _ h => nomatch h)
    | _ + 2 => simp [wfcEntryFrame2] at hmls
  · intro i _ _ _ _ _ _ hi _
    revert hi
    match i with
    | 0 | 1 | _ + 2 => simp [wfcEntryFrame2]

theorem wfc_allImm_entry2 (body : CapturedMir) (retTy : Ty) :
    WfcAllImm (wfcMiriEntry2 body retTy) := by
  intro tf htf k mls hmls mp hmp
  injection htf with h₁
  injection h₁ with h₂
  subst h₂
  match k with
  | 0 => simp [wfcEntryFrame2] at hmls; subst hmls; cases hmp
  | 1 => simp [wfcEntryFrame2] at hmls; subst hmls; cases hmp
  | _ + 2 => simp [wfcEntryFrame2] at hmls

def wfcW5DS0 : MachineState := wfcAt wfcW5DBody 0 [.uninit, .dead]
def wfcW5DS1 : MachineState := wfcAt wfcW5DBody 1 [.uninit, .uninit]
def wfcW5DS2 : MachineState := wfcAt wfcW5DBody 2
  [.uninit, .init (.scalar ⟨0x4008000000000000, 8⟩)]
def wfcW5DS3 : MachineState := wfcAt wfcW5DBody 3
  [.init (.scalar ⟨0x40400000, 4⟩), .init (.scalar ⟨0x4008000000000000, 8⟩)]
def wfcW5DS4 : MachineState := wfcAt wfcW5DBody 4 [.init (.scalar ⟨0x40400000, 4⟩), .dead]

set_option maxRecDepth 200000 in
theorem wfcW5D_anneal_run :
    initMachineState wfcW5DBody [] = wfcW5DS0 ∧
    stepMirFn wfcW5DBody wfcW5DS0 = .step wfcW5DS1 ∧
    stepMirFn wfcW5DBody wfcW5DS1 = .step wfcW5DS2 ∧
    stepMirFn wfcW5DBody wfcW5DS2 = .step wfcW5DS3 ∧
    stepMirFn wfcW5DBody wfcW5DS3 = .step wfcW5DS4 ∧
    stepMirFn wfcW5DBody wfcW5DS4 = .fail .ub ∧
    stepMirFn wfcW5D2Body (initMachineState wfcW5D2Body []) = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5c) dead sources fault in both machines, from program entry**: starting from Anneal's
`initMachineState` and `lean-miri`'s entry frame (`_1` dead in both), `StorageLive(_1)`, two
float casts, and `StorageDead(_1)` run in `StateRelLM3_1` lockstep (both machines hold
`3.0_f64` in `_1` and `3.0_f32` in `_0`), and the final `copy _1` of the now-dead `_1` makes
Anneal fail with `.ub` and `lean-miri` report `.undefinedBehavior`; likewise `move _1` of a local
whose storage never became live (`wfcW5D2Body`) faults in both machines at entry. -/
theorem wfcW5_dead_source_ub :
    initMachineState wfcW5DBody [] = wfcW5DS0 ∧
    ∃ m₁ m₂ m₃ m₄ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksFloat wfcW5DBody.localDecls wfcW5DBody.layouts)
        () (wfcMiriEntry2 wfcW5DBody wfcF32Ty) = (m₁, .ok true) ∧
      stepMirFn wfcW5DBody wfcW5DS0 = .step wfcW5DS1 ∧
      StateRelLM3_1 wfcW5DBody wfcW5DS1 m₁ [] ∧
      MiriHoldsUninit m₁ 1 ∧
      WfcLockstep wfcW5DBody wfcW5DS1 wfcW5DS2 m₁ m₂ 1 0x4008000000000000 8 ∧
      WfcLockstep wfcW5DBody wfcW5DS2 wfcW5DS3 m₂ m₃ 0 0x40400000 4 ∧
      Miri.Interpreter.Step.step (annealStepHooksFloat wfcW5DBody.localDecls wfcW5DBody.layouts)
        () m₃ = (m₄, .ok true) ∧
      stepMirFn wfcW5DBody wfcW5DS3 = .step wfcW5DS4 ∧
      StateRelLM3_1 wfcW5DBody wfcW5DS4 m₄ [] ∧
      MiriHoldsScalar m₄ 0 ⟨0x40400000, 4⟩ ∧
      WfcUB wfcW5DBody wfcW5DS4 m₄ ∧
      WfcUB wfcW5D2Body (initMachineState wfcW5D2Body []) (wfcMiriEntry2 wfcW5D2Body wfcF32Ty) := by
  have hph : ∀ p, wfcW5DBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := wfcW5D_anneal_run
  have hrel₀ : StateRelLM3_1 wfcW5DBody wfcW5DS0 (wfcMiriEntry2 wfcW5DBody wfcF32Ty) [] := by
    rw [← h0]
    exact wfc_stateRel_entry2 _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨m₁, hm₁, hrel₁, i₁⟩ := wfc_step_storageLive hrel₀ (wfc_allImm_entry2 _ _) hph rfl rfl
    rfl h1
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant hrel₁ i₁ hph rfl rfl rfl (.intToFloat rfl rfl) rfl rfl
    wfcVSB4 (by decide) rfl rfl h2 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_copy l₂.2.2.1 i₂ hph rfl rfl rfl rfl (.floatToFloat rfl rfl)
    rfl rfl h3 rfl
  obtain ⟨m₄, hm₄, hrel₄, i₄⟩ := wfc_step_storageDead l₃.2.2.1 i₃ hph rfl rfl rfl (by decide) h4
  have hrel₀' : StateRelLM3_1 wfcW5D2Body (initMachineState wfcW5D2Body [])
      (wfcMiriEntry2 wfcW5D2Body wfcF32Ty) [] :=
    wfc_stateRel_entry2 _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  exact ⟨h0, m₁, m₂, m₃, m₄, hm₁, h1, hrel₁, wfc_miri_uninit hrel₁ i₁ rfl (Or.inl ⟨_, rfl⟩) rfl,
    l₂, l₃, hm₄, h4, hrel₄, wfc_miri_scalar hrel₄ i₄ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_ub_copy hrel₄ i₄ hph rfl rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl h5,
    wfc_ub_move hrel₀' (wfc_allImm_entry2 _ _) (fun _ h => nomatch h) rfl rfl rfl rfl
      (.floatToFloat rfl rfl) rfl rfl h6⟩

/-! ### (W5d) `f16` / `f128` fail-closed boundaries -/

/-- **(W5d) `f16` source body** `bb0: _0 = const 1.0_f16 (0x3C00) as f32; return`. -/
def wfcW5HBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_f16_source" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF16Ty 0x3C00 2)) wfcF32Ty)]

def wfcW5HS0 : MachineState := wfcAt wfcW5HBody 0 [.uninit]

/-- **(W5d) `f128` target body** (`_0 : f32`, `_1 : f128`):
`bb0: StorageLive(_1); _0 = const 1.0_f64 as f32; _1 = const 1.0_f64 as f128; return`. -/
def wfcW5H2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_f128_target" [wfcDecl wfcF32Ty, wfcDecl wfcF128Ty] 4
    [.storageLive 1,
     .assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x3FF0000000000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x3FF0000000000000 8))
      wfcF128Ty)]

def wfcW5H2S0 : MachineState := wfcAt wfcW5H2Body 0 [.uninit, .dead]
def wfcW5H2P1 : MachineState := wfcAt wfcW5H2Body 1 [.uninit, .uninit]
def wfcW5H2S1 : MachineState := wfcAt wfcW5H2Body 2 [.init (.scalar ⟨0x3F800000, 4⟩), .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5H_anneal_run :
    initMachineState wfcW5HBody [] = wfcW5HS0 ∧
    stepMirFn wfcW5HBody wfcW5HS0 = .unsupported ∧
    initMachineState wfcW5H2Body [] = wfcW5H2S0 ∧
    stepMirFn wfcW5H2Body wfcW5H2S0 = .step wfcW5H2P1 ∧
    stepMirFn wfcW5H2Body wfcW5H2P1 = .step wfcW5H2S1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5d) `f16` / `f128` casts fail closed in both machines, from program entry**
(`step_cast_f16_f128_constant_fail_closed`): an `f16` source (`1.0_f16 as f32`) makes Anneal's
`stepMirFn` return `.unsupported` and `lean-miri`'s `Step.step` report `.unsupported` at program
entry; and after `StorageLive(_1)` and a lockstep `1.0_f64 as f32` step, an `f128` target
(`1.0_f64 as f128`) fails closed in both machines. -/
theorem wfcW5_f16_f128_fail_closed :
    (initMachineState wfcW5HBody [] = wfcW5HS0 ∧
      stepMirFn wfcW5HBody wfcW5HS0 = .unsupported ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooksFloat wfcW5HBody.localDecls wfcW5HBody.layouts) ()
          (wfcMiriEntry wfcW5HBody wfcF32Ty) = (m', .error (.unsupported msg))) ∧
    initMachineState wfcW5H2Body [] = wfcW5H2S0 ∧
    ∃ mₚ m₁,
      WfcRun wfcW5H2Body wfcW5H2S0 (wfcMiriEntry wfcW5H2Body wfcF32Ty) wfcW5H2P1 mₚ ∧
      WfcLockstep wfcW5H2Body wfcW5H2P1 wfcW5H2S1 mₚ m₁ 0 0x3F800000 4 ∧
      stepMirFn wfcW5H2Body wfcW5H2S1 = .unsupported ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooksFloat wfcW5H2Body.localDecls wfcW5H2Body.layouts) () m₁ =
        (m', .error (.unsupported msg)) := by
  obtain ⟨h0, h1, h0', h1', h2'⟩ := wfcW5H_anneal_run
  have hph : ∀ p, wfcW5HBody.phase ≠ .other p := fun _ h => nomatch h
  have hph2 : ∀ p, wfcW5H2Body.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRelLM3_1 wfcW5HBody wfcW5HS0 (wfcMiriEntry wfcW5HBody wfcF32Ty) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrel₀' : StateRelLM3_1 wfcW5H2Body wfcW5H2S0 (wfcMiriEntry wfcW5H2Body wfcF32Ty) [] := by
    rw [← h0']; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  refine ⟨⟨h0, step_cast_f16_f128_constant_fail_closed hrel₀ hph true annealChooseQuietedNaN rfl
    rfl rfl rfl rfl rfl wfcVSB2 (by decide) rfl (Or.inl (Or.inl rfl))⟩, h0', ?_⟩
  obtain ⟨p₁, e₁, r₁, q₁⟩ := wfc_step_storageLive hrel₀' (wfc_allImm_entry _ _) hph2 rfl rfl rfl h1'
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant r₁ q₁ hph2 rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl
    wfcVSB8 (by decide) rfl rfl h2' rfl
  exact ⟨p₁, m₁, .step h1' e₁ r₁ (.refl _ _), l₁,
    step_cast_f16_f128_constant_fail_closed l₁.2.2.1 hph2 true
    annealChooseQuietedNaN rfl rfl rfl rfl rfl rfl wfcVSB8 (by decide) rfl
    (Or.inr ⟨Or.inr ⟨Or.inl rfl, _, rfl⟩, Or.inr rfl⟩)⟩

/-- **(W5d') uninitialized `f16` source body** `bb0: StorageLive(_1); _0 = copy _1 as f32; return`
(`_0 : f32`, `_1 : f16` live but never written). -/
def wfcW5UninitF16SrcBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_f16_src" [wfcDecl wfcF32Ty, wfcDecl wfcF16Ty] 4
    [.storageLive 1, .assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty)]

def wfcW5UninitF16SrcS0 : MachineState := wfcAt wfcW5UninitF16SrcBody 0 [.uninit, .dead]
def wfcW5UninitF16SrcP1 : MachineState := wfcAt wfcW5UninitF16SrcBody 1 [.uninit, .uninit]

/-- **(W5d') uninitialized `f32 → f128` target body**
`bb0: StorageLive(_1); _1 = copy _0 as f128; return` (`_0 : f32` uninitialized, `_1 : f128`). -/
def wfcW5UninitF128DstBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_f128_dst" [wfcDecl wfcF32Ty, wfcDecl wfcF128Ty] 4
    [.storageLive 1, .assign (local_ 1) (.cast .floatToFloat (.copy (local_ 0)) wfcF128Ty)]

def wfcW5UninitF128DstS0 : MachineState := wfcAt wfcW5UninitF128DstBody 0 [.uninit, .dead]
def wfcW5UninitF128DstP1 : MachineState := wfcAt wfcW5UninitF128DstBody 1 [.uninit, .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5UninitF16F128_anneal_run :
    initMachineState wfcW5UninitF16SrcBody [] = wfcW5UninitF16SrcS0 ∧
    stepMirFn wfcW5UninitF16SrcBody wfcW5UninitF16SrcS0 = .step wfcW5UninitF16SrcP1 ∧
    initMachineState wfcW5UninitF128DstBody [] = wfcW5UninitF128DstS0 ∧
    stepMirFn wfcW5UninitF128DstBody wfcW5UninitF128DstS0 = .step wfcW5UninitF128DstP1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **(W5d') source-vs-target evaluation-order contrast on uninitialized `f16` / `f128` casts, from
program entry** (`step_cast_f16_f128_uninit_source_divergence` vs
`step_cast_f16_f128_uninit_target_ub_lockstep`), after `StorageLive(_1)` runs in lockstep:
* on `_0 = copy _1_f16 as f32` with uninitialized `_1`, Anneal rejects the uninitialized read with
  `.fail .ub` whereas `lean-miri`'s `Cast.cast` checks `h.typeInfo` on the `f16` source *before*
  reading `_1` and fails closed with `.error (.unsupported _)` (`¬ StepRelLM3_1`);
* on `_1 = copy _0_f32 as f128` with uninitialized `_0`, `lean-miri`'s `Cast.cast` reads the modeled
  `f32` source *before* checking `h.typeInfo` on the `f128` target, so **both** machines report UB
  in lockstep (`WfcUB`, `StepRelLM3_1.ub`). -/
theorem wfcW5_f16_f128_uninit_source_vs_target :
    initMachineState wfcW5UninitF16SrcBody [] = wfcW5UninitF16SrcS0 ∧
    initMachineState wfcW5UninitF128DstBody [] = wfcW5UninitF128DstS0 ∧
    ∃ mSrc mDst : AnnealStepState,
      WfcRun wfcW5UninitF16SrcBody wfcW5UninitF16SrcS0
        (wfcMiriEntry wfcW5UninitF16SrcBody wfcF32Ty) wfcW5UninitF16SrcP1 mSrc ∧
      (stepMirFn wfcW5UninitF16SrcBody wfcW5UninitF16SrcP1 = .fail .ub ∧
        (∃ m' msg, Miri.Interpreter.Step.step
            (annealStepHooksFloat wfcW5UninitF16SrcBody.localDecls wfcW5UninitF16SrcBody.layouts)
            () mSrc = (m', .error (.unsupported msg))) ∧
        ¬ StepRelLM3_1 wfcW5UninitF16SrcBody mSrc []
            (stepMirFn wfcW5UninitF16SrcBody wfcW5UninitF16SrcP1)
            (Miri.Interpreter.Step.step
              (annealStepHooksFloat wfcW5UninitF16SrcBody.localDecls wfcW5UninitF16SrcBody.layouts)
              () mSrc)) ∧
      WfcRun wfcW5UninitF128DstBody wfcW5UninitF128DstS0
        (wfcMiriEntry wfcW5UninitF128DstBody wfcF32Ty) wfcW5UninitF128DstP1 mDst ∧
      WfcUB wfcW5UninitF128DstBody wfcW5UninitF128DstP1 mDst := by
  obtain ⟨h0, h1, h0', h1'⟩ := wfcW5UninitF16F128_anneal_run
  have hph : ∀ p, wfcW5UninitF16SrcBody.phase ≠ .other p := fun _ h => nomatch h
  have hph' : ∀ p, wfcW5UninitF128DstBody.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRelLM3_1 wfcW5UninitF16SrcBody wfcW5UninitF16SrcS0
      (wfcMiriEntry wfcW5UninitF16SrcBody wfcF32Ty) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  have hrel₀' : StateRelLM3_1 wfcW5UninitF128DstBody wfcW5UninitF128DstS0
      (wfcMiriEntry wfcW5UninitF128DstBody wfcF32Ty) [] := by
    rw [← h0']; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨mSrc, e₁, r₁, _⟩ := wfc_step_storageLive hrel₀ (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨mDst, e₁', r₁', q₁'⟩ :=
    wfc_step_storageLive hrel₀' (wfc_allImm_entry _ _) hph' rfl rfl rfl h1'
  have hdiv := step_cast_f16_f128_uninit_source_divergence r₁ hph true annealChooseQuietedNaN rfl
    rfl rfl rfl rfl (Or.inl rfl) rfl rfl
  have hub := step_cast_f16_f128_uninit_target_ub_lockstep r₁' hph' true annealChooseQuietedNaN rfl
    rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) (Or.inr rfl) rfl rfl (fun tf htf => q₁' tf htf 0)
  exact ⟨h0, h0', mSrc, mDst, .step h1 e₁ r₁ (.refl _ _), hdiv, .step h1' e₁' r₁' (.refl _ _),
    hub.1, hub.2, wfc_ub_of_stepRel hub.2 hub.1⟩

/-! ### (W5e) `bool` / `char → float` boundary -/

/-- `char`. -/
def wfcCharTy : Ty := { kind := .char, layoutIdx := 0 }

/-- **(W5e) `bool` source body** `bb0: _0 = const true as f32; return` (rustc never emits
it: `bool as f32` is rejected by type checking). -/
def wfcW5BBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_bool_source" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .intToFloat (.constant (wfcConst boolTy 1 1)) wfcF32Ty)]

def wfcW5BS0 : MachineState := wfcAt wfcW5BBody 0 [.uninit]

/-- **(W5e) `char` source body** `bb0: _0 = const 'A' (0x41) as f64; return` (rustc never emits
it: `char as f64` is rejected by type checking). -/
def wfcW5CBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_char_source" [wfcDecl wfcF64Ty] 8
    [.assign (local_ 0) (.cast .intToFloat (.constant (wfcConst wfcCharTy 0x41 4)) wfcF64Ty)]

def wfcW5CS0 : MachineState := wfcAt wfcW5CBody 0 [.uninit]

/-- **(W5e) `bool` / `char → float` boundary**: Anneal fails closed (`evalFloatCast = none`, so
`stepMirFn` returns `.unsupported` on both `true as f32` and `'A' as f64`), whereas `lean-miri`'s
`Cast.cast .IntToFloat` accepts both `bool` (`true ↦ 1.0_f32 = 0x3F80_0000`, `false ↦ +0.0_f32`)
and `char` (`'A' ↦ 65.0_f64 = 0x4050_4000_0000_0000`, `'\u{10FFFF}' ↦ 1114111.0_f32 = 0x4987_FFF8`):
the boundary is a one-sided Anneal fail-closed restriction, never an unsound acceptance. -/
theorem wfcW5_bool_char_boundary (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    stepMirFn wfcW5BBody wfcW5BS0 = .unsupported ∧
    stepMirFn wfcW5CBody wfcW5CS0 = .unsupported ∧
    evalFloatCast .intToFloat (some boolTy) wfcF32Ty emptyLayoutTable (.scalar ⟨1, 1⟩) = none ∧
    evalFloatCast .intToFloat (some wfcCharTy) wfcF64Ty emptyLayoutTable
      (.scalar ⟨0x41, 4⟩) = none ∧
    (∃ msc, ScalarRel ⟨0x3F800000, 4⟩ msc ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat emptyLayoutTable) () 16
          ⟨.immediate (.scalar (.fromBool true)), translateTy boolTy emptyLayoutTable⟩ .IntToFloat
          (encodeTyId wfcF32Ty) ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc))
          ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩) ∧
    (∃ msc, ScalarRel ⟨0, 4⟩ msc ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat emptyLayoutTable) () 16
          ⟨.immediate (.scalar (.fromBool false)), translateTy boolTy emptyLayoutTable⟩ .IntToFloat
          (encodeTyId wfcF32Ty) ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc))
          ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩) ∧
    (∃ msc, ScalarRel ⟨0x4050400000000000, 8⟩ msc ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat emptyLayoutTable) () 16
          ⟨.immediate (.scalar (.fromChar 'A')), translateTy wfcCharTy emptyLayoutTable⟩ .IntToFloat
          (encodeTyId wfcF64Ty) ⟨destRef, translateTy wfcF64Ty emptyLayoutTable⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc))
          ⟨destRef, translateTy wfcF64Ty emptyLayoutTable⟩) ∧
    (∃ msc, ScalarRel ⟨0x4987FFF8, 4⟩ msc ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat emptyLayoutTable) () 16
          ⟨.immediate (.scalar (.fromChar (Char.ofNat 0x10FFFF))),
            translateTy wfcCharTy emptyLayoutTable⟩
          .IntToFloat (encodeTyId wfcF32Ty) ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc))
          ⟨destRef, translateTy wfcF32Ty emptyLayoutTable⟩) := by
  refine ⟨rfl, rfl, evalFloatCast_intToFloat_bool_char_none _ _ (Or.inl rfl),
    evalFloatCast_intToFloat_bool_char_none _ _ (Or.inr rfl), ?_, ?_, ?_, ?_⟩
  · exact cast_intToFloat_bool_miri_ok emptyLayoutTable true annealChooseQuietedNaN
      (srcTy := boolTy) (targetTy := wfcF32Ty) rfl rfl true destRef
  · exact cast_intToFloat_bool_miri_ok emptyLayoutTable true annealChooseQuietedNaN
      (srcTy := boolTy) (targetTy := wfcF32Ty) rfl rfl false destRef
  · exact cast_intToFloat_char_miri_ok emptyLayoutTable true annealChooseQuietedNaN
      (srcTy := wfcCharTy) (targetTy := wfcF64Ty) rfl rfl 'A' destRef
  · exact cast_intToFloat_char_miri_ok emptyLayoutTable true annealChooseQuietedNaN
      (srcTy := wfcCharTy) (targetTy := wfcF32Ty) rfl rfl (Char.ofNat 0x10FFFF) destRef

/-! ### (W5f) Promoted `&raw` (`allocMap`) and unpromoted `LocalRel.indirect` float witnesses -/

/-- `*mut i64`. -/
def wfcRawPtrMutI64Ty : Ty := { kind := .rawPtr .mut (.int .i64), layoutIdx := 0 }

/-- Placeholder ZST layout at index `0` (`unresolvedLayoutIdx`), matching
`Anneal.CastStage1Tests.unitPlaceholderLayout`. -/
def wfcUnitPlaceholderLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Non-empty 64-bit `LayoutTable` matching `Anneal.CastStage1Tests.castStage1Layouts` at index `0`
so `rawPtrPerm` exercises its resolved `some tl` branch (`.active`) alongside `emptyLayoutTable`
(`.unique`). -/
def wfcStage1Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [wfcUnitPlaceholderLayout] }

/-- Single-basic-block `Runtime(PostCleanup)` body `bb0: stmts; return` over custom `layouts`. -/
def wfcBodyLayouts (name : String) (decls : List LocalDecl) (retSz : Nat)
    (layouts : LayoutTable) (stmts : List StatementKind) : CapturedMir :=
  { wfcBody name decls retSz stmts with layouts := layouts }

/-- **(W5f-1a) uninitialized promoted-local UB body** from program entry (`emptyLayoutTable`,
`_0 : f64`, `_1 : i64`, `_2 : *mut i64`):
`bb0: StorageLive(_1); StorageLive(_2); _2 = &raw mut _1; _0 = copy _1 as f64; return`. -/
def wfcW5PromUBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_promoted_uninit_ub"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty] 8
    [.storageLive 1, .storageLive 2,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty)]

def wfcW5PromUS0 : MachineState := wfcAt wfcW5PromUBody 0 [.uninit, .dead, .dead]
def wfcW5PromUS1 : MachineState := wfcAt wfcW5PromUBody 1 [.uninit, .uninit, .dead]
def wfcW5PromUS2 : MachineState := wfcAt wfcW5PromUBody 2 [.uninit, .uninit, .uninit]

abbrev wfcW5PromUE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5PromUBody.localDecls wfcW5PromUBody.layouts .mut 1 1 floatWitAllocId1

def wfcW5PromUS3 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { wfcW5PromUS2.memory with borrows := [wfcW5PromUE1.toBorrowEntry], nextTag := 2 } }

set_option maxRecDepth 200000 in
theorem wfcW5PromU_anneal_run :
    initMachineState wfcW5PromUBody [] = wfcW5PromUS0 ∧
    stepMirFn wfcW5PromUBody wfcW5PromUS0 = .step wfcW5PromUS1 ∧
    stepMirFn wfcW5PromUBody wfcW5PromUS1 = .step wfcW5PromUS2 ∧
    stepMirFn wfcW5PromUBody wfcW5PromUS2 = .step wfcW5PromUS3 ∧
    stepMirFn wfcW5PromUBody wfcW5PromUS3 = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5f-1a) reading an uninitialized `&raw`-promoted local in a float cast faults with UB in
both machines, from program entry**: after `StorageLive(_1); StorageLive(_2)` (`WfcRun` from
`initMachineState` / `wfcMiriEntry`), `_2 = &raw mut _1` promotes `.uninit` `_1 : i64` into
`allocMap = [wfcW5PromUE1]` (`perm = .unique` on `emptyLayoutTable`) at `AllocId 1`
(`MiriHoldsIndirectUninit`), and `_0 = copy _1 as f64` faults with `.ub` in both `stepMirFn` and
`Step.step` (`WfcUB ... [wfcW5PromUE1]`). -/
theorem wfcW5_promoted_uninit_ub :
    initMachineState wfcW5PromUBody [] = wfcW5PromUS0 ∧
    ∃ mₚ m₁ : AnnealStepState,
      let b := wfcW5PromUBody
      WfcRun b wfcW5PromUS0 (wfcMiriEntry b wfcF64Ty) wfcW5PromUS2 mₚ ∧
      stepMirFn b wfcW5PromUS2 = .step wfcW5PromUS3 ∧
      Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () mₚ =
        (m₁, .ok true) ∧
      StateRelLM3_1 b wfcW5PromUS3 m₁ [wfcW5PromUE1] ∧
      wfcW5PromUE1.perm = .unique ∧
      MiriHoldsIndirectUninit m₁ 1 floatWitAllocId1 (Miri.ABI.Size.ofBytes 8) ∧
      WfcUB b wfcW5PromUS3 m₁ [wfcW5PromUE1] := by
  have hph : ∀ p, wfcW5PromUBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, h1, h2, hs₁, hs₂⟩ := wfcW5PromU_anneal_run
  have hrel_ent : StateRelLM3_1 wfcW5PromUBody wfcW5PromUS0
      (wfcMiriEntry wfcW5PromUBody wfcF64Ty) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p₁, e₁, r₁, q₁, hm_p₁⟩ :=
    wfc_step_storageLive_mem hrel_ent (wfc_allImm_entry _ _) hph rfl rfl rfl h1
  obtain ⟨p₂, e₂, r₂, q₂, hm_p₂⟩ := wfc_step_storageLive_mem r₁ q₁ hph rfl rfl rfl h2
  have hmach : p₂.machine = AnnealMachine.empty := hm_p₂.trans hm_p₁
  rcases p₂ with ⟨stackₚ, machₚ⟩
  dsimp only at hmach
  subst hmach
  have hrun : WfcRun wfcW5PromUBody wfcW5PromUS0
      (wfcMiriEntry wfcW5PromUBody wfcF64Ty) wfcW5PromUS2
      { stack := stackₚ, machine := AnnealMachine.empty } :=
    .step h1 e₁ r₁ (.step h2 e₂ r₂ (.refl _ _))
  have hm_eq₁ := step_float_eq_annealStepHooks_at_stmt r₂ true annealChooseQuietedNaN rfl rfl rfl
  have hr₁ := step_rawPtr_addrOf_lm3_1_simulation r₂ hph rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₂ tf htf 2, q₂ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁_base, hrel₁⟩ := wfc_step_of_stepRel hr₁ hs₁
  have hm₁ : Miri.Interpreter.Step.step
      (annealStepHooksFloat wfcW5PromUBody.localDecls wfcW5PromUBody.layouts) ()
      { stack := stackₚ, machine := AnnealMachine.empty } = (m₁, .ok true) := hm_eq₁.trans hm₁_base
  have hmap₁_eq :
      [rawPtrAllocMapEntry wfcW5PromUBody.localDecls wfcW5PromUBody.layouts .mut 1
        wfcW5PromUS2.memory.nextTag ⟨AnnealMachine.empty.memory.nextAllocId,
          AllocIdSupplyReady.empty.nonzero⟩] = [wfcW5PromUE1] := rfl
  have hrel₁' : StateRelLM3_1 wfcW5PromUBody wfcW5PromUS3 m₁ [wfcW5PromUE1] :=
    (congrArg (StateRelLM3_1 wfcW5PromUBody wfcW5PromUS3 m₁) hmap₁_eq).mp hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_supply r₂ rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₂ tf htf 2, q₂ tf htf 1⟩) AllocIdSupplyReady.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 32 by decide)
    (fun h => nomatch h) hm₁_base
  obtain ⟨tfₚ, htfₚ, _⟩ := id r₂
  have himm₁_0 : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 0 :=
    fun tf₁ htf₁ => himm₁_step tfₚ tf₁ htfₚ htf₁ 0 (by decide) (q₂ tfₚ htfₚ 0)
  have hr₂ : StepRelLM3_1 wfcW5PromUBody m₁ [wfcW5PromUE1]
      (stepMirFn wfcW5PromUBody wfcW5PromUS3)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromUBody.localDecls wfcW5PromUBody.layouts) () m₁) :=
    step_cast_float_copy_anyLocal_simulation hrel₁' hph rfl rfl rfl rfl
      (.intToFloat (t := .signed .i64) rfl rfl) rfl
      (fun _ _ => Or.inr ⟨wfcW5PromUE1, .head _, rfl⟩)
      (fun tf₁ htf₁ => Or.inl (himm₁_0 tf₁ htf₁))
  have hun₁ := wfc_miri_promoted_uninit hrel₁' (.head _) rfl (Or.inr ⟨.signed .i64, rfl⟩) rfl
  exact ⟨h0, _, m₁, hrun, hs₁, hm₁, hrel₁', rfl, hun₁, hs₂, hr₂, wfc_ub_of_stepRel hr₂ hs₂⟩

/-- **(W5f-1a') dead-target `&raw` and post-`StorageDead` promoted float-cast UB bodies**:
* `wfcW5RawDeadBody`: `bb0: StorageLive(_2); _2 = &raw mut _1; _0 = copy _1 as f64; return`
  (`_1` never made live).
* `wfcW5PromDeadCastBody`: `bb0: StorageLive(_1); StorageLive(_2); _2 = &raw mut _1;
  _1 = const -42.75_f64 as i64; StorageDead(_1); _0 = copy _1 as f64; return`. -/
def wfcW5RawDeadBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_raw_ptr_dead_ub"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty] 8
    [.storageLive 2,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty)]

def wfcW5RDS0 : MachineState := wfcAt wfcW5RawDeadBody 0 [.uninit, .dead, .dead]
def wfcW5RDS1 : MachineState := wfcAt wfcW5RawDeadBody 1 [.uninit, .dead, .uninit]

abbrev wfcW5RDE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5RawDeadBody.localDecls wfcW5RawDeadBody.layouts .mut 1 1 floatWitAllocId1

def wfcW5PromDeadCastBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_promoted_dead_cast_ub"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty] 8
    [.storageLive 1, .storageLive 2,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 1) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0xC045600000000000 8))
       (wfcIntTy .i64)),
     .storageDead 1,
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty)]

def wfcW5PromDCE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts .mut 1 1
    floatWitAllocId1
def wfcW5PromDCMap2 : List AllocMapEntry := updateAllocMapOnWrite [wfcW5PromDCE1] 1 none
def wfcW5PromDCMap3 : List AllocMapEntry := disableAllocMapLocal wfcW5PromDCMap2 1

def wfcW5PromDCS0 : MachineState := wfcAt wfcW5PromDeadCastBody 0 [.uninit, .dead, .dead]
def wfcW5PromDCS1 : MachineState := wfcAt wfcW5PromDeadCastBody 1 [.uninit, .uninit, .dead]
def wfcW5PromDCS2 : MachineState := wfcAt wfcW5PromDeadCastBody 2 [.uninit, .uninit, .uninit]
def wfcW5PromDCS3 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { wfcW5PromDCS2.memory with
                borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }]
                nextTag := 2 } }
def wfcW5PromDCS4 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 4,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { wfcW5PromDCS3.memory with
                borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                              perm := .disabled, allocDead := false }] } }
def wfcW5PromDCS5 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 5,
               locals := [.uninit, .dead, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { wfcW5PromDCS4.memory with
                borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                              perm := .disabled, allocDead := true }] } }

set_option maxRecDepth 200000 in
theorem wfcW5PromDead_anneal_run :
    initMachineState wfcW5RawDeadBody [] = wfcW5RDS0 ∧
    stepMirFn wfcW5RawDeadBody wfcW5RDS0 = .step wfcW5RDS1 ∧
    stepMirFn wfcW5RawDeadBody wfcW5RDS1 = .fail .ub ∧
    initMachineState wfcW5PromDeadCastBody [] = wfcW5PromDCS0 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS0 = .step wfcW5PromDCS1 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS1 = .step wfcW5PromDCS2 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS2 = .step wfcW5PromDCS3 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS3 = .step wfcW5PromDCS4 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS4 = .step wfcW5PromDCS5 ∧
    stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS5 = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **(W5f-1a') dead-local `&raw mut` and post-`StorageDead` promoted float-cast UB from program
entry**:
1. Taking `_2 = &raw mut _1` before `StorageLive(_1)` faults with `WfcUB` in both machines.
2. Promoting `_1` via `&raw mut _1`, writing `-42_i64` into `AllocId 1`, and running
   `StorageDead(_1)` frees `AllocId 1` (`MiriPromotedFreed`, `allocDead = true`); reading the
   retired `_1` in `_0 = copy _1 as f64` then faults with `WfcUB` in both machines. -/
theorem wfcW5_rawPtr_dead_and_promoted_dead_ub :
    initMachineState wfcW5RawDeadBody [] = wfcW5RDS0 ∧
    initMachineState wfcW5PromDeadCastBody [] = wfcW5PromDCS0 ∧
    ∃ m_rd m_dc₀ m_dc₁ m_dc₂ m_dc₃ : AnnealStepState,
      WfcRun wfcW5RawDeadBody wfcW5RDS0 (wfcMiriEntry wfcW5RawDeadBody wfcF64Ty) wfcW5RDS1 m_rd ∧
      WfcUB wfcW5RawDeadBody wfcW5RDS1 m_rd [wfcW5RDE1] ∧
      WfcRun wfcW5PromDeadCastBody wfcW5PromDCS0
        (wfcMiriEntry wfcW5PromDeadCastBody wfcF64Ty) wfcW5PromDCS2 m_dc₀ ∧
      Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts)
        () m_dc₀ = (m_dc₁, .ok true) ∧
      Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts)
        () m_dc₁ = (m_dc₂, .ok true) ∧
      Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts)
        () m_dc₂ = (m_dc₃, .ok true) ∧
      StateRelLM3_1 wfcW5PromDeadCastBody wfcW5PromDCS5 m_dc₃ wfcW5PromDCMap3 ∧
      MiriPromotedFreed m_dc₃ 1 floatWitAllocId1 ∧
      WfcUB wfcW5PromDeadCastBody wfcW5PromDCS5 m_dc₃ wfcW5PromDCMap3 := by
  obtain ⟨hrd0, hrd1, hrd_ub, hdc0, hdc1, hdc2, hdc3, hdc4, hdc5, hdc_ub⟩ :=
    wfcW5PromDead_anneal_run
  have hph_rd : ∀ p, wfcW5RawDeadBody.phase ≠ .other p := fun _ h => nomatch h
  have hph_dc : ∀ p, wfcW5PromDeadCastBody.phase ≠ .other p := fun _ h => nomatch h
  -- Part 1: `&raw mut _1` on never-live `_1`
  have hrel_rd0 : StateRelLM3_1 wfcW5RawDeadBody wfcW5RDS0
      (wfcMiriEntry wfcW5RawDeadBody wfcF64Ty) [] := by
    rw [← hrd0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p_rd, e_rd, r_rd, q_rd, hm_rd⟩ :=
    wfc_step_storageLive_mem hrel_rd0 (wfc_allImm_entry _ _) hph_rd rfl rfl rfl hrd1
  rcases p_rd with ⟨stack_rd, mach_rd⟩
  dsimp only at hm_rd
  subst hm_rd
  have hm_eq_rd := step_float_eq_annealStepHooks_at_stmt r_rd true annealChooseQuietedNaN rfl rfl
    rfl
  have hr_rd := step_rawPtr_addrOf_lm3_1_simulation r_rd hph_rd rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q_rd tf htf 2, q_rd tf htf 1⟩) AllocIdSupplyReady.empty
  rw [← hm_eq_rd] at hr_rd
  have hub_rd : WfcUB wfcW5RawDeadBody wfcW5RDS1
      { stack := stack_rd, machine := AnnealMachine.empty } [wfcW5RDE1] :=
    ⟨hrd_ub, hr_rd, wfc_ub_of_stepRel hr_rd hrd_ub⟩
  -- Part 2: `StorageDead(_1)` on `&raw`-promoted `_1`, followed by `copy _1 as f64`
  have hrel_dc0 : StateRelLM3_1 wfcW5PromDeadCastBody wfcW5PromDCS0
      (wfcMiriEntry wfcW5PromDeadCastBody wfcF64Ty) [] := by
    rw [← hdc0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p₁, e₁, r₁, q₁, hm_p₁⟩ :=
    wfc_step_storageLive_mem hrel_dc0 (wfc_allImm_entry _ _) hph_dc rfl rfl rfl hdc1
  obtain ⟨p₂, e₂, r₂, q₂, hm_p₂⟩ := wfc_step_storageLive_mem r₁ q₁ hph_dc rfl rfl rfl hdc2
  have hmach : p₂.machine = AnnealMachine.empty := hm_p₂.trans hm_p₁
  rcases p₂ with ⟨stack_dc, mach_dc⟩
  dsimp only at hmach
  subst hmach
  have hm_eq_dc1 := step_float_eq_annealStepHooks_at_stmt r₂ true annealChooseQuietedNaN rfl rfl rfl
  have hr_dc1 := step_rawPtr_addrOf_lm3_1_simulation r₂ hph_dc rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₂ tf htf 2, q₂ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m_dc₁, hm_dc1_base, hrel_dc1_raw⟩ := wfc_step_of_stepRel hr_dc1 hdc3
  have hm_dc1 : Miri.Interpreter.Step.step
      (annealStepHooksFloat wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts) ()
      { stack := stack_dc, machine := AnnealMachine.empty } = (m_dc₁, .ok true) :=
    hm_eq_dc1.trans hm_dc1_base
  have hmap_dc1 :
      [rawPtrAllocMapEntry wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts .mut 1
        wfcW5PromDCS2.memory.nextTag ⟨AnnealMachine.empty.memory.nextAllocId,
          AllocIdSupplyReady.empty.nonzero⟩] = [wfcW5PromDCE1] := rfl
  have hrel_dc1 : StateRelLM3_1 wfcW5PromDeadCastBody wfcW5PromDCS3 m_dc₁ [wfcW5PromDCE1] :=
    (congrArg (StateRelLM3_1 wfcW5PromDeadCastBody wfcW5PromDCS3 m_dc₁) hmap_dc1).mp hrel_dc1_raw
  obtain ⟨_, himm_dc1_step⟩ := step_rawPtr_addrOf_preserves_supply r₂ rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₂ tf htf 2, q₂ tf htf 1⟩) AllocIdSupplyReady.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 32 by decide)
    (fun h => nomatch h) hm_dc1_base
  obtain ⟨tf_dc₀, htf_dc₀, _⟩ := id r₂
  have himm_dc1_0 : ∀ tf₁, m_dc₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 0 :=
    fun tf₁ htf₁ => himm_dc1_step tf_dc₀ tf₁ htf_dc₀ htf₁ 0 (by decide) (q₂ tf_dc₀ htf_dc₀ 0)
  have hcan8 : (0xC045600000000000 : Nat) < scalarModulus 8 := by decide
  have hr_dc2 := step_cast_float_constant_anyLocal_simulation hrel_dc1 hph_dc rfl rfl rfl
    (.floatToInt (t := .signed .i64) rfl rfl) rfl rfl wfcVSB8 hcan8 rfl
    (fun _ _ => Or.inr ⟨wfcW5PromDCE1, .head _, rfl⟩)
  obtain ⟨m_dc₂, hm_dc2, hrel_dc2⟩ := wfc_step_of_stepRel hr_dc2 hdc4
  have hp_dc2 := step_cast_float_constant_anyLocal_preserves hrel_dc1 true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl (.floatToInt (t := .signed .i64) rfl rfl) rfl rfl wfcVSB8
    hcan8 rfl (fun h => nomatch h) (fun _ _ => Or.inr ⟨wfcW5PromDCE1, .head _, rfl⟩) rfl
    m_dc₂ hm_dc2
  obtain ⟨tf_dc₁, htf_dc₁, _⟩ := id hrel_dc1
  have himm_dc2_0 : ∀ tf₂, m_dc₂.stack.frames = #[tf₂] → IsImmediateFrameLocal tf₂ 0 :=
    fun tf₂ htf₂ => hp_dc2.2 tf_dc₁ tf₂ htf_dc₁ htf₂ 0 (himm_dc1_0 tf_dc₁ htf_dc₁)
  obtain ⟨m_dc₃, hm_dc3, hrel_dc3, himm_dc3_1, hpres_dc3⟩ :=
    wfc_step_storageDead_any hrel_dc2 hph_dc rfl rfl rfl (by decide) hdc5
  obtain ⟨tf_dc₂, htf_dc₂, _⟩ := id hrel_dc2
  have himm_dc3_0 : ∀ tf₃, m_dc₃.stack.frames = #[tf₃] → IsImmediateFrameLocal tf₃ 0 :=
    fun tf₃ htf₃ => hpres_dc3 tf_dc₂ tf₃ htf_dc₂ htf₃ 0 (himm_dc2_0 tf_dc₂ htf_dc₂)
  have hr_dc4_raw := step_cast_float_copy_anyLocal_simulation hrel_dc3 hph_dc rfl rfl rfl rfl
    (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun tf₃ htf₃ => Or.inl (himm_dc3_1 tf₃ htf₃))
    (fun tf₃ htf₃ => Or.inl (himm_dc3_0 tf₃ htf₃))
  have hmap_dc4 : updateAllocMapOnWrite wfcW5PromDCMap3 0 none = wfcW5PromDCMap3 := rfl
  have hr_dc4 : StepRelLM3_1 wfcW5PromDeadCastBody m_dc₃ wfcW5PromDCMap3
      (stepMirFn wfcW5PromDeadCastBody wfcW5PromDCS5)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromDeadCastBody.localDecls wfcW5PromDeadCastBody.layouts)
        () m_dc₃) :=
    (congrArg (fun mp => StepRelLM3_1 wfcW5PromDeadCastBody m_dc₃ mp _ _) hmap_dc4).mp hr_dc4_raw
  have he_dc3 : { wfcW5PromDCE1 with perm := .disabled, allocDead := true } ∈ wfcW5PromDCMap3 :=
    .head _
  exact ⟨hrd0, hdc0, _, _, m_dc₁, m_dc₂, m_dc₃,
    .step hrd1 e_rd r_rd (.refl _ _), hub_rd,
    .step hdc1 e₁ r₁ (.step hdc2 e₂ r₂ (.refl _ _)),
    hm_dc1, hm_dc2, hm_dc3, hrel_dc3,
    wfc_miri_promoted_freed hrel_dc3 he_dc3 himm_dc3_1 rfl rfl,
    hdc_ub, hr_dc4, wfc_ub_of_stepRel hr_dc4 hdc_ub⟩

/-- **(W5f-1b) multi-step `&raw`-promoted local + float-cast pipeline + `StorageDead` + `return`**
from program entry over non-empty 64-bit `wfcStage1Layouts`
(`_0 : f64` returned, `_1 : i64`, `_2 : *mut i64`, `_3 : f32`):
```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3)
     _2 = &raw mut _1                             // promotes _1 into allocMap = [e₁] (.active)
     _1 = const -42.75_f64 as i64                 // writes -42_i64 to AllocId 1, disables e₁
     _3 = copy _1 as f32                          // reads AllocId 1 ↦ -42.0_f32 (0xC228_0000)
     _1 = move _3 as i64                          // writes -42_i64 to AllocId 1, deinitializes _3
     _0 = copy _1 as f64                          // reads AllocId 1 ↦ -42.0_f64 (0xC045_0000_0000_0000)
     StorageDead(_3); StorageDead(_2); StorageDead(_1)  // frees AllocId 1 (allocDead = true)
     return
``` -/
def wfcW5PromBody : CapturedMir :=
  wfcBodyLayouts "wit_float_cast_lm::w5_promoted_raw_pipeline"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty, wfcDecl wfcF32Ty] 8
    wfcStage1Layouts
    [.storageLive 1, .storageLive 2, .storageLive 3,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 1) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0xC045600000000000 8))
       (wfcIntTy .i64)),
     .assign (local_ 3) (.cast .intToFloat (.copy (local_ 1)) wfcF32Ty),
     .assign (local_ 1) (.cast .floatToInt (.move (local_ 3)) (wfcIntTy .i64)),
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty),
     .storageDead 3, .storageDead 2, .storageDead 1]

def wfcW5PromE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5PromBody.localDecls wfcW5PromBody.layouts .mut 1 1 floatWitAllocId1

def wfcW5PromMap2 : List AllocMapEntry :=
  updateAllocMapOnWrite [wfcW5PromE1] 1 none

def wfcW5PromMapDead : List AllocMapEntry :=
  disableAllocMapLocal wfcW5PromMap2 1

def wfcW5PromBor1 : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := .active }

def wfcW5PromBor2 : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := .disabled, allocDead := false }

def wfcW5PromBorDead : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := .disabled, allocDead := true }

def wfcW5PromS0 : MachineState := wfcAt wfcW5PromBody 0 [.uninit, .dead, .dead, .dead]
def wfcW5PromS1 : MachineState := wfcAt wfcW5PromBody 1 [.uninit, .uninit, .dead, .dead]
def wfcW5PromS2 : MachineState := wfcAt wfcW5PromBody 2 [.uninit, .uninit, .uninit, .dead]
def wfcW5PromS3 : MachineState := wfcAt wfcW5PromBody 3 [.uninit, .uninit, .uninit, .uninit]
def wfcW5PromS4 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 4,
               locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                          .uninit] }
    memory := { wfcW5PromS3.memory with borrows := [wfcW5PromBor1], nextTag := 2 } }
def wfcW5PromS5 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 5,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := { wfcW5PromS4.memory with borrows := [wfcW5PromBor2] } }
def wfcW5PromS6 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 6,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                          .init (.scalar ⟨0xC2280000, 4⟩)] }
    memory := wfcW5PromS5.memory }
def wfcW5PromS7 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 7,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := wfcW5PromS6.memory }
def wfcW5PromS8 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 8,
               locals := [.init (.scalar ⟨0xC045000000000000, 8⟩),
                          .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := wfcW5PromS7.memory }
def wfcW5PromS9 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 9,
               locals := [.init (.scalar ⟨0xC045000000000000, 8⟩),
                          .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .dead] }
    memory := { wfcW5PromS8.memory with borrows := [wfcW5PromBor2] } }
def wfcW5PromS10 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 10,
               locals := [.init (.scalar ⟨0xC045000000000000, 8⟩),
                          .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩), .dead, .dead] }
    memory := { wfcW5PromS9.memory with borrows := [wfcW5PromBor2] } }
def wfcW5PromS11 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 11,
               locals := [.init (.scalar ⟨0xC045000000000000, 8⟩), .dead, .dead, .dead] }
    memory := { wfcW5PromS10.memory with borrows := [wfcW5PromBorDead] } }

set_option maxRecDepth 200000 in
theorem wfcW5Prom_anneal_run :
    initMachineState wfcW5PromBody [] = wfcW5PromS0 ∧
    stepMirFn wfcW5PromBody wfcW5PromS0 = .step wfcW5PromS1 ∧
    stepMirFn wfcW5PromBody wfcW5PromS1 = .step wfcW5PromS2 ∧
    stepMirFn wfcW5PromBody wfcW5PromS2 = .step wfcW5PromS3 ∧
    stepMirFn wfcW5PromBody wfcW5PromS3 = .step wfcW5PromS4 ∧
    stepMirFn wfcW5PromBody wfcW5PromS4 = .step wfcW5PromS5 ∧
    stepMirFn wfcW5PromBody wfcW5PromS5 = .step wfcW5PromS6 ∧
    stepMirFn wfcW5PromBody wfcW5PromS6 = .step wfcW5PromS7 ∧
    stepMirFn wfcW5PromBody wfcW5PromS7 = .step wfcW5PromS8 ∧
    stepMirFn wfcW5PromBody wfcW5PromS8 = .step wfcW5PromS9 ∧
    stepMirFn wfcW5PromBody wfcW5PromS9 = .step wfcW5PromS10 ∧
    stepMirFn wfcW5PromBody wfcW5PromS10 = .step wfcW5PromS11 ∧
    stepMirFn wfcW5PromBody wfcW5PromS11 =
      .retNormal (.scalar ⟨0xC045000000000000, 8⟩)
        { wfcW5PromS11.memory with
          borrows := disableFrameBorrows wfcW5PromS11.memory.borrows 0 4 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wfc_preserves_imm_ne {b : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry} {skip : Nat}
    (hstate : StateRelLM3_1 b s m allocMap)
    (hpres : ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k)
    (himm : ∀ tf, m.stack.frames = #[tf] → ∀ k, k ≠ skip → IsImmediateFrameLocal tf k) :
    ∀ tf', m'.stack.frames = #[tf'] → ∀ k, k ≠ skip → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, htf, _⟩ := id hstate
  exact fun tf' htf' k hne => hpres tf tf' htf htf' k (himm tf htf k hne)

/-- **(W5f-1b) end-to-end two-sided promoted `&raw` + float-cast + Tree Borrows invalidation +
`StorageDead` stack deallocation + `return` witness from program entry** over non-empty 64-bit
`wfcStage1Layouts` (mirroring `Anneal.CastStage1Tests.promotedRawFloatBody` 1-to-1):
after `StorageLive(_1.._3)` (`WfcRun` from `initMachineState` / `wfcMiriEntry`),
`_2 = &raw mut _1` promotes `_1 : i64` into `allocMap = [wfcW5PromE1]` (`perm = .active`) at
`AllocId 1`; `_1 = const -42.75_f64 as i64` writes `-42_i64` into `lean-miri`'s stack allocation at
`AllocId 1` (`MiriHoldsIndirectScalar`) and transitions `wfcW5PromE1` to `.disabled`
(`allocDead = false`); `_3 = copy _1 as f32` reads `AllocId 1` into immediate `_3` (`-42.0_f32`);
`_1 = move _3 as i64` deinitializes `_3` (`MiriHoldsUninit`) and writes `-42_i64` back into
`AllocId 1`; `_0 = copy _1 as f64` reads `AllocId 1` into immediate `_0` (`-42.0_f64`);
`StorageDead(_3); StorageDead(_2); StorageDead(_1)` retires `wfcW5PromE1` (`allocDead = true`),
frees `AllocId 1` from `lean-miri` live memory (`MiriPromotedFreed`), and restores `WfcAllImm`;
and `wfc_step_return_any` pops the root frame and returns `-42.0_f64` in both machines! -/
theorem wfcW5_promoted_raw_pipeline_end_to_end :
    initMachineState wfcW5PromBody [] = wfcW5PromS0 ∧
    ∃ mₚ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState,
      let b := wfcW5PromBody
      let hooks := annealStepHooksFloat b.localDecls b.layouts
      WfcRun b wfcW5PromS0 (wfcMiriEntry b wfcF64Ty) wfcW5PromS3 mₚ ∧
      stepMirFn b wfcW5PromS3 = .step wfcW5PromS4 ∧
      Miri.Interpreter.Step.step hooks () mₚ = (m₁, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS4 m₁ [wfcW5PromE1] ∧
      wfcW5PromE1.perm = .active ∧
      MiriHoldsIndirectUninit m₁ 1 floatWitAllocId1 (Miri.ABI.Size.ofBytes 8) ∧
      stepMirFn b wfcW5PromS4 = .step wfcW5PromS5 ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS5 m₂ wfcW5PromMap2 ∧
      wfcW5PromMap2 = [{ wfcW5PromE1 with perm := .disabled, allocDead := false }] ∧
      MiriHoldsIndirectScalar m₂ 1 floatWitAllocId1 ⟨0xFFFFFFFFFFFFFFD6, 8⟩ ∧
      stepMirFn b wfcW5PromS5 = .step wfcW5PromS6 ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS6 m₃ wfcW5PromMap2 ∧
      MiriHoldsScalar m₃ 3 ⟨0xC2280000, 4⟩ ∧
      stepMirFn b wfcW5PromS6 = .step wfcW5PromS7 ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS7 m₄ wfcW5PromMap2 ∧
      MiriHoldsUninit m₄ 3 ∧
      MiriHoldsIndirectScalar m₄ 1 floatWitAllocId1 ⟨0xFFFFFFFFFFFFFFD6, 8⟩ ∧
      stepMirFn b wfcW5PromS7 = .step wfcW5PromS8 ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS8 m₅ wfcW5PromMap2 ∧
      MiriHoldsScalar m₅ 0 ⟨0xC045000000000000, 8⟩ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS11 m₈ wfcW5PromMapDead ∧
      wfcW5PromMapDead = [{ wfcW5PromE1 with perm := .disabled, allocDead := true }] ∧
      MiriPromotedFreed m₈ 1 floatWitAllocId1 ∧
      WfcAllImm m₈ ∧
      WfcReturns b wfcW5PromS11 m₈ (.scalar ⟨0xC045000000000000, 8⟩) := by
  have hph : ∀ p, wfcW5PromBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h0, hp1, hp2, hp3, hs₁, hs₂, hs₃, hs₄, hs₅, hd3, hd2, hd1, hret⟩ := wfcW5Prom_anneal_run
  have hrel_ent : StateRelLM3_1 wfcW5PromBody wfcW5PromS0
      (wfcMiriEntry wfcW5PromBody wfcF64Ty) [] := by
    rw [← h0]; exact wfc_stateRel_entry _ _ rfl rfl rfl rfl rfl rfl (by decide)
  obtain ⟨p₁, e₁, r₁, q₁, hm_p₁⟩ :=
    wfc_step_storageLive_mem hrel_ent (wfc_allImm_entry _ _) hph rfl rfl rfl hp1
  obtain ⟨p₂, e₂, r₂, q₂, hm_p₂⟩ := wfc_step_storageLive_mem r₁ q₁ hph rfl rfl rfl hp2
  obtain ⟨p₃, e₃, r₃, q₃, hm_p₃⟩ := wfc_step_storageLive_mem r₂ q₂ hph rfl rfl rfl hp3
  have hmach : p₃.machine = AnnealMachine.empty := hm_p₃.trans (hm_p₂.trans hm_p₁)
  rcases p₃ with ⟨stackₚ, machₚ⟩
  dsimp only at hmach
  subst hmach
  have hrun : WfcRun wfcW5PromBody wfcW5PromS0 (wfcMiriEntry wfcW5PromBody wfcF64Ty) wfcW5PromS3
      { stack := stackₚ, machine := AnnealMachine.empty } :=
    .step hp1 e₁ r₁ (.step hp2 e₂ r₂ (.step hp3 e₃ r₃ (.refl _ _)))
  -- Step 1: `_2 = &raw mut _1`
  have hm_eq₁ := step_float_eq_annealStepHooks_at_stmt r₃ true annealChooseQuietedNaN rfl rfl rfl
  have hr₁ := step_rawPtr_addrOf_lm3_1_simulation r₃ hph rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₃ tf htf 2, q₃ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁_base, hrel₁⟩ := wfc_step_of_stepRel hr₁ hs₁
  have hm₁ : Miri.Interpreter.Step.step
      (annealStepHooksFloat wfcW5PromBody.localDecls wfcW5PromBody.layouts) ()
      { stack := stackₚ, machine := AnnealMachine.empty } = (m₁, .ok true) := hm_eq₁.trans hm₁_base
  have hmap₁_eq :
      [rawPtrAllocMapEntry wfcW5PromBody.localDecls wfcW5PromBody.layouts .mut 1
        wfcW5PromS3.memory.nextTag
        ⟨AnnealMachine.empty.memory.nextAllocId,
          AllocIdSupplyReady.empty.nonzero⟩] = [wfcW5PromE1] := rfl
  have hrel₁' : StateRelLM3_1 wfcW5PromBody wfcW5PromS4 m₁ [wfcW5PromE1] :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS4 m₁) hmap₁_eq).mp hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_supply r₃ rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨q₃ tf htf 2, q₃ tf htf 1⟩) AllocIdSupplyReady.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 32 by decide)
    (fun h => nomatch h) hm₁_base
  obtain ⟨tfₚ, htfₚ, _⟩ := id r₃
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step tfₚ tf₁ htfₚ htf₁ k hne (q₃ tfₚ htfₚ k)
  -- Step 2: `_1 = const -42.75_f64 as i64` (writes into promoted `_1`, disables `wfcW5PromE1`)
  have hcan8 : (0xC045600000000000 : Nat) < scalarModulus 8 := by decide
  have hr₂ := step_cast_float_constant_anyLocal_simulation hrel₁' hph rfl rfl rfl
    (.floatToInt (t := .signed .i64) rfl rfl) rfl rfl wfcVSB8 hcan8 rfl
    (fun _ _ => Or.inr ⟨wfcW5PromE1, .head _, rfl⟩)
  obtain ⟨m₂, hm₂, hrel₂⟩ := wfc_step_of_stepRel hr₂ hs₂
  have hp₂ := step_cast_float_constant_anyLocal_preserves hrel₁' true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl (.floatToInt (t := .signed .i64) rfl rfl) rfl rfl wfcVSB8
    hcan8 rfl (fun h => nomatch h) (fun _ _ => Or.inr ⟨wfcW5PromE1, .head _, rfl⟩) rfl m₂ hm₂
  have himm₂ := wfc_preserves_imm_ne hrel₁' hp₂.2 himm₁
  have he₂ : { wfcW5PromE1 with perm := .disabled, allocDead := false } ∈ wfcW5PromMap2 := .head _
  -- Step 3: `_3 = copy _1 as f32` (reads promoted `_1` into immediate `_3`)
  have hmap₃_eq : updateAllocMapOnWrite wfcW5PromMap2 3 none = wfcW5PromMap2 := rfl
  have hr₃ := step_cast_float_copy_anyLocal_simulation hrel₂ hph rfl rfl rfl rfl
    (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
    (fun tf₂ htf₂ => Or.inl (himm₂ tf₂ htf₂ 3 (by decide)))
  obtain ⟨m₃, hm₃, hrel₃_raw⟩ := wfc_step_of_stepRel hr₃ hs₃
  have hrel₃ : StateRelLM3_1 wfcW5PromBody wfcW5PromS6 m₃ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS6 m₃) hmap₃_eq).mp hrel₃_raw
  have hp₃ := step_cast_float_copy_anyLocal_preserves hrel₂ true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl rfl (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun h => nomatch h) (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
    (fun tf₂ htf₂ => Or.inl (himm₂ tf₂ htf₂ 3 (by decide))) rfl m₃ hm₃
  have himm₃ := wfc_preserves_imm_ne hrel₂ hp₃.2 himm₂
  -- Step 4: `_1 = move _3 as i64` (moves immediate `_3` into promoted `_1`)
  have hmap₄_eq : updateAllocMapOnWrite wfcW5PromMap2 1 none = wfcW5PromMap2 := rfl
  have hr₄ := step_cast_float_move_anyLocal_simulation hrel₃ hph rfl rfl rfl rfl
    (.floatToInt (t := .signed .i64) rfl rfl) rfl
    (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 3 (by decide))
    (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
  obtain ⟨m₄, hm₄, hrel₄_raw⟩ := wfc_step_of_stepRel hr₄ hs₄
  have hrel₄ : StateRelLM3_1 wfcW5PromBody wfcW5PromS7 m₄ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS7 m₄) hmap₄_eq).mp hrel₄_raw
  have hp₄ := step_cast_float_move_anyLocal_preserves hrel₃ true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl rfl (.floatToInt (t := .signed .i64) rfl rfl) rfl
    (fun h => nomatch h) (fun tf₃ htf₃ => himm₃ tf₃ htf₃ 3 (by decide))
    (fun _ _ => Or.inr ⟨_, he₂, rfl⟩) rfl m₄ hm₄
  have himm₄ := wfc_preserves_imm_ne hrel₃ hp₄.2 himm₃
  -- Step 5: `_0 = copy _1 as f64` (reads promoted `_1` into immediate `_0`)
  have hmap₅_eq : updateAllocMapOnWrite wfcW5PromMap2 0 none = wfcW5PromMap2 := rfl
  have hr₅ := step_cast_float_copy_anyLocal_simulation hrel₄ hph rfl rfl rfl rfl
    (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
    (fun tf₄ htf₄ => Or.inl (himm₄ tf₄ htf₄ 0 (by decide)))
  obtain ⟨m₅, hm₅, hrel₅_raw⟩ := wfc_step_of_stepRel hr₅ hs₅
  have hrel₅ : StateRelLM3_1 wfcW5PromBody wfcW5PromS8 m₅ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS8 m₅) hmap₅_eq).mp hrel₅_raw
  have hp₅ := step_cast_float_copy_anyLocal_preserves hrel₄ true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl rfl (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun h => nomatch h) (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
    (fun tf₄ htf₄ => Or.inl (himm₄ tf₄ htf₄ 0 (by decide))) rfl m₅ hm₅
  have himm₅ := wfc_preserves_imm_ne hrel₄ hp₅.2 himm₄
  have himm₅_0 : ∀ tf₅, m₅.stack.frames = #[tf₅] → IsImmediateFrameLocal tf₅ 0 :=
    fun tf₅ htf₅ => himm₅ tf₅ htf₅ 0 (by decide)
  -- Epilogue: `StorageDead(_3); StorageDead(_2); StorageDead(_1)`
  have hmap₆_eq : disableAllocMapLocal wfcW5PromMap2 3 = wfcW5PromMap2 := rfl
  obtain ⟨m₆, hm₆, hrel₆_raw, _, hpres₆⟩ :=
    wfc_step_storageDead_any hrel₅ hph rfl rfl rfl (by decide) hd3
  have hrel₆ : StateRelLM3_1 wfcW5PromBody wfcW5PromS9 m₆ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS9 m₆) hmap₆_eq).mp hrel₆_raw
  have himm₆ := wfc_preserves_imm_ne hrel₅ hpres₆ himm₅
  have hmap₇_eq : disableAllocMapLocal wfcW5PromMap2 2 = wfcW5PromMap2 := rfl
  obtain ⟨m₇, hm₇, hrel₇_raw, _, hpres₇⟩ :=
    wfc_step_storageDead_any hrel₆ hph rfl rfl rfl (by decide) hd2
  have hrel₇ : StateRelLM3_1 wfcW5PromBody wfcW5PromS10 m₇ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS10 m₇) hmap₇_eq).mp hrel₇_raw
  have himm₇ := wfc_preserves_imm_ne hrel₆ hpres₇ himm₆
  obtain ⟨m₈, hm₈, hrel₈, himm₈_1, hpres₈⟩ :=
    wfc_step_storageDead_any hrel₇ hph rfl rfl rfl (by decide) hd1
  obtain ⟨tf₇, htf₇, _⟩ := id hrel₇
  have himm₈ : WfcAllImm m₈ := fun tf₈ htf₈ k =>
    if hk : k = 1 then hk ▸ himm₈_1 tf₈ htf₈
    else hpres₈ tf₇ tf₈ htf₇ htf₈ k (himm₇ tf₇ htf₇ k hk)
  have he_dead : { wfcW5PromE1 with perm := .disabled, allocDead := true } ∈ wfcW5PromMapDead :=
    .head _
  exact ⟨h0, _, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, hrun,
    hs₁, hm₁, hrel₁', rfl,
    wfc_miri_promoted_uninit hrel₁' (.head _) rfl (Or.inr ⟨.signed .i64, rfl⟩) rfl,
    hs₂, hm₂, hrel₂, rfl,
    wfc_miri_promoted_scalar hrel₂ he₂ rfl (Or.inr ⟨.signed .i64, rfl⟩) rfl,
    hs₃, hm₃, hrel₃,
    wfc_miri_scalar_at hrel₃ (fun tf htf => himm₃ tf htf 3 (by decide)) rfl (Or.inl ⟨_, rfl⟩) rfl,
    hs₄, hm₄, hrel₄,
    wfc_miri_uninit_at hrel₄ (fun tf htf => himm₄ tf htf 3 (by decide)) rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_miri_promoted_scalar hrel₄ he₂ rfl (Or.inr ⟨.signed .i64, rfl⟩) rfl,
    hs₅, hm₅, hrel₅,
    wfc_miri_scalar_at hrel₅ himm₅_0 rfl (Or.inl ⟨_, rfl⟩) rfl,
    hm₆, hm₇, hm₈, hrel₈, rfl,
    wfc_miri_promoted_freed hrel₈ he_dead (fun tf htf => himm₈ tf htf 1) rfl rfl,
    himm₈,
    wfc_step_return_any hrel₈ (fun tf htf => himm₈ tf htf 0) hph rfl rfl rfl rfl rfl rfl
      (Or.inl ⟨_, rfl⟩) hret⟩

/-! #### Unpromoted stack-allocated `LocalRel.indirect` float multi-step witness ending in `return` -/

/-- Unpromoted `LocalRel.indirect` stack-local bundle for local `idx` of type `ty` at `allocId`:
`allocId < 2³²`, cached base address, unique live `StackScalarAllocShape` entry, and indirect
frame slot `stackAllocPlace allocId`. -/
def WfcIndirectAt (b : CapturedMir) (m : AnnealStepState) (idx : Local) (ty : Ty)
    (allocId : Miri.Memory.AllocId) : Prop :=
  allocId.value.toNat < 2 ^ 32 ∧
  m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) ∧
  (∃ localAlloc,
    m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) ∧
    (∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂) ∧
    StackScalarAllocShape (translateTy ty b.layouts).layout.size localAlloc.allocation) ∧
  (∀ tf, m.stack.frames = #[tf] →
    ∃ lay, tf.locals[idx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)

private theorem wfc_list_filter_ne_find_none {β : Type}
    (l : List (Miri.Memory.AllocId × β)) (id₀ : Miri.Memory.AllocId) :
    (l.filter (fun x => x.1 != id₀)).find? (fun x => x.1 == id₀) = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h : hd.1 = id₀
    · subst h; simp [ih]
    · have hne : (hd.1 != id₀) = true := bne_iff_ne.mpr h
      have hbeq : (hd.1 == id₀) = false := beq_false_of_ne h
      simp [hne, hbeq, ih]

private theorem wfc_filter_push_find_and_uniq {β : Type}
    (arr : Array (Miri.Memory.AllocId × β)) (id₀ : Miri.Memory.AllocId) (la' : β) :
    ((arr.filter (fun x => x.1 != id₀)).push (id₀, la')).find? (fun x => x.1 == id₀) =
        some (id₀, la') ∧
      ∀ la₁ la₂,
        (id₀, la₁) ∈ ((arr.filter (fun x => x.1 != id₀)).push (id₀, la')).toList →
        (id₀, la₂) ∈ ((arr.filter (fun x => x.1 != id₀)).push (id₀, la')).toList →
        la₁ = la₂ := by
  refine ⟨?_, ?_⟩
  · rw [← Array.find?_toList, Array.toList_push, Array.toList_filter, List.find?_append,
      wfc_list_filter_ne_find_none]
    simp
  · intro la₁ la₂ h₁ h₂
    rw [Array.toList_push, Array.toList_filter, List.mem_append] at h₁ h₂
    have h1 : la₁ = la' := by
      rcases h₁ with hm | hm
      · exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp hm).2)
      · exact (Prod.mk.inj (List.mem_singleton.mp hm)).2
    have h2 : la₂ = la' := by
      rcases h₂ with hm | hm
      · exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp hm).2)
      · exact (Prod.mk.inj (List.mem_singleton.mp hm)).2
    exact h1.trans h2.symm

/-- **Packaged indirect float-destination `constant` step** (`_d = const c as castTy`): runs
`step_cast_float_constant_indirect_floatDst_simulation`, preserves `WfcIndirectAt` on `dstIdx` and
`IsImmediateFrameLocal` on all other immediate locals, and reads back `MiriHoldsIndirectScalar`. -/
theorem wfc_step_constant_indirect_floatDst {b : CapturedMir} {s s' : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m [])
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty b.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {allocId : Miri.Memory.AllocId}
    (hind : WfcIndirectAt b m dstIdx dstDecl.ty allocId)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩)))
    (hptr8 : layoutPointerBytes b.layouts = 8 := by rfl) :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_1 b s' m' [] ∧
      WfcIndirectAt b m' dstIdx dstDecl.ty allocId ∧
      (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
      MiriHoldsIndirectScalar m' dstIdx allocId ⟨bits, w⟩ := by
  obtain ⟨hid_lt, hbase, ⟨localAlloc, hfind_la, _, hshape_la⟩, hind_dst⟩ := hind
  have hr := step_cast_float_constant_indirect_floatDst_simulation hstate hphase hbb hstmt
    hdecl_dst hsig hdst_ty hdst_fmt hval hsz hcan hlaysz hid_lt hbase hfind_la hshape_la hind_dst
    hptr8
  obtain ⟨m', hm', hrel_st⟩ := wfc_step_of_stepRel hr hs
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq b.localDecls b.layouts true
    annealChooseQuietedNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty b.layouts = translateTy castTy b.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty b.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty b.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty b.layouts)
  have hlay_tfa : tfa.locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)),
        some (translateTy dstDecl.ty b.layouts)⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
    injection hlay_0 with hm0
    rw [hm0]
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand b.localDecls b.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty b.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar b.layouts]
  obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode b.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩) hsig hrel
    hlaysz (fun h => nomatch h) (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
      localAlloc.allocation := hsz' ▸ hshape_la
  obtain ⟨alloc', hw_alloc, _, hshape_alloc', _, _⟩ := hshape_sc.writeScalar_readScalar hrel'
  have hmsc_sz : msc'.size = (translateTy dstDecl.ty b.layouts).layout.size := by
    rw [hrel'.size_eq, ← hsz']
  have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy dstDecl.ty b.layouts).layout.size)
      (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
    rw [← hmsc_sz]; exact hw_alloc
  have hget_dm := frame_getLocal_of_getElem? tfa dstIdx _ hlay_tfa
  have hw_ind := annealWriteImmediate_indirect
    (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tfa]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty b.layouts) rfl hget_dm
  have hw_m := annealWriteMemoryPlace_floatCastScalar_zero_offset_ok hdst_scalar hid_lt hbase
    hfind_la hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hw_alloc_lay
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfa]⟩ })
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat b.localDecls b.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      ({ stack := ⟨#[tfa]⟩
         machine := { m.machine with
           memory := { m.machine.memory with
             live := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
               (allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast, hw_ind, stackAllocPlace,
      hw_m]
  have hstep_eq := miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
    rfl hfr.location_eq
  have hm'_shape := hm'.symm.trans hstep_eq
  injection hm'_shape with hm'_eq _
  obtain ⟨hfind', huniq'⟩ := wfc_filter_push_find_and_uniq m.machine.memory.live allocId
    ⟨localAlloc.kind, alloc'⟩
  have hind' : WfcIndirectAt b m' dstIdx dstDecl.ty allocId := by
    subst hm'_eq
    refine ⟨hid_lt, hbase, ⟨⟨localAlloc.kind, alloc'⟩, hfind', huniq', hsz'.symm ▸ hshape_alloc'⟩,
      ?_⟩
    intro tf' htf'
    injection htf' with h₁; injection h₁ with h₂; subst h₂
    exact ⟨_, hlay_tfa⟩
  have himm_pres : ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k := by
    subst hm'_eq
    intro tf₀ tf' htf₀ htf' k hk
    rw [hframes] at htf₀
    injection htf₀ with h0; injection h0 with h0'; subst h0'
    injection htf' with h1; injection h1 with h1'; subst h1'
    exact hk.cache_layout hlt_d _
  exact ⟨m', hm', hrel_st, hind', himm_pres,
    wfc_miri_indirect_scalar hrel_st hdecl_dst hdst_scalar hslot
      (by subst hm'_eq; exact hbase) (by subst hm'_eq; exact hfind')
      (by subst hm'_eq; exact huniq') hind'.2.2.2⟩

/-- **Packaged indirect float-source `copy` step** (`_d = copy _s as castTy` into an immediate
destination `dstIdx ≠ srcIdx`): runs `step_cast_float_copy_indirect_float_simulation`, preserves
`WfcIndirectAt` on `srcIdx` and `IsImmediateFrameLocal` on all immediate locals, and reads back
both `MiriHoldsScalar` on `dstIdx` and `MiriHoldsIndirectScalar` on `srcIdx`. -/
theorem wfc_step_copy_indirect_float {b : CapturedMir} {s s' : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m [])
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    (hind : WfcIndirectAt b m srcIdx srcDecl.ty allocId)
    {sc_s : MirAst.ScalarInt} (hslot_src : get? s.frame.locals srcIdx = some (.init (.scalar sc_s)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot_dst : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩)))
    (hslot_src' : get? s'.frame.locals srcIdx = some (.init (.scalar sc_s)))
    (hptr8 : layoutPointerBytes b.layouts = 8 := by rfl) :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_1 b s' m' [] ∧
      WfcIndirectAt b m' srcIdx srcDecl.ty allocId ∧
      (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
      MiriHoldsScalar m' dstIdx ⟨bits, w⟩ ∧
      MiriHoldsIndirectScalar m' srcIdx allocId sc_s := by
  obtain ⟨hid_lt, hbase, ⟨localAlloc, hfind_la, huniq_la, hshape_la⟩, hind_src⟩ := hind
  have hr := step_cast_float_copy_indirect_float_simulation hstate hphase hbb hstmt hdecl_dst
    hdecl_src hsig hdst_ty hid_lt hbase hfind_la huniq_la hshape_la hind_src
    (fun v hv => ⟨sc_s, by
      rw [hslot_src] at hv; injection hv with h1; injection h1 with h2; exact h2.symm⟩)
    (fun tf htf => Or.inl (himm_dst tf htf)) hptr8
  obtain ⟨m', hm', hrel_st⟩ := wfc_step_of_stepRel hr hs
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq b.localDecls b.layouts true
    annealChooseQuietedNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy
    span m
  have hdstT : translateTy dstDecl.ty b.layouts = translateTy castTy b.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty b.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty b.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty b.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s0, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty b.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty b.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_tfa : tfa.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hne_ds]
    exact hlay_0
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    rw [hmls_s] at hlay_tfa; exact Option.some.inj hlay_tfa
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  obtain ⟨_, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry) hmls_s_ind hbase
    hfind_la huniq_la (hsig.src_scalar.size_ne_zero b.layouts)
  rw [hslot_src] at hslot_s0; injection hslot_s0 with hss_eq
  obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc_s hss_eq.symm
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar hid_lt
    hbase hfind_la hshape_la.byteSize_eq (borTag := Miri.Memory.BorTag.one)
    (st := { m with stack := ⟨#[tfb]⟩ })
  have hri_ok : annealReadImmediate
      ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty b.layouts⟩
      { m with stack := ⟨#[tfb]⟩ } =
      .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } := by
    rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
      hread_mem, hread_ok]
    dsimp only []
    rw [hsig.src_scalar.validateScalar_true msc]; rfl
  have hcast_red := cast_floatCast_of_readImmediate_scalar b.layouts true annealChooseQuietedNaN
    hsig (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
    (.fromScalarInt msc) hri_ok
  obtain ⟨_, msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode b.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩) hsig hrel
    hsz (fun h => nomatch h) (.local 0 dstIdx none tf.localsIdentity)
  have hcast_ind :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat b.layouts true annealChooseQuietedNaN) () 16
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty b.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
      annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } := by
    rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
  rw [← hdstT] at hsz'
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat b.localDecls b.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩)
        { m with stack := ⟨#[tfb]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    ((himm_dst tf hframes).cache_layout hlt_d _).cache_layout hlt_sa _
  have hp := finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_b rfl
    (fun _ hk => (hk.cache_layout hlt_d _).cache_layout hlt_sa _) hbb hstmt hdecl_dst hdst_scalar
    (Or.inl himm_d_tfb) hrel' hsz' hm_write m' hm'
  -- Also extract `m'.machine = m.machine` and `tf'.locals[srcIdx]?` from `annealWriteImmediate_live`
  obtain ⟨slot_dm, mls_dm, _, hlt_dm, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_dst
  have hsd_dead : slot_dm ≠ .dead := fun hd => hlive_dst (hd ▸ hslot_dm)
  have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
    cases hloc_dm with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfb _ hmls_dm mp)
      | dead _ _ => exact absurd rfl hsd_dead
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
  have hdm_live : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
    rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
  have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty b.layouts) rfl hlt_dm
    (frame_getLocal_of_getElem? tfb dstIdx _ hdm_live)
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat b.localDecls b.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[{ tfb with
          locals := tfb.locals.set dstIdx
            { tfb.locals[dstIdx]'hlt_dm with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
            hlt_dm }]⟩ }, .ok ()) := by
    rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
  have hstep_eq := miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
    rfl (hstate_b.frame_rel_singleton rfl).location_eq
  have hm'_shape := hm'.symm.trans hstep_eq
  injection hm'_shape with hm'_eq _
  have hind' : WfcIndirectAt b m' srcIdx srcDecl.ty allocId := by
    subst hm'_eq
    refine ⟨hid_lt, hbase, ⟨localAlloc, hfind_la, huniq_la, hshape_la⟩, ?_⟩
    intro tf' htf'
    injection htf' with h1; injection h1 with h2; subst h2
    dsimp only []
    rw [Array.getElem?_set_ne _ hne_ds]
    dsimp [tfb, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_sa, hmls_s']
    exact ⟨_, rfl⟩
  exact ⟨m', hm', hrel_st, hind', hp.2,
    wfc_miri_scalar_at hrel_st
      (fun tf' htf' => hp.2 tf tf' hframes htf' dstIdx (himm_dst tf hframes))
      hdecl_dst hdst_scalar hslot_dst,
    wfc_miri_indirect_scalar hrel_st hdecl_src hsig.src_scalar hslot_src'
      (by subst hm'_eq; exact hbase)
      (by subst hm'_eq; exact hfind_la) (by subst hm'_eq; exact huniq_la) hind'.2.2.2⟩

/-- **Packaged indirect float-source `move` step** (`_d = move _s as castTy` into an immediate
destination `dstIdx ≠ srcIdx`): runs `step_cast_float_move_indirect_float_simulation`, deinitializes
`srcIdx` to immediate `.uninit` (`MiriHoldsUninit`), preserves `IsImmediateFrameLocal` on all
immediate locals, and reads back `MiriHoldsScalar` on `dstIdx`. -/
theorem wfc_step_move_indirect_float {b : CapturedMir} {s s' : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM3_1 b s m [])
    (hphase : ∀ p, b.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? b.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? b.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? b.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    (hind : WfcIndirectAt b m srcIdx srcDecl.ty allocId)
    {sc_s : MirAst.ScalarInt} (hslot_src : get? s.frame.locals srcIdx = some (.init (.scalar sc_s)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    {bits w : Nat} (hs : stepMirFn b s = .step s')
    (hslot_dst : get? s'.frame.locals dstIdx = some (.init (.scalar ⟨bits, w⟩)))
    (hslot_src' : get? s'.frame.locals srcIdx = some .uninit)
    (hptr8 : layoutPointerBytes b.layouts = 8 := by rfl) :
    ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_1 b s' m' [] ∧
      (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
        ∀ k, (k = srcIdx ∨ IsImmediateFrameLocal tf k) → IsImmediateFrameLocal tf' k) ∧
      MiriHoldsScalar m' dstIdx ⟨bits, w⟩ ∧
      MiriHoldsUninit m' srcIdx := by
  obtain ⟨hid_lt, hbase, ⟨localAlloc, hfind_la, huniq_la, hshape_la⟩, hind_src⟩ := hind
  have hr := step_cast_float_move_indirect_float_simulation hstate hphase hbb hstmt hdecl_dst
    hdecl_src hsig hdst_ty hid_lt hbase hfind_la huniq_la hshape_la hind_src (fun _ h => nomatch h)
    (fun v hv => ⟨sc_s, by
      rw [hslot_src] at hv; injection hv with h1; injection h1 with h2; exact h2.symm⟩)
    (fun _ tf htf => Or.inl (himm_dst tf htf)) hptr8
  obtain ⟨m', hm', hrel_st⟩ := wfc_step_of_stepRel hr hs
  obtain ⟨tf, hframes, _, _, hfr, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq b.localDecls b.layouts true
    annealChooseQuietedNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy
    span m
  have hdstT : translateTy dstDecl.ty b.layouts = translateTy castTy b.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty b.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty b.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty b.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s0, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty b.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty b.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  let tfc := deinitFrameLocal tfb srcIdx hlt_sb
  have hstate_mid := hstate_b.deinit_unpromoted_local rfl hdecl_src (fun _ h => nomatch h) hlt_sb
  have hlay_tfa : tfa.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hne_ds]
    exact hlay_0
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    rw [hmls_s] at hlay_tfa; exact Option.some.inj hlay_tfa
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_0⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  obtain ⟨_, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry) hmls_s_ind hbase
    hfind_la huniq_la (hsig.src_scalar.size_ne_zero b.layouts)
  rw [hslot_src] at hslot_s0; injection hslot_s0 with hss_eq
  obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc_s hss_eq.symm
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar hid_lt
    hbase hfind_la hshape_la.byteSize_eq (borTag := Miri.Memory.BorTag.one)
    (st := { m with stack := ⟨#[tfc]⟩ })
  have hri_ok : annealReadImmediate
      ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty b.layouts⟩
      { m with stack := ⟨#[tfc]⟩ } =
      .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } := by
    rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
      hread_mem, hread_ok]
    dsimp only []
    rw [hsig.src_scalar.validateScalar_true msc]; rfl
  have hcast_red := cast_floatCast_of_readImmediate_scalar b.layouts true annealChooseQuietedNaN
    hsig (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
    (.fromScalarInt msc) hri_ok
  obtain ⟨_, msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode b.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩) hsig hrel
    hsz (fun h => nomatch h) (.local 0 dstIdx none tf.localsIdentity)
  have hcast_ind :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat b.layouts true annealChooseQuietedNaN) () 16
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty b.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
      annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } := by
    rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
  rw [← hdstT] at hsz'
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat b.localDecls b.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty b.layouts⟩)
        { m with stack := ⟨#[tfc]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
  have himm_tfc : ∀ k, (k = srcIdx ∨ IsImmediateFrameLocal tf k) → IsImmediateFrameLocal tfc k := by
    intro k hk
    rcases hk with rfl | hk_imm
    · intro mls hmls mp hmp
      dsimp only [tfc, deinitFrameLocal] at hmls
      rw [Array.getElem?_set_self hlt_sb] at hmls
      injection hmls with hm_eq
      rw [← hm_eq] at hmp; cases hmp
    · exact ((hk_imm.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb
  have himm_d_tfc : IsImmediateFrameLocal tfc dstIdx := himm_tfc dstIdx (Or.inr (himm_dst tf hframes))
  -- Use `finish_write_anyLocal_preserves` starting from `{ m with stack := ⟨#[tfc]⟩ }`? Note `hm_write`
  -- steps from `m` (whose frame is `tf`), so pass a trivial wrapper on `IsImmediateFrameLocal tfc k`:
  obtain ⟨slot_dm, mls_dm, _, hlt_dm, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hstate_mid.frame_rel_singleton rfl |>.lookup_local hdecl_dst
  have hsd_dead : slot_dm ≠ .dead := by
    intro hd
    dsimp only [] at hslot_dm
    rw [get?_eq_getElem?, List.getElem?_set_ne hne_ds.symm, ← get?_eq_getElem?] at hslot_dm
    exact hlive_dst (hd ▸ hslot_dm)
  have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
    cases hloc_dm with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfc _ hmls_dm mp)
      | dead _ _ => exact absurd rfl hsd_dead
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
  have hdm_live : tfc.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
    rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
  have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty b.layouts) rfl hlt_dm
    (frame_getLocal_of_getElem? tfc dstIdx _ hdm_live)
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat b.localDecls b.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[{ tfc with
          locals := tfc.locals.set dstIdx
            { tfc.locals[dstIdx]'hlt_dm with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
            hlt_dm }]⟩ }, .ok ()) := by
    rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
  have hstep_eq := miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
    rfl (hstate_mid.frame_rel_singleton rfl).location_eq
  have hm'_shape := hm'.symm.trans hstep_eq
  injection hm'_shape with hm'_eq _
  have himm_pres : ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, (k = srcIdx ∨ IsImmediateFrameLocal tf₀ k) → IsImmediateFrameLocal tf' k := by
    subst hm'_eq
    intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp
    rw [hframes] at htf₀
    injection htf₀ with h0; injection h0 with h0'; subst h0'
    injection htf' with h1; injection h1 with h1'; subst h1'
    dsimp only [] at hmls'
    rw [Array.getElem?_set] at hmls'
    split at hmls'
    · injection hmls' with hmls_eq
      subst hmls_eq; cases hmp
    · exact himm_tfc k hk mls' hmls' mp hmp
  exact ⟨m', hm', hrel_st, himm_pres,
    wfc_miri_scalar_at hrel_st
      (fun tf' htf' => himm_pres tf tf' hframes htf' dstIdx (Or.inr (himm_dst tf hframes)))
      hdecl_dst hdst_scalar hslot_dst,
    wfc_miri_uninit_at hrel_st
      (fun tf' htf' => himm_pres tf tf' hframes htf' srcIdx (Or.inl rfl))
      hdecl_src hsig.src_scalar hslot_src'⟩

/-- **(W5f-2) multi-step unpromoted stack-allocated `LocalRel.indirect` float body ending in
`return`** (`_0 : f32` immediate, `_1 : f64` force-allocated `LocalRel.indirect` at `AllocId 1`
initially holding `0.0_f64`, `_2 : i64` immediate):
```text
bb0: _1 = const (2⁵³ + 3)_u64 as f64   // indirect f64 write ↦ 0x4340_0000_0000_0002 at AllocId 1
     _2 = copy _1 as i64               // indirect f64 copy  ↦ 2⁵³ + 4 in immediate _2
     _0 = move _1 as f32               // indirect f64 move  ↦ 2⁵³_f32 (0x5A00_0000), _1 deinitialized
     return
``` -/
def wfcW5IndBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_indirect_float_pipeline"
    [wfcDecl wfcF32Ty, wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64)] 4
    [.assign (local_ 1) (.cast .intToFloat (.constant (wfcConst (wfcUintTy .u64) (2 ^ 53 + 3) 8))
       wfcF64Ty),
     .assign (local_ 2) (.cast .floatToInt (.copy (local_ 1)) (wfcIntTy .i64)),
     .assign (local_ 0) (.cast .floatToFloat (.move (local_ 1)) wfcF32Ty)]

def wfcW5IndS0 : MachineState := wfcAt wfcW5IndBody 0
  [.uninit, .init (.scalar ⟨0, 8⟩), .uninit]
def wfcW5IndS1 : MachineState := wfcAt wfcW5IndBody 1
  [.uninit, .init (.scalar ⟨0x4340000000000002, 8⟩), .uninit]
def wfcW5IndS2 : MachineState := wfcAt wfcW5IndBody 2
  [.uninit, .init (.scalar ⟨0x4340000000000002, 8⟩),
   .init (.scalar ⟨0x0020000000000004, 8⟩)]
def wfcW5IndS3 : MachineState := wfcAt wfcW5IndBody 3
  [.init (.scalar ⟨0x5A000000, 4⟩), .uninit,
   .init (.scalar ⟨0x0020000000000004, 8⟩)]

def wfcW5IndFrame0 : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { wfcFrame wfcW5IndBody wfcF32Ty with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none },
      { value := .live (.immediate .uninit), layout := none }] }

def wfcW5IndMiri0 : AnnealStepState :=
  { stack := ⟨#[wfcW5IndFrame0]⟩, machine := floatWitIndMachine }

theorem wfcW5Ind_stateRel_init :
    StateRelLM3_1 wfcW5IndBody wfcW5IndS0 wfcW5IndMiri0 [] := by
  refine (StateRel.mk wfcW5IndFrame0 rfl rfl ⟨translateTy wfcF32Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl ?_).toLM3_1
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 =>
      have hs : slot = .uninit := by simpa [wfcW5IndS0, wfcAt, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [wfcW5IndFrame0] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = wfcDecl wfcF64Ty := by simpa [wfcW5IndBody, wfcBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0, 8⟩) := by
        simpa [wfcW5IndS0, wfcAt, get?] using hslot.symm
      have hm : mls =
          { value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none } := by
        simpa [wfcW5IndFrame0] using hmls.symm
      subst hd hs hm
      refine .indirect (.init (.scalar ⟨0, 8⟩)) (stackAllocPlace floatWitAllocId1) none
        (fun _ h => nomatch h) nofun ?_
      refine MemPlaceRel.mk floatWitAllocId1 Miri.Memory.BorTag.one
        (annealStackBaseAddr floatWitAllocId1) Miri.ABI.Size.ZERO
        { kind := .stack, allocation := floatWitIndAlloc }
        rfl rfl rfl (List.Mem.head _) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (fun h _ => nomatch h) (fun _ _ _ => by decide) ?_
        (fun _ _ _ _ h => nomatch h)
      intro sc h
      injection h with hv
      injection hv with hsc
      subst hsc
      exact ⟨by decide, (fun hb => nomatch hb), (fun hc => nomatch hc),
        extractExceptOk (translateScalarInt ⟨0, 8⟩) (by decide),
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, by decide, by decide⟩,
        by with_unfolding_all rfl⟩
    | _ + 3 => simp [wfcW5IndBody, wfcBody, get?] at hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    have hi1 : i = 1 := by
      match i, hi with
      | 1, _ => rfl
      | 0, h => simp [wfcW5IndFrame0] at h
      | 2, h => simp [wfcW5IndFrame0] at h
      | _ + 3, h => simp [wfcW5IndFrame0] at h
    have hj1 : j = 1 := by
      match j, hj with
      | 1, _ => rfl
      | 0, h => simp [wfcW5IndFrame0] at h
      | 2, h => simp [wfcW5IndFrame0] at h
      | _ + 3, h => simp [wfcW5IndFrame0] at h
    exact absurd (hi1.trans hj1.symm) hij

set_option maxRecDepth 200000 in
theorem wfcW5Ind_anneal_run :
    stepMirFn wfcW5IndBody wfcW5IndS0 = .step wfcW5IndS1 ∧
    stepMirFn wfcW5IndBody wfcW5IndS1 = .step wfcW5IndS2 ∧
    stepMirFn wfcW5IndBody wfcW5IndS2 = .step wfcW5IndS3 ∧
    stepMirFn wfcW5IndBody wfcW5IndS3 = .retNormal (.scalar ⟨0x5A000000, 4⟩) wfcW5IndS3.memory :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **(W5f-2) end-to-end two-sided stack-allocated `LocalRel.indirect` float pipeline ending in
`return`**: starting with `_1 : f64` memory-backed at `AllocId 1` (`0.0_f64`, unpromoted) and
`_0 : f32`, `_2 : i64` immediate:
1. `_1 = const (2⁵³ + 3)_u64 as f64` overwrites `AllocId 1` in `lean-miri`'s stack memory with the
   `roundTiesToEven` result `0x4340_0000_0000_0002` (`2⁵³ + 4`, `MiriHoldsIndirectScalar`);
2. `_2 = copy _1 as i64` reads `AllocId 1` from `lean-miri`'s stack memory into immediate `_2`
   (`0x0020_0000_0000_0004`);
3. `_0 = move _1 as f32` reads `AllocId 1` from `lean-miri`'s stack memory, rounds `2⁵³ + 4` to
   `2⁵³_f32 = 0x5A00_0000` in immediate `_0`, and transitions `_1` from `.indirect` to immediate
   `.uninit` (`MiriHoldsUninit m₃ 1`);
4. `return` pops the root frame and returns `0x5A00_0000_f32` in both machines! -/
theorem wfcW5_indirect_float_pipeline_end_to_end :
    ∃ m₁ m₂ m₃ : AnnealStepState,
      let b := wfcW5IndBody
      let hooks := annealStepHooksFloat b.localDecls b.layouts
      stepMirFn b wfcW5IndS0 = .step wfcW5IndS1 ∧
      Miri.Interpreter.Step.step hooks () wfcW5IndMiri0 = (m₁, .ok true) ∧
      StateRelLM3_1 b wfcW5IndS1 m₁ [] ∧
      MiriHoldsIndirectScalar m₁ 1 floatWitAllocId1 ⟨0x4340000000000002, 8⟩ ∧
      stepMirFn b wfcW5IndS1 = .step wfcW5IndS2 ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b wfcW5IndS2 m₂ [] ∧
      MiriHoldsScalar m₂ 2 ⟨0x0020000000000004, 8⟩ ∧
      MiriHoldsIndirectScalar m₂ 1 floatWitAllocId1 ⟨0x4340000000000002, 8⟩ ∧
      stepMirFn b wfcW5IndS2 = .step wfcW5IndS3 ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b wfcW5IndS3 m₃ [] ∧
      MiriHoldsScalar m₃ 0 ⟨0x5A000000, 4⟩ ∧
      MiriHoldsUninit m₃ 1 ∧
      WfcReturns b wfcW5IndS3 m₃ (.scalar ⟨0x5A000000, 4⟩) := by
  have hph : ∀ p, wfcW5IndBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hs₁, hs₂, hs₃, hret⟩ := wfcW5Ind_anneal_run
  have hind₀ : WfcIndirectAt wfcW5IndBody wfcW5IndMiri0 1 wfcF64Ty floatWitAllocId1 := by
    refine ⟨by decide, by decide, ⟨{ kind := .stack, allocation := floatWitIndAlloc },
      rfl, ?_, floatWitIndAlloc_shape⟩, ?_⟩
    · intro la₁ la₂ h₁ h₂
      have e₁ := List.mem_singleton.mp h₁
      have e₂ := List.mem_singleton.mp h₂
      rw [(Prod.mk.inj e₁).2, (Prod.mk.inj e₂).2]
    · intro tf htf
      injection htf with h1; injection h1 with h2; subst h2
      exact ⟨none, rfl⟩
  have himm₀_0 : IsImmediateFrameLocal wfcW5IndFrame0 0 := by
    intro mls hmls mp hmp
    simp [wfcW5IndFrame0] at hmls; subst hmls; cases hmp
  have himm₀_2 : IsImmediateFrameLocal wfcW5IndFrame0 2 := by
    intro mls hmls mp hmp
    simp [wfcW5IndFrame0] at hmls; subst hmls; cases hmp
  obtain ⟨m₁, hm₁, hrel₁, hind₁, himm_p₁, hsc_ind₁⟩ :=
    wfc_step_constant_indirect_floatDst wfcW5Ind_stateRel_init hph rfl rfl rfl
      (.intToFloat (t := .unsigned .u64) rfl rfl) rfl rfl rfl wfcVSB8 (by decide) rfl hind₀ hs₁ rfl
  obtain ⟨m₂, hm₂, hrel₂, hind₂, himm_p₂, hsc₂, hsc_ind₂⟩ :=
    wfc_step_copy_indirect_float hrel₁ hph rfl rfl rfl rfl
      (.floatToInt (t := .signed .i64) rfl rfl) rfl (by decide) hind₁ rfl (fun h => nomatch h)
      (fun tf₁ htf₁ => himm_p₁ _ tf₁ rfl htf₁ 2 himm₀_2) hs₂ rfl rfl
  obtain ⟨tf₁_w, htf₁_w, _⟩ := id hrel₁
  obtain ⟨m₃, hm₃, hrel₃, himm_p₃, hsc₃, hun₃⟩ :=
    wfc_step_move_indirect_float hrel₂ hph rfl rfl rfl rfl (.floatToFloat rfl rfl) rfl
      (by decide) hind₂ rfl (fun h => nomatch h)
      (fun tf₂ htf₂ => himm_p₂ tf₁_w tf₂ htf₁_w htf₂ 0 (himm_p₁ _ tf₁_w rfl htf₁_w 0 himm₀_0))
      hs₃ rfl rfl
  obtain ⟨tf₂_w, htf₂_w, _⟩ := id hrel₂
  have himm₃_0 : ∀ tf₃, m₃.stack.frames = #[tf₃] → IsImmediateFrameLocal tf₃ 0 :=
    fun tf₃ htf₃ => himm_p₃ tf₂_w tf₃ htf₂_w htf₃ 0
      (Or.inr (himm_p₂ tf₁_w tf₂_w htf₁_w htf₂_w 0 (himm_p₁ _ tf₁_w rfl htf₁_w 0 himm₀_0)))
  exact ⟨m₁, m₂, m₃,
    hs₁, hm₁, hrel₁, hsc_ind₁,
    hs₂, hm₂, hrel₂, hsc₂, hsc_ind₂,
    hs₃, hm₃, hrel₃, hsc₃, hun₃,
    wfc_step_return_any hrel₃ himm₃_0 hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-! ## Axiom guards

Every public theorem of this file depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): `#guard_msgs` fails the build if a proof ever starts
depending on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any other axiom. -/

section AxiomGuards

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcFrame_locals_getElem?' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcFrame_locals_getElem?

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_allImm_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_allImm_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcEntryFrame_locals_getElem?' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcEntryFrame_locals_getElem?

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcEntrySlots_get?' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcEntrySlots_get?

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_allImm_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_allImm_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_scalar_at' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_scalar_at

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_scalar' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_scalar

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_uninit_at' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_uninit_at

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_uninit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_uninit

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_indirect_scalar' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_indirect_scalar

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_promoted_scalar' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_promoted_scalar

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_promoted_uninit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_promoted_uninit

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_miri_promoted_freed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_miri_promoted_freed

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_of_stepRel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_of_stepRel

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_ub_of_stepRel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_ub_of_stepRel

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_ret_of_stepRel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_ret_of_stepRel

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_constant' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_constant

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_copy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_copy

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_move' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_move

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_ub_copy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_ub_copy

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_ub_move' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_ub_move

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_return_any' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_return_any

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_return' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_return

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageLive' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageLive

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageLive_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageLive_mem

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageDead_any' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageDead_any

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageDead' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageDead

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcLockstep_eq_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcLockstep_eq_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcReturns_eq_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcReturns_eq_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcRun_iff_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcRun_iff_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_detAgrees_f2f' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_detAgrees_f2f

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageLive_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageLive_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_constant_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_constant_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_copy_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_copy_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_move_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_move_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_return_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_return_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcVSB1' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcVSB1

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcVSB2' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcVSB2

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcVSB4' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcVSB4

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcVSB8' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcVSB8

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcVSB16' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcVSB16

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_deterministic_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_deterministic_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_convert' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_convert

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_convert_table' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_convert_table

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2Det_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2Det_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_deterministic_canonicalization' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_deterministic_canonicalization

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_deterministic_lockstep_cases' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_deterministic_lockstep_cases

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2Sel_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2Sel_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_selectors_exact' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_selectors_exact

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_constant_snan_index' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_constant_snan_index

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2Sel4_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2Sel4_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_selectors_snan_4_5_and_out_of_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_selectors_snan_4_5_and_out_of_range

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_selectors_copy_and_move' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_selectors_copy_and_move

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_nanChoices_exact' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_nanChoices_exact

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_toInteger' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_toInteger

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_toInteger_all_targets' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_toInteger_all_targets

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_saturation_cliffs' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_saturation_cliffs

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_stateRel_entry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_stateRel_entry

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_deterministic_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_deterministic_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_fromInteger' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_fromInteger

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_fromInteger_all_sources' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_fromInteger_all_sources

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_signed_negative_ties' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_signed_negative_ties

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_ties_all_wide_sources' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_ties_all_wide_sources

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_evalFloatCast_layouts_eq' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_evalFloatCast_layouts_eq

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_translateTy_floatCast_eq' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_translateTy_floatCast_eq

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_cast_two_sided_mode' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_cast_two_sided_mode

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_cast_two_sided' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_cast_two_sided

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcCast_two_sided_table' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcCast_two_sided_table

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcCast_deterministic_and_f16_f128_boundary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcCast_deterministic_and_f16_f128_boundary

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5U_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5U_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_uninit_source_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_uninit_source_ub

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5M_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5M_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_moved_from_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_moved_from_ub

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_stateRel_entry2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_stateRel_entry2

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_allImm_entry2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_allImm_entry2

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5D_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5D_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_dead_source_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_dead_source_ub

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5H_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5H_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_f16_f128_fail_closed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_f16_f128_fail_closed

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5UninitF16F128_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5UninitF16F128_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_f16_f128_uninit_source_vs_target' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_f16_f128_uninit_source_vs_target

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_bool_char_boundary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_bool_char_boundary

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5PromU_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5PromU_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_promoted_uninit_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_promoted_uninit_ub

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5PromDead_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5PromDead_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_rawPtr_dead_and_promoted_dead_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_rawPtr_dead_and_promoted_dead_ub

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5Prom_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5Prom_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_promoted_raw_pipeline_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_promoted_raw_pipeline_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_constant_indirect_floatDst' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_constant_indirect_floatDst

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_copy_indirect_float' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_copy_indirect_float

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_move_indirect_float' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_move_indirect_float

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5Ind_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5Ind_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5Ind_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5Ind_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_indirect_float_pipeline_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_indirect_float_pipeline_end_to_end

end AxiomGuards

end LeanMiriSpec.Correspondence.WitFloatCast
