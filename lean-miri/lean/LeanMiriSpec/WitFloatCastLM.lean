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

* **Part 0 (machinery)**: `wfc_stateRel_init` (post-`StorageLive`-prologue entry states of any
  body are `StateRelLM3_1`-related), the lockstep predicates `WfcLockstep` / `WfcReturns` /
  `WfcUB` (carrying explicit `StepRelLM3_1` over arbitrary `allocMap`) and read-backs
  `MiriHoldsScalar` / `MiriHoldsUninit` / `MiriHoldsIndirectScalar` / `MiriHoldsIndirectUninit`
  (`wfc_miri_scalar_at`, `wfc_miri_uninit_at`, `wfc_miri_indirect_scalar`,
  `wfc_miri_promoted_scalar`, `wfc_miri_promoted_uninit`), and the packaged step lemmas
  `wfc_step_{constant,copy,move}`, `wfc_ub_{copy,move}`, `wfc_step_return_any` / `wfc_step_return`,
  `wfc_step_storage{Live,Dead}`.
* **(W1)** `wfcW1_end_to_end`: 9 `f32 ↔ f64` casts + `return`: subnormal halfway ties
  `1.5·2⁻¹⁴⁹` / `2.5·2⁻¹⁴⁹ ↦ 0x2`, `f32::MAX + ½ulp ↦ +∞`, `-0.0` sign preservation, and exact
  `f32 → f64 → f32` round trips (subnormal and normal).
* **(W2)** `wfcW2_end_to_end` (6 NaN casts + `return`: `0x7F80_0001_f32 ↦ 0x7FF8_0000_2000_0000`,
  `0x7FF0_0000_0000_0001 ↦ 0x7FC0_0000`, `0x7FF0_0000_2000_0001 ↦ 0x7FC0_0001`, negative and
  round-trip payload NaNs), `wfcW2_deterministic_canonicalization` (`floatNondeterministic :=
  false` stores `preferredNaN`, simulation modulo canonicalization, provably no lockstep),
  `wfcW2_selectors_exact` (`pure 0 .. pure 3`), `wfcW2_selectors_snan_4_5_and_out_of_range`
  (`pure 4` / `pure 5` signaling-NaN step outputs + `pure 6` / `pure 4` out-of-range
  `.invalidProgram` tightness), `wfcW2_selectors_copy_and_move` (`copy` & `move` NaN-selector
  simulations), and `wfcW2_nanChoices_exact` (exact 6-, 4-, and 6-element candidate lists and
  deterministic singleton).
* **(W3)** `wfcW3_end_to_end` (14 casts + `return` hitting all 12 integer targets: `NaN ↦ 0`,
  `±∞ ↦ MAX/MIN`, `-0.0 ↦ 0`, finite saturation, truncation toward zero) and
  `wfcW3_toInteger_all_targets` (the full class table for every target and both formats at
  `FloatBits.toInteger`).
* **(W4)** `wfcW4_end_to_end` (9 casts + `return`: `u128::MAX as f32 = +∞`,
  `u128::MAX as f64 = 2¹²⁸`, `i128::MIN as f32 = -2¹²⁷`, `2²⁴ + 1 / 2²⁴ + 3` and
  `2⁵³ + 1 / 2⁵³ + 3` ties to even).
* **(W5)** `wfcW5_uninit_source_ub`, `wfcW5_moved_from_ub`, `wfcW5_dead_source_ub` (from program
  entry, through `StorageLive` / `StorageDead`) fault with `.ub` in both machines
  (`StepRelLM3_1.ub`); `wfcW5_f16_f128_fail_closed` + `wfcW5_f16_f128_uninit_source_vs_target`
  (`.unsupported` fail-closed and uninit source-vs-target evaluation-order contrast);
  `wfcW5_bool_char_boundary` (`bool` and `char` Anneal fail-closed vs `lean-miri` `Cast.cast`);
  `wfcW5_promoted_raw_pipeline_end_to_end` + `wfcW5_promoted_uninit_ub` (multi-step `&raw mut`
  promoted local + float-cast memory reads/writes + Tree Borrows invalidation + `return`); and
  `wfcW5_indirect_float_pipeline_end_to_end` (multi-step unpromoted stack-allocated
  `LocalRel.indirect` `f64` destination write + indirect `copy` + indirect `move` + `return`).

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

/-- **Post-prologue entry relation for any body**: an Anneal state at `bb0[0]` whose locals
are all `.uninit` (the state reached from `initMachineState` once the `StorageLive` prologue
has run) and `wfcMiriInit body retTy` are `StateRelLM3_1`-related with an empty
`allocMap`. -/
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

/-- `ValidScalarBytes` witnesses. -/
theorem wfcVSB1 : ValidScalarBytes 1 := Or.inl rfl
theorem wfcVSB2 : ValidScalarBytes 2 := Or.inr (Or.inl rfl)
theorem wfcVSB4 : ValidScalarBytes 4 := Or.inr (Or.inr (Or.inl rfl))
theorem wfcVSB8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem wfcVSB16 : ValidScalarBytes 16 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ### Shared types, constants, and body builder -/

/-- `f32`. -/
def wfcF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
/-- `f64`. -/
def wfcF64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
/-- Signed integer type. -/
def wfcIntTy (it : IntTy) : Ty := { kind := .int it, layoutIdx := 0 }
/-- Unsigned integer type. -/
def wfcUintTy (ut : UintTy) : Ty := { kind := .uint ut, layoutIdx := 0 }
/-- Mutable local of type `ty`. -/
def wfcDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
/-- Scalar constant `⟨bits, sz⟩ : ty`. -/
def wfcConst (ty : Ty) (bits sz : Nat) : ConstOperand :=
  { ty := ty, val := .scalar (.int ⟨bits, sz⟩) }
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
bb0: _1 = const 0x36A8_0000_0000_0000_f64 as f32  // 1.5·2⁻¹⁴⁹ tie (odd 1) ↦ even 2·2⁻¹⁴⁹
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
     .assign (local_ 0) (.cast .floatToFloat (.move (local_ 5)) wfcF32Ty)]

def wfcW1S0 : MachineState := wfcAt wfcW1Body 0 [.uninit, .uninit, .uninit, .uninit, .uninit,
  .uninit, .uninit, .uninit, .uninit]
def wfcW1S1 : MachineState := wfcAt wfcW1Body 1 [.uninit, .init (.scalar ⟨0x2, 4⟩), .uninit,
  .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW1S2 : MachineState := wfcAt wfcW1Body 2 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW1S3 : MachineState := wfcAt wfcW1Body 3 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .uninit, .uninit, .uninit, .uninit,
  .uninit]
def wfcW1S4 : MachineState := wfcAt wfcW1Body 4 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x80000000, 4⟩),
  .uninit, .uninit, .uninit, .uninit]
def wfcW1S5 : MachineState := wfcAt wfcW1Body 5 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x80000000, 4⟩),
  .init (.scalar ⟨0x36B0000000000000, 8⟩), .uninit, .uninit, .uninit]
def wfcW1S6 : MachineState := wfcAt wfcW1Body 6 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .uninit,
  .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩), .uninit,
  .uninit]
def wfcW1S7 : MachineState := wfcAt wfcW1Body 7 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .uninit,
  .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩),
  .init (.scalar ⟨0x3FB99999A0000000, 8⟩), .uninit]
def wfcW1S8 : MachineState := wfcAt wfcW1Body 8 [.uninit, .init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .uninit,
  .init (.scalar ⟨0x36B0000000000000, 8⟩), .init (.scalar ⟨0x8000000000000000, 8⟩), .uninit,
  .init (.scalar ⟨0x3DCCCCCD, 4⟩)]
def wfcW1S9 : MachineState := wfcAt wfcW1Body 9 [.init (.scalar ⟨0x2, 4⟩),
  .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩), .uninit,
  .uninit, .init (.scalar ⟨0x8000000000000000, 8⟩), .uninit, .init (.scalar ⟨0x3DCCCCCD, 4⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW1Body` (kernel evaluation of `stepMirFn`). -/
theorem wfcW1_anneal_run :
    stepMirFn wfcW1Body wfcW1S0 = .step wfcW1S1 ∧
    stepMirFn wfcW1Body wfcW1S1 = .step wfcW1S2 ∧
    stepMirFn wfcW1Body wfcW1S2 = .step wfcW1S3 ∧
    stepMirFn wfcW1Body wfcW1S3 = .step wfcW1S4 ∧
    stepMirFn wfcW1Body wfcW1S4 = .step wfcW1S5 ∧
    stepMirFn wfcW1Body wfcW1S5 = .step wfcW1S6 ∧
    stepMirFn wfcW1Body wfcW1S6 = .step wfcW1S7 ∧
    stepMirFn wfcW1Body wfcW1S7 = .step wfcW1S8 ∧
    stepMirFn wfcW1Body wfcW1S8 = .step wfcW1S9 ∧
    stepMirFn wfcW1Body wfcW1S9 = .retNormal (.scalar ⟨0x2, 4⟩) wfcW1S9.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW1_stateRel_init :
    StateRelLM3_1 wfcW1Body wfcW1S0 (wfcMiriInit wfcW1Body wfcF32Ty) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W1) end-to-end two-sided witness**: from program entry, Anneal's `stepMirFn` and
`lean-miri`'s `Step.step` (`annealStepHooksFloat`) run `wfcW1Body` in `StateRelLM3_1`
lockstep through all nine `floatToFloat` casts (`.constant` / `.copy` / `.move`) and the
root `return`, with both machines holding the IEEE-754 `roundTiesToEven` results
bit-for-bit after every step: both subnormal halfway ties round to the even `0x0000_0002`,
`f32::MAX + ½ulp` overflows to `+∞`, `-0.0` keeps its sign through `f64 → f32 → f64`, and
the subnormal `2⁻¹⁴⁸` and `0.1_f32` survive `f32 → f64 → f32` round trips exactly; the
function returns `0x0000_0002_f32` in both machines. -/
theorem wfcW1_end_to_end :
    ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcLockstep wfcW1Body wfcW1S0 wfcW1S1 (wfcMiriInit wfcW1Body wfcF32Ty) m₁ 1 0x2 4 ∧
      WfcLockstep wfcW1Body wfcW1S1 wfcW1S2 m₁ m₂ 2 0x2 4 ∧
      WfcLockstep wfcW1Body wfcW1S2 wfcW1S3 m₂ m₃ 3 0x7F800000 4 ∧
      WfcLockstep wfcW1Body wfcW1S3 wfcW1S4 m₃ m₄ 4 0x80000000 4 ∧
      WfcLockstep wfcW1Body wfcW1S4 wfcW1S5 m₄ m₅ 5 0x36B0000000000000 8 ∧
      WfcLockstep wfcW1Body wfcW1S5 wfcW1S6 m₅ m₆ 6 0x8000000000000000 8 ∧
      MiriHoldsUninit m₆ 4 ∧
      WfcLockstep wfcW1Body wfcW1S6 wfcW1S7 m₆ m₇ 7 0x3FB99999A0000000 8 ∧
      WfcLockstep wfcW1Body wfcW1S7 wfcW1S8 m₇ m₈ 8 0x3DCCCCCD 4 ∧
      WfcLockstep wfcW1Body wfcW1S8 wfcW1S9 m₈ m₉ 0 0x2 4 ∧
      MiriHoldsUninit m₉ 5 ∧
      WfcReturns wfcW1Body wfcW1S9 m₉ (.scalar ⟨0x2, 4⟩) := by
  have hph : ∀ p, wfcW1Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hret⟩ := wfcW1_anneal_run
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant wfcW1_stateRel_init (wfc_allImm_init _ _) hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h1 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h2 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h3 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h4 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_copy l₄.2.2.1 i₄ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h5 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_move l₅.2.2.1 i₅ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h6 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h7 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_move l₇.2.2.1 i₇ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h8 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_move l₈.2.2.1 i₈ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h9 rfl
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, l₁, l₂, l₃, l₄, l₅, l₆,
    wfc_miri_uninit l₆.2.2.1 i₆ rfl (Or.inl ⟨_, rfl⟩) rfl, l₇, l₈, l₉,
    wfc_miri_uninit l₉.2.2.1 i₉ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₉.2.2.1 i₉ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

/-! ## (W2) Signaling-NaN quietization, `nanChoices` membership, and NaN-choice refinement -/

/-- **(W2) body** (`_0, _1 : f64`; `_2.._5 : f32`):
```text
bb0: _1 = const 0x7F80_0001_f32 as f64             // sNaN ↦ quiet 0x7FF8_0000_2000_0000
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
    [.assign (local_ 1) (.cast .floatToFloat (.constant (wfcConst wfcF32Ty 0x7F800001 4)) wfcF64Ty),
     .assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000000000001 8))
      wfcF32Ty),
     .assign (local_ 3) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF0000020000001 8))
      wfcF32Ty),
     .assign (local_ 5) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0xFFF0000020000001 8))
      wfcF32Ty),
     .assign (local_ 4) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty),
     .assign (local_ 0) (.cast .floatToFloat (.move (local_ 4)) wfcF64Ty)]

def wfcW2S0 : MachineState := wfcAt wfcW2Body 0
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW2S1 : MachineState := wfcAt wfcW2Body 1
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .uninit, .uninit, .uninit, .uninit]
def wfcW2S2 : MachineState := wfcAt wfcW2Body 2
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩), .uninit,
   .uninit, .uninit]
def wfcW2S3 : MachineState := wfcAt wfcW2Body 3
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .uninit, .uninit]
def wfcW2S4 : MachineState := wfcAt wfcW2Body 4
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .uninit, .init (.scalar ⟨0xFFC00001, 4⟩)]
def wfcW2S5 : MachineState := wfcAt wfcW2Body 5
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00000, 4⟩),
   .init (.scalar ⟨0x7FC00001, 4⟩), .init (.scalar ⟨0x7FC00001, 4⟩),
   .init (.scalar ⟨0xFFC00001, 4⟩)]
def wfcW2S6 : MachineState := wfcAt wfcW2Body 6
  [.init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FF8000020000000, 8⟩),
   .init (.scalar ⟨0x7FC00000, 4⟩), .init (.scalar ⟨0x7FC00001, 4⟩), .uninit,
   .init (.scalar ⟨0xFFC00001, 4⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW2Body` (kernel evaluation of `stepMirFn`). -/
theorem wfcW2_anneal_run :
    stepMirFn wfcW2Body wfcW2S0 = .step wfcW2S1 ∧
    stepMirFn wfcW2Body wfcW2S1 = .step wfcW2S2 ∧
    stepMirFn wfcW2Body wfcW2S2 = .step wfcW2S3 ∧
    stepMirFn wfcW2Body wfcW2S3 = .step wfcW2S4 ∧
    stepMirFn wfcW2Body wfcW2S4 = .step wfcW2S5 ∧
    stepMirFn wfcW2Body wfcW2S5 = .step wfcW2S6 ∧
    stepMirFn wfcW2Body wfcW2S6 = .retNormal (.scalar ⟨0x7FF8000020000000, 8⟩) wfcW2S6.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW2_stateRel_init :
    StateRelLM3_1 wfcW2Body wfcW2S0 (wfcMiriInit wfcW2Body wfcF64Ty) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W2) end-to-end two-sided NaN witness**: from the post-prologue entry state, Anneal's
`stepMirFn` and `lean-miri`'s `Step.step` (`annealStepHooksFloat`, nondeterministic NaN mode with
the refinement selector `annealChooseQuietedNaN`) run `wfcW2Body` in `StateRelLM3_1` lockstep:
the signaling `0x7F80_0001_f32` is quieted to `0x7FF8_0000_2000_0000_f64` (payload kept), the
signaling `0x7FF0_0000_0000_0001_f64` narrows to the canonical quiet `0x7FC0_0000_f32` (payload
below bit 29 dropped), the payload-preserving `0x7FF0_0000_2000_0001_f64` narrows to
`0x7FC0_0001_f32`, the negative `0xFFF0_0000_2000_0001_f64` keeps its sign (`0xFFC0_0001_f32`),
and the quiet payload NaN round-trips `f64 → f32 → f64`; the function returns
`0x7FF8_0000_2000_0000_f64` in both machines. -/
theorem wfcW2_end_to_end :
    ∃ m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState,
      WfcLockstep wfcW2Body wfcW2S0 wfcW2S1 (wfcMiriInit wfcW2Body wfcF64Ty) m₁ 1
        0x7FF8000020000000 8 ∧
      WfcLockstep wfcW2Body wfcW2S1 wfcW2S2 m₁ m₂ 2 0x7FC00000 4 ∧
      WfcLockstep wfcW2Body wfcW2S2 wfcW2S3 m₂ m₃ 3 0x7FC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S3 wfcW2S4 m₃ m₄ 5 0xFFC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S4 wfcW2S5 m₄ m₅ 4 0x7FC00001 4 ∧
      WfcLockstep wfcW2Body wfcW2S5 wfcW2S6 m₅ m₆ 0 0x7FF8000020000000 8 ∧
      MiriHoldsUninit m₆ 4 ∧
      WfcReturns wfcW2Body wfcW2S6 m₆ (.scalar ⟨0x7FF8000020000000, 8⟩) := by
  have hph : ∀ p, wfcW2Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h1, h2, h3, h4, h5, h6, hret⟩ := wfcW2_anneal_run
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant wfcW2_stateRel_init (wfc_allImm_init _ _) hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h1 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h2 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h3 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h4 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_copy l₄.2.2.1 i₄ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h5 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_move l₅.2.2.1 i₅ hph rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl rfl h6 rfl
  exact ⟨m₁,
    m₂,
    m₃,
    m₄,
    m₅,
    m₆,
    l₁,
    l₂,
    l₃,
    l₄,
    l₅,
    l₆,
    wfc_miri_uninit l₆.2.2.1 i₆ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₆.2.2.1 i₆ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩



/-! ### (W2) Deterministic NaN mode, explicit NaN-choice selectors, and exact candidate lists -/

/-- **(W2) deterministic-mode (`floatNondeterministic := false`) canonicalization on the first
step of `wfcW2Body`** (`_1 = const 0x7F80_0001_f32 as f64`), for **every** `chooseNaN`: Anneal
steps to `wfcW2S1` (storing the quieted `0x7FF8_0000_2000_0000`), while `lean-miri` steps and
stores the canonical `preferredNaNBits .binary64 = 0x7FF8_0000_0000_0000` in `_1`; the Anneal
successor storing that canonical NaN is `StepRelLM3_1`-related to `lean-miri`'s step (simulation
modulo NaN canonicalization), and **no** `StepRelLM3_1` relates the real Anneal step to it. In
contrast, `wfcW2_end_to_end` keeps both machines in lockstep under the refinement selector
`annealChooseQuietedNaN`. -/
theorem wfcW2_deterministic_canonicalization
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    let hooksDet := annealStepHooksFloat wfcW2Body.localDecls wfcW2Body.layouts false chooseNaN
    let m₀ := wfcMiriInit wfcW2Body wfcF64Ty
    stepMirFn wfcW2Body wfcW2S0 = .step wfcW2S1 ∧
    (∃ m', Miri.Interpreter.Step.step hooksDet () m₀ = (m', .ok true) ∧
      MiriHoldsScalar m' 1 ⟨0x7FF8000000000000, 8⟩) ∧
    StepRelLM3_1 wfcW2Body m₀ []
      (.step (wfcAt wfcW2Body 1
        [.uninit, .init (.scalar ⟨0x7FF8000000000000, 8⟩), .uninit, .uninit, .uninit, .uninit]))
      (Miri.Interpreter.Step.step hooksDet () m₀) ∧
    ¬ StepRelLM3_1 wfcW2Body m₀ [] (stepMirFn wfcW2Body wfcW2S0)
      (Miri.Interpreter.Step.step hooksDet () m₀) := by
  intro hooksDet m₀
  have himm₀ : ∀ tf, m₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 1 :=
    fun tf htf => wfc_allImm_init _ _ tf htf 1
  have hnan : Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7F800001 = true := rfl
  have hev : evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7F800001 =
      0x7FF8000020000000 := rfl
  have hpref : preferredNaNBits .binary64 = 0x7FF8000000000000 := rfl
  have hspec := step_cast_floatToFloat_constant_deterministic_spec wfcW2_stateRel_init
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀
  dsimp only at hspec
  simp only [hev, hnan, ↓reduceIte, hpref] at hspec
  obtain ⟨m', tf', msc', hrel', _, hm', htf', hval'⟩ := hspec
  have hsim := (step_cast_floatToFloat_constant_deterministic_simulation wfcW2_stateRel_init
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀).2
  simp only [hnan, ↓reduceIte, hpref] at hsim
  refine ⟨wfcW2_anneal_run.1, ⟨m', hm', tf', msc', htf', hval', hrel'⟩, hsim, fun hstep => ?_⟩
  have hag := (step_cast_floatToFloat_constant_deterministic_lockstep_iff wfcW2_stateRel_init
    (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀).mp hstep
  rw [hnan, hev, hpref] at hag
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

theorem wfcW2Sel_stateRel_init :
    StateRelLM3_1 wfcW2SelBody wfcW2SelS0 (wfcMiriInit wfcW2SelBody wfcF32Ty) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W2) universal 4-candidate NaN-choice selectors (`pure 0 .. pure 3`) at the step level** on
`wfcW2SelBody`: Anneal always stores the quieted conversion `0x7FC0_0001`, and for the four quiet
selectors `pure 0 .. pure 3` (`floatNondeterministic := true`) `lean-miri`'s step is
`StepRelLM3_1`-simulated by the Anneal successor storing `0x7FC0_0000` (`preferredNaN`),
`0xFFC0_0000` (its negation), `0x7FC0_0001` (the quieted conversion, i.e. Anneal's own result),
and `0xFFC0_0001` (its negation), instantiating `step_cast_floatToFloat_constant_pure_index_simulation`.
See `wfcW2_selectors_snan_4_5_and_out_of_range` below for the remaining signaling-NaN selectors
`pure 4` and `pure 5` and out-of-range selector failure! -/
theorem wfcW2_selectors_exact :
    let m₀ := wfcMiriInit wfcW2SelBody wfcF32Ty
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
    fun tf htf => wfc_allImm_init _ _ tf htf 0
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
    (_hphase : ∀ p, body.phase ≠ .other p)
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

theorem wfcW2Sel4_stateRel_init :
    StateRelLM3_1 wfcW2Sel4Body wfcW2Sel4S0 (wfcMiriInit wfcW2Sel4Body wfcF32Ty) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W2) signaling-NaN selectors `pure 4` & `pure 5` and out-of-range selector tightness**:
* on `wfcW2SelBody` (`0x7FF0_0000_2000_0001_f64 as f32`, 6 candidates), selectors `pure 4` and
  `pure 5` succeed and store the **signaling** `f32` NaNs `0x7F80_0001` and `0xFF80_0001`
  (`FloatBits.isSignaling = .ok true`), while `pure 6` fails with
  `.invalidProgram "invalid floating NaN choice index"` (`¬ StepRelLM3_1`);
* on `wfcW2Sel4Body` (`0x7FF0_0000_0000_0001_f64 as f32`, 4 candidates because the scaled payload
  vanishes), already `pure 4` fails with `.invalidProgram "invalid floating NaN choice index"`
  (`¬ StepRelLM3_1`). -/
theorem wfcW2_selectors_snan_4_5_and_out_of_range :
    let m₀ := wfcMiriInit wfcW2SelBody wfcF32Ty
    let sel (i : Nat) :=
      annealStepHooksFloat wfcW2SelBody.localDecls wfcW2SelBody.layouts true (fun _ _ => pure i)
    let m₄₀ := wfcMiriInit wfcW2Sel4Body wfcF32Ty
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
    fun tf htf => wfc_allImm_init _ _ tf htf 0
  have himm₄₀ : ∀ tf, m₄₀.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => wfc_allImm_init _ _ tf htf 0
  have hph : ∀ p, wfcW2SelBody.phase ≠ .other p := fun _ h => nomatch h
  have hph4 : ∀ p, wfcW2Sel4Body.phase ≠ .other p := fun _ h => nomatch h
  have hnan6 : decodeBits .binary64 0x7FF0000020000001 = .nan false false 0x20000001 := rfl
  have hnan4 : decodeBits .binary64 0x7FF0000000000001 = .nan false false 1 := rfl
  have h4 := wfc_step_constant_snan_index wfcW2Sel_stateRel_init hph 4 (by decide) rfl rfl rfl
    rfl rfl rfl rfl rfl (by decide) hnan6 (by decide) (fun h => nomatch h) himm₀ (by decide)
  have h5 := wfc_step_constant_snan_index wfcW2Sel_stateRel_init hph 5 (by decide) rfl rfl rfl
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
`bb0: _2 = const 0x7FF8_0000_2000_0000_f64 as f32; _1 = copy _2 as f64; _0 = move _2 as f64; return`. -/
def wfcW2CopyMoveSelBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w2_copy_move_selector"
    [wfcDecl wfcF64Ty, wfcDecl wfcF64Ty, wfcDecl wfcF32Ty] 8
    [.assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x7FF8000020000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.copy (local_ 2)) wfcF64Ty),
     .assign (local_ 0) (.cast .floatToFloat (.move (local_ 2)) wfcF64Ty)]

def wfcW2CMS0 : MachineState := wfcAt wfcW2CopyMoveSelBody 0 [.uninit, .uninit, .uninit]
def wfcW2CMS1 : MachineState := wfcAt wfcW2CopyMoveSelBody 1
  [.uninit, .uninit, .init (.scalar ⟨0x7FC00001, 4⟩)]
def wfcW2CMS2 : MachineState := wfcAt wfcW2CopyMoveSelBody 2
  [.uninit, .init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FC00001, 4⟩)]

/-- **(W2) concrete `copy` and `move` NaN-choice selector simulations**
(`step_cast_floatToFloat_copy_pure_index_simulation` and
`step_cast_floatToFloat_move_pure_index_simulation`): along the lockstep run `m₀ ↦ m₁ ↦ m₂` of
`wfcW2CopyMoveSelBody`, at `m₁` `_1 = copy _2 as f64` under selector `pure 1` stores the negative
canonical `f64` NaN `0xFFF8_0000_0000_0000` (while Anneal stores `0x7FF8_0000_2000_0000`), and at
`m₂` `_0 = move _2 as f64` under selector `pure 3` deinitializes `_2` and stores the negative
payload NaN `0xFFF8_0000_2000_0000`. -/
theorem wfcW2_selectors_copy_and_move :
    ∃ m₁ m₂ : AnnealStepState,
      let b := wfcW2CopyMoveSelBody
      let sel (i : Nat) := annealStepHooksFloat b.localDecls b.layouts true (fun _ _ => pure i)
      WfcLockstep b wfcW2CMS0 wfcW2CMS1 (wfcMiriInit b wfcF64Ty) m₁ 2 0x7FC00001 4 ∧
      StepRelLM3_1 b m₁ []
        (.step (wfcAt b 2
          [.uninit, .init (.scalar ⟨0xFFF8000000000000, 8⟩), .init (.scalar ⟨0x7FC00001, 4⟩)]))
        (Miri.Interpreter.Step.step (sel 1) () m₁) ∧
      WfcLockstep b wfcW2CMS1 wfcW2CMS2 m₁ m₂ 1 0x7FF8000020000000 8 ∧
      StepRelLM3_1 b m₂ []
        (.step (wfcAt b 3
          [.init (.scalar ⟨0xFFF8000020000000, 8⟩),
           .init (.scalar ⟨0x7FF8000020000000, 8⟩), .uninit]))
        (Miri.Interpreter.Step.step (sel 3) () m₂) := by
  have hph : ∀ p, wfcW2CopyMoveSelBody.phase ≠ .other p := fun _ h => nomatch h
  have hs1 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMS0 = .step wfcW2CMS1 := rfl
  have hs2 : stepMirFn wfcW2CopyMoveSelBody wfcW2CMS1 = .step wfcW2CMS2 := rfl
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant
    (wfc_stateRel_init wfcW2CopyMoveSelBody wfcF64Ty wfcW2CMS0 rfl rfl rfl rfl rfl rfl)
    (wfc_allImm_init _ _) hph rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide)
    rfl rfl hs1 rfl
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
  exact ⟨m₁, m₂, l₁, hcopy.2, l₂, hmove.2⟩

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
bb0: _13 = const -1.5_f32 as f64          _12 = const 1e23_f64 as f32
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
     .assign (local_ 11) (.cast .floatToInt (.move (local_ 12)) (wfcUintTy .usize))]

def wfcW3S0 : MachineState := wfcAt wfcW3Body 0
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit]
def wfcW3S1 : MachineState := wfcAt wfcW3Body 1
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S2 : MachineState := wfcAt wfcW3Body 2
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S3 : MachineState := wfcAt wfcW3Body 3
  [.init (.scalar ⟨0x7F, 1⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S4 : MachineState := wfcAt wfcW3Body 4
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S5 : MachineState := wfcAt wfcW3Body 5
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩), .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S6 : MachineState := wfcAt wfcW3Body 6
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S7 : MachineState := wfcAt wfcW3Body 7
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S8 : MachineState := wfcAt wfcW3Body 8
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S9 : MachineState := wfcAt wfcW3Body 9
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S10 : MachineState := wfcAt wfcW3Body 10
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S11 : MachineState := wfcAt wfcW3Body 11
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩), .uninit,
   .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S12 : MachineState := wfcAt wfcW3Body 12
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩), .uninit, .uninit, .init (.scalar ⟨0x65A96816, 4⟩),
   .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S13 : MachineState := wfcAt wfcW3Body 13
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩),
   .init (.scalar ⟨0xFFFFFF00000000000000000000000000, 16⟩), .uninit,
   .init (.scalar ⟨0x65A96816, 4⟩), .init (.scalar ⟨0xBFF8000000000000, 8⟩)]
def wfcW3S14 : MachineState := wfcAt wfcW3Body 14
  [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩), .init (.scalar ⟨0x7FFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩), .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩),
   .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩),
   .init (.scalar ⟨0xFFFFFF00000000000000000000000000, 16⟩),
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩), .uninit, .init (.scalar ⟨0xBFF8000000000000, 8⟩)]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW3Body` (kernel evaluation of `stepMirFn`). -/
theorem wfcW3_anneal_run :
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
    stepMirFn wfcW3Body wfcW3S14 = .retNormal (.scalar ⟨0x7F, 1⟩) wfcW3S14.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW3_stateRel_init :
    StateRelLM3_1 wfcW3Body wfcW3S0 (wfcMiriInit wfcW3Body (wfcIntTy .i8)) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W3) end-to-end two-sided saturating float-to-int witness** over all twelve integer
targets: from the post-prologue entry state, both machines run `wfcW3Body` in `StateRelLM3_1`
lockstep (`.constant` / `.copy` / `.move` operands, `f32` and `f64` sources) with bit-identical
results after every step: `+∞ as i8 = i8::MAX`, `-∞ as i16 = i16::MIN`, `3e9 as i32 = i32::MAX`,
`-2.9 as i64 = -2` (truncation toward zero), `NaN as i128 = 0`, `-0.0_f32 as isize = 0`,
`-1.5 as u8 = 0` (negative saturates to `u8::MIN`), `65535.5_f32 as u16 = u16::MAX`,
`2³² as u32 = u32::MAX`, `2⁶⁴_f32 as u64 = u64::MAX`, `f32::MAX as u128` exact (it is below
`u128::MAX`), and `1e23_f32 as usize = usize::MAX`; the function returns `127_i8`. -/
theorem wfcW3_end_to_end :
    ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ : AnnealStepState,
      WfcLockstep wfcW3Body wfcW3S0 wfcW3S1 (wfcMiriInit wfcW3Body (wfcIntTy .i8)) m₁ 13
        0xBFF8000000000000 8 ∧
      WfcLockstep wfcW3Body wfcW3S1 wfcW3S2 m₁ m₂ 12 0x65A96816 4 ∧
      WfcLockstep wfcW3Body wfcW3S2 wfcW3S3 m₂ m₃ 0 0x7F 1 ∧
      WfcLockstep wfcW3Body wfcW3S3 wfcW3S4 m₃ m₄ 1 0x8000 2 ∧
      WfcLockstep wfcW3Body wfcW3S4 wfcW3S5 m₄ m₅ 2 0x7FFFFFFF 4 ∧
      WfcLockstep wfcW3Body wfcW3S5 wfcW3S6 m₅ m₆ 3 0xFFFFFFFFFFFFFFFE 8 ∧
      WfcLockstep wfcW3Body wfcW3S6 wfcW3S7 m₆ m₇ 4 0 16 ∧
      WfcLockstep wfcW3Body wfcW3S7 wfcW3S8 m₇ m₈ 5 0 8 ∧
      WfcLockstep wfcW3Body wfcW3S8 wfcW3S9 m₈ m₉ 6 0 1 ∧
      WfcLockstep wfcW3Body wfcW3S9 wfcW3S10 m₉ m₁₀ 7 0xFFFF 2 ∧
      WfcLockstep wfcW3Body wfcW3S10 wfcW3S11 m₁₀ m₁₁ 8 0xFFFFFFFF 4 ∧
      WfcLockstep wfcW3Body wfcW3S11 wfcW3S12 m₁₁ m₁₂ 9 0xFFFFFFFFFFFFFFFF 8 ∧
      WfcLockstep wfcW3Body wfcW3S12 wfcW3S13 m₁₂ m₁₃ 10 0xFFFFFF00000000000000000000000000 16 ∧
      WfcLockstep wfcW3Body wfcW3S13 wfcW3S14 m₁₃ m₁₄ 11 0xFFFFFFFFFFFFFFFF 8 ∧
      MiriHoldsUninit m₁₄ 12 ∧
      WfcReturns wfcW3Body wfcW3S14 m₁₄ (.scalar ⟨0x7F, 1⟩) := by
  have hph : ∀ p, wfcW3Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hret⟩ := wfcW3_anneal_run
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant wfcW3_stateRel_init (wfc_allImm_init _ _) hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h1 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_constant l₁.2.2.1 i₁ hph rfl rfl
    rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h2 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_constant l₂.2.2.1 i₂ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h3 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h4 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_constant l₄.2.2.1 i₄ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h5 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_constant l₅.2.2.1 i₅ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h6 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h7 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_constant l₇.2.2.1 i₇ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h8 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_copy l₈.2.2.1 i₈ hph rfl rfl rfl rfl
    (.floatToInt rfl rfl) rfl rfl h9 rfl
  obtain ⟨m₁₀, l₁₀, i₁₀⟩ := wfc_step_constant l₉.2.2.1 i₉ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h10 rfl
  obtain ⟨m₁₁, l₁₁, i₁₁⟩ := wfc_step_constant l₁₀.2.2.1 i₁₀ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h11 rfl
  obtain ⟨m₁₂, l₁₂, i₁₂⟩ := wfc_step_constant l₁₁.2.2.1 i₁₁ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h12 rfl
  obtain ⟨m₁₃, l₁₃, i₁₃⟩ := wfc_step_constant l₁₂.2.2.1 i₁₂ hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h13 rfl
  obtain ⟨m₁₄, l₁₄, i₁₄⟩ := wfc_step_move l₁₃.2.2.1 i₁₃ hph rfl rfl rfl rfl
    (.floatToInt rfl rfl) rfl rfl h14 rfl
  exact ⟨m₁,
    m₂,
    m₃,
    m₄,
    m₅,
    m₆,
    m₇,
    m₈,
    m₉,
    m₁₀,
    m₁₁,
    m₁₂,
    m₁₃,
    m₁₄,
    l₁,
    l₂,
    l₃,
    l₄,
    l₅,
    l₆,
    l₇,
    l₈,
    l₉,
    l₁₀,
    l₁₁,
    l₁₂,
    l₁₃,
    l₁₄,
    wfc_miri_uninit l₁₄.2.2.1 i₁₄ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_step_return l₁₄.2.2.1 i₁₄ hph rfl rfl rfl rfl rfl rfl (Or.inr ⟨_, rfl⟩) hret⟩



/-! ### (W3) All twelve integer targets × both source formats at the `lean-miri` primitive -/

/-- `FloatBits.toInteger` on an in-width bit pattern returns any closed form `V` of
`floatToIntValue` (`floatBits_toInteger_eq` with the trusted side evaluated). -/
theorem wfc_toInteger (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) (t : FloatIntTarget)
    (V : Int)
    (hv : floatToIntValue (decodeBits f bits) (t.minValue .bits64) (t.maxValue .bits64) = V) :
    Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
        (t.bitWidth .bits64) t.isSigned = .ok V := by
  rw [floatBits_toInteger_eq f bits h t .bits64, hv]

/-- **(W3) saturating float-to-int for every one of the twelve integer targets** (64-bit
`isize` / `usize`) and both source formats, at `lean-miri`'s `FloatBits.toInteger` (the
primitive behind `Cast.cast .FloatToInt`): `NaN ↦ 0`, `+∞ ↦ MAX`, `-∞ ↦ MIN`, `-0.0 ↦ 0`,
out-of-range finite values saturate (`1e300_f64 ↦ MAX`, `-f32::MAX ↦ MIN`), and in-range values
truncate toward zero (`1.75 ↦ 1`; `-1.75 ↦ -1` on signed targets, saturating to `0 = MIN` on
unsigned ones). -/
theorem wfcW3_toInteger_all_targets (t : FloatIntTarget) :
    let toI (f : IeeeFormat) (bits : Nat) :=
      Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
        (t.bitWidth .bits64) t.isSigned
    toI .binary32 0x7FC00000 = .ok 0 ∧ toI .binary64 0x7FF8000000000000 = .ok 0 ∧
    toI .binary32 0x7F800000 = .ok (t.maxValue .bits64) ∧
    toI .binary64 0x7FF0000000000000 = .ok (t.maxValue .bits64) ∧
    toI .binary32 0xFF800000 = .ok (t.minValue .bits64) ∧
    toI .binary64 0xFFF0000000000000 = .ok (t.minValue .bits64) ∧
    toI .binary32 0x80000000 = .ok 0 ∧ toI .binary64 0x8000000000000000 = .ok 0 ∧
    toI .binary64 0x7E37E43C8800759C = .ok (t.maxValue .bits64) ∧
    toI .binary32 0xFF7FFFFF = .ok (t.minValue .bits64) ∧
    toI .binary32 0x3FE00000 = .ok 1 ∧ toI .binary64 0x3FFC000000000000 = .ok 1 ∧
    toI .binary32 0xBFE00000 = .ok (if t.isSigned then -1 else 0) ∧
    toI .binary64 0xBFFC000000000000 = .ok (if t.isSigned then -1 else 0) := by
  intro toI
  refine ⟨wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ rfl, wfc_toInteger _ _ (by decide) t _ rfl,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_,
    wfc_toInteger _ _ (by decide) t _ ?_, wfc_toInteger _ _ (by decide) t _ ?_⟩ <;>
    (cases t <;> rename_i w <;> cases w <;> decide +kernel)


/-! ## (W4) Integer-to-float ties-to-even and overflow -/

/-- **(W4) body** (`_0, _1, _3, _4, _5 : f32` with `_0` returned; `_2, _6, _7 : f64`;
`_8 : u128`):
```text
bb0: _8 = const +∞_f32 as u128            // u128::MAX (saturation)
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
     .assign (local_ 0) (.cast .intToFloat (.constant (wfcConst (wfcIntTy .i8) 0x80 1)) wfcF32Ty)]

def wfcW4S0 : MachineState := wfcAt wfcW4Body 0
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S1 : MachineState := wfcAt wfcW4Body 1
  [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 16⟩)]
def wfcW4S2 : MachineState := wfcAt wfcW4Body 2
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
   .init (.scalar ⟨0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 16⟩)]
def wfcW4S3 : MachineState := wfcAt wfcW4Body 3
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩), .uninit,
   .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S4 : MachineState := wfcAt wfcW4Body 4
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .uninit, .uninit, .uninit, .uninit, .uninit]
def wfcW4S5 : MachineState := wfcAt wfcW4Body 5
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩), .uninit, .uninit, .uninit,
   .uninit]
def wfcW4S6 : MachineState := wfcAt wfcW4Body 6
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .uninit, .uninit, .uninit]
def wfcW4S7 : MachineState := wfcAt wfcW4Body 7
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .init (.scalar ⟨0x4340000000000000, 8⟩), .uninit, .uninit]
def wfcW4S8 : MachineState := wfcAt wfcW4Body 8
  [.uninit, .init (.scalar ⟨0x7F800000, 4⟩), .init (.scalar ⟨0x47F0000000000000, 8⟩),
   .init (.scalar ⟨0xFF000000, 4⟩), .init (.scalar ⟨0x4B800000, 4⟩),
   .init (.scalar ⟨0x4B800002, 4⟩), .init (.scalar ⟨0x4340000000000000, 8⟩),
   .init (.scalar ⟨0x4340000000000002, 8⟩), .uninit]
def wfcW4S9 : MachineState := wfcAt wfcW4Body 9
  [.init (.scalar ⟨0xC3000000, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
   .init (.scalar ⟨0x47F0000000000000, 8⟩), .init (.scalar ⟨0xFF000000, 4⟩),
   .init (.scalar ⟨0x4B800000, 4⟩), .init (.scalar ⟨0x4B800002, 4⟩),
   .init (.scalar ⟨0x4340000000000000, 8⟩), .init (.scalar ⟨0x4340000000000002, 8⟩), .uninit]

set_option maxRecDepth 200000 in
/-- Anneal's concrete run of `wfcW4Body` (kernel evaluation of `stepMirFn`). -/
theorem wfcW4_anneal_run :
    stepMirFn wfcW4Body wfcW4S0 = .step wfcW4S1 ∧
    stepMirFn wfcW4Body wfcW4S1 = .step wfcW4S2 ∧
    stepMirFn wfcW4Body wfcW4S2 = .step wfcW4S3 ∧
    stepMirFn wfcW4Body wfcW4S3 = .step wfcW4S4 ∧
    stepMirFn wfcW4Body wfcW4S4 = .step wfcW4S5 ∧
    stepMirFn wfcW4Body wfcW4S5 = .step wfcW4S6 ∧
    stepMirFn wfcW4Body wfcW4S6 = .step wfcW4S7 ∧
    stepMirFn wfcW4Body wfcW4S7 = .step wfcW4S8 ∧
    stepMirFn wfcW4Body wfcW4S8 = .step wfcW4S9 ∧
    stepMirFn wfcW4Body wfcW4S9 = .retNormal (.scalar ⟨0xC3000000, 4⟩) wfcW4S9.memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wfcW4_stateRel_init :
    StateRelLM3_1 wfcW4Body wfcW4S0 (wfcMiriInit wfcW4Body wfcF32Ty) [] :=
  wfc_stateRel_init _ _ _ rfl rfl rfl rfl rfl rfl

/-- **(W4) end-to-end two-sided integer-to-float witness**: from the post-prologue entry state,
both machines run `wfcW4Body` in `StateRelLM3_1` lockstep with bit-identical
`roundTiesToEven` results: `+∞_f32 as u128 = u128::MAX`, then `u128::MAX as f32 = +∞` (it exceeds
`f32::MAX + ½ulp`) and `u128::MAX as f64 = 2¹²⁸`, `i128::MIN as f32 = -2¹²⁷` exactly, the
`2²⁴ + 1` / `2²⁴ + 3` ties round to the even `2²⁴` / `2²⁴ + 4` in `f32`, the `2⁵³ + 1` /
`2⁵³ + 3` ties round to the even `2⁵³` / `2⁵³ + 4` in `f64`, and `i8::MIN as f32 = -128.0`; the
function returns `-128.0_f32`. -/
theorem wfcW4_end_to_end :
    ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState,
      WfcLockstep wfcW4Body wfcW4S0 wfcW4S1 (wfcMiriInit wfcW4Body wfcF32Ty) m₁ 8
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 16 ∧
      WfcLockstep wfcW4Body wfcW4S1 wfcW4S2 m₁ m₂ 1 0x7F800000 4 ∧
      WfcLockstep wfcW4Body wfcW4S2 wfcW4S3 m₂ m₃ 2 0x47F0000000000000 8 ∧
      MiriHoldsUninit m₃ 8 ∧
      WfcLockstep wfcW4Body wfcW4S3 wfcW4S4 m₃ m₄ 3 0xFF000000 4 ∧
      WfcLockstep wfcW4Body wfcW4S4 wfcW4S5 m₄ m₅ 4 0x4B800000 4 ∧
      WfcLockstep wfcW4Body wfcW4S5 wfcW4S6 m₅ m₆ 5 0x4B800002 4 ∧
      WfcLockstep wfcW4Body wfcW4S6 wfcW4S7 m₆ m₇ 6 0x4340000000000000 8 ∧
      WfcLockstep wfcW4Body wfcW4S7 wfcW4S8 m₇ m₈ 7 0x4340000000000002 8 ∧
      WfcLockstep wfcW4Body wfcW4S8 wfcW4S9 m₈ m₉ 0 0xC3000000 4 ∧
      WfcReturns wfcW4Body wfcW4S9 m₉ (.scalar ⟨0xC3000000, 4⟩) := by
  have hph : ∀ p, wfcW4Body.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hret⟩ := wfcW4_anneal_run
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant wfcW4_stateRel_init (wfc_allImm_init _ _) hph rfl rfl
    rfl (.floatToInt rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h1 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_copy l₁.2.2.1 i₁ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl h2 rfl
  obtain ⟨m₃, l₃, i₃⟩ := wfc_step_move l₂.2.2.1 i₂ hph rfl rfl rfl rfl
    (.intToFloat rfl rfl) rfl rfl h3 rfl
  obtain ⟨m₄, l₄, i₄⟩ := wfc_step_constant l₃.2.2.1 i₃ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB16 (by decide) rfl rfl h4 rfl
  obtain ⟨m₅, l₅, i₅⟩ := wfc_step_constant l₄.2.2.1 i₄ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h5 rfl
  obtain ⟨m₆, l₆, i₆⟩ := wfc_step_constant l₅.2.2.1 i₅ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB4 (by decide) rfl rfl h6 rfl
  obtain ⟨m₇, l₇, i₇⟩ := wfc_step_constant l₆.2.2.1 i₆ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h7 rfl
  obtain ⟨m₈, l₈, i₈⟩ := wfc_step_constant l₇.2.2.1 i₇ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB8 (by decide) rfl rfl h8 rfl
  obtain ⟨m₉, l₉, i₉⟩ := wfc_step_constant l₈.2.2.1 i₈ hph rfl rfl
    rfl (.intToFloat rfl rfl) rfl rfl wfcVSB1 (by decide) rfl rfl h9 rfl
  exact ⟨m₁,
    m₂,
    m₃,
    m₄,
    m₅,
    m₆,
    m₇,
    m₈,
    m₉,
    l₁,
    l₂,
    l₃,
    wfc_miri_uninit l₃.2.2.1 i₃ rfl (Or.inr ⟨_, rfl⟩) rfl,
    l₄,
    l₅,
    l₆,
    l₇,
    l₈,
    l₉,
    wfc_step_return l₉.2.2.1 i₉ hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩


/-! ## (W5) Negative controls: UB, fail-closed boundaries, and memory-backed locals -/

/-- **(W5a) uninitialized-source body** `bb0: _0 = copy _1 as u32; return` (`_0 : u32`,
`_1 : f64` never written). -/
def wfcW5UBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_copy" [wfcDecl (wfcUintTy .u32), wfcDecl wfcF64Ty] 4
    [.assign (local_ 0) (.cast .floatToInt (.copy (local_ 1)) (wfcUintTy .u32))]

def wfcW5US0 : MachineState := wfcAt wfcW5UBody 0 [.uninit, .uninit]

/-- **(W5a') uninitialized integer-source body** `bb0: _0 = move _1 as f32; return`
(`_0 : f32`, `_1 : i64` never written). -/
def wfcW5U2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_move" [wfcDecl wfcF32Ty, wfcDecl (wfcIntTy .i64)] 4
    [.assign (local_ 0) (.cast .intToFloat (.move (local_ 1)) wfcF32Ty)]

def wfcW5U2S0 : MachineState := wfcAt wfcW5U2Body 0 [.uninit, .uninit]

/-- **(W5a) uninitialized sources fault in both machines**: reading the never-written `_1`
(by `copy` in a float-to-int cast and by `move` in an int-to-float cast) makes Anneal's
`stepMirFn` fail with `.ub` and `lean-miri`'s `Step.step` report `.undefinedBehavior`
(`StepRelLM3_1.ub`). -/
theorem wfcW5_uninit_source_ub :
    WfcUB wfcW5UBody wfcW5US0 (wfcMiriInit wfcW5UBody (wfcUintTy .u32)) ∧
    WfcUB wfcW5U2Body wfcW5U2S0 (wfcMiriInit wfcW5U2Body wfcF32Ty) :=
  ⟨wfc_ub_copy (wfc_stateRel_init wfcW5UBody (wfcUintTy .u32) wfcW5US0 rfl rfl rfl rfl rfl rfl)
      (wfc_allImm_init _ _) (fun _ h => nomatch h) rfl rfl rfl rfl (.floatToInt rfl rfl) rfl rfl
      rfl,
    wfc_ub_move (wfc_stateRel_init wfcW5U2Body wfcF32Ty wfcW5U2S0 rfl rfl rfl rfl rfl rfl)
      (wfc_allImm_init _ _) (fun _ h => nomatch h) rfl rfl rfl rfl (.intToFloat rfl rfl) rfl rfl
      rfl⟩

/-- **(W5b) moved-from-source body** (`_0 : i32`, `_1 : f64`, `_2 : f32`):
```text
bb0: _2 = const 2.5_f64 as f32     // 0x4020_0000
     _1 = move _2 as f64           // 0x4004_0000_0000_0000, `_2` deinitialized
     _0 = move _2 as i32           // read of moved-from `_2`: UB
     return
``` -/
def wfcW5MBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_moved_from"
    [wfcDecl (wfcIntTy .i32), wfcDecl wfcF64Ty, wfcDecl wfcF32Ty] 4
    [.assign (local_ 2) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x4004000000000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.move (local_ 2)) wfcF64Ty),
     .assign (local_ 0) (.cast .floatToInt (.move (local_ 2)) (wfcIntTy .i32))]

def wfcW5MS0 : MachineState := wfcAt wfcW5MBody 0 [.uninit, .uninit, .uninit]
def wfcW5MS1 : MachineState := wfcAt wfcW5MBody 1
  [.uninit, .uninit, .init (.scalar ⟨0x40200000, 4⟩)]
def wfcW5MS2 : MachineState := wfcAt wfcW5MBody 2
  [.uninit, .init (.scalar ⟨0x4004000000000000, 8⟩), .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5M_anneal_run :
    stepMirFn wfcW5MBody wfcW5MS0 = .step wfcW5MS1 ∧
    stepMirFn wfcW5MBody wfcW5MS1 = .step wfcW5MS2 ∧
    stepMirFn wfcW5MBody wfcW5MS2 = .fail .ub :=
  ⟨rfl, rfl, rfl⟩

/-- **(W5b) moved-from sources fault in both machines**: after two lockstep steps (the second
deinitializes `_2` in both machines), `move _2` makes Anneal fail with `.ub` and `lean-miri`
report `.undefinedBehavior`. -/
theorem wfcW5_moved_from_ub :
    ∃ m₁ m₂ : AnnealStepState,
      WfcLockstep wfcW5MBody wfcW5MS0 wfcW5MS1 (wfcMiriInit wfcW5MBody (wfcIntTy .i32)) m₁ 2
        0x40200000 4 ∧
      WfcLockstep wfcW5MBody wfcW5MS1 wfcW5MS2 m₁ m₂ 1 0x4004000000000000 8 ∧
      MiriHoldsUninit m₂ 2 ∧
      WfcUB wfcW5MBody wfcW5MS2 m₂ := by
  have hph : ∀ p, wfcW5MBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨h1, h2, h3⟩ := wfcW5M_anneal_run
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant
    (wfc_stateRel_init wfcW5MBody (wfcIntTy .i32) wfcW5MS0 rfl rfl rfl rfl rfl rfl)
    (wfc_allImm_init _ _) hph rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl wfcVSB8 (by decide)
    rfl rfl h1 rfl
  obtain ⟨m₂, l₂, i₂⟩ := wfc_step_move l₁.2.2.1 i₁ hph rfl rfl rfl rfl (.floatToFloat rfl rfl)
    rfl rfl h2 rfl
  exact ⟨m₁, m₂, l₁, l₂, wfc_miri_uninit l₂.2.2.1 i₂ rfl (Or.inl ⟨_, rfl⟩) rfl,
    wfc_ub_move l₂.2.2.1 i₂ hph rfl rfl rfl rfl (.floatToInt rfl rfl) rfl rfl h3⟩

/-! ### (W5c) Dead (`StorageDead` / never-`StorageLive`) sources, run from program entry -/

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

/-- `f16`. -/
def wfcF16Ty : Ty := { kind := .float .f16, layoutIdx := 0 }
/-- `f128`. -/
def wfcF128Ty : Ty := { kind := .float .f128, layoutIdx := 0 }

/-- **(W5d) `f16` source body** `bb0: _0 = const 1.0_f16 (0x3C00) as f32; return`. -/
def wfcW5HBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_f16_source" [wfcDecl wfcF32Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF16Ty 0x3C00 2)) wfcF32Ty)]

def wfcW5HS0 : MachineState := wfcAt wfcW5HBody 0 [.uninit]

/-- **(W5d) `f128` target body** (`_0 : f32`, `_1 : f128`):
`bb0: _0 = const 1.0_f64 as f32; _1 = const 1.0_f64 as f128; return`. -/
def wfcW5H2Body : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_f128_target" [wfcDecl wfcF32Ty, wfcDecl wfcF128Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x3FF0000000000000 8))
      wfcF32Ty),
     .assign (local_ 1) (.cast .floatToFloat (.constant (wfcConst wfcF64Ty 0x3FF0000000000000 8))
      wfcF128Ty)]

def wfcW5H2S0 : MachineState := wfcAt wfcW5H2Body 0 [.uninit, .uninit]
def wfcW5H2S1 : MachineState := wfcAt wfcW5H2Body 1 [.init (.scalar ⟨0x3F800000, 4⟩), .uninit]

set_option maxRecDepth 200000 in
theorem wfcW5H_anneal_run :
    stepMirFn wfcW5HBody wfcW5HS0 = .unsupported ∧
    stepMirFn wfcW5H2Body wfcW5H2S0 = .step wfcW5H2S1 :=
  ⟨rfl, rfl⟩

/-- **(W5d) `f16` / `f128` casts fail closed in both machines** (`step_cast_f16_f128_constant_fail_closed`):
an `f16` source (`1.0_f16 as f32`) makes Anneal's `stepMirFn` return `.unsupported` and
`lean-miri`'s `Step.step` report `.unsupported` at entry; and after a lockstep
`1.0_f64 as f32` step, an `f128` target (`1.0_f64 as f128`) fails closed in both machines. -/
theorem wfcW5_f16_f128_fail_closed :
    (stepMirFn wfcW5HBody wfcW5HS0 = .unsupported ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooksFloat wfcW5HBody.localDecls wfcW5HBody.layouts) ()
          (wfcMiriInit wfcW5HBody wfcF32Ty) = (m', .error (.unsupported msg))) ∧
    ∃ m₁, WfcLockstep wfcW5H2Body wfcW5H2S0 wfcW5H2S1 (wfcMiriInit wfcW5H2Body wfcF32Ty) m₁ 0
        0x3F800000 4 ∧
      stepMirFn wfcW5H2Body wfcW5H2S1 = .unsupported ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooksFloat wfcW5H2Body.localDecls wfcW5H2Body.layouts) () m₁ =
        (m', .error (.unsupported msg)) := by
  obtain ⟨_, h2⟩ := wfcW5H_anneal_run
  have hph : ∀ p, wfcW5HBody.phase ≠ .other p := fun _ h => nomatch h
  have hph2 : ∀ p, wfcW5H2Body.phase ≠ .other p := fun _ h => nomatch h
  refine ⟨step_cast_f16_f128_constant_fail_closed
    (wfc_stateRel_init wfcW5HBody wfcF32Ty wfcW5HS0 rfl rfl rfl rfl rfl rfl) hph true
    annealChooseQuietedNaN rfl rfl rfl rfl rfl rfl wfcVSB2 (by decide) rfl (Or.inl (Or.inl rfl)), ?_⟩
  obtain ⟨m₁, l₁, i₁⟩ := wfc_step_constant
    (wfc_stateRel_init wfcW5H2Body wfcF32Ty wfcW5H2S0 rfl rfl rfl rfl rfl rfl)
    (wfc_allImm_init _ _) hph2 rfl rfl rfl (.floatToFloat rfl rfl) rfl rfl
    wfcVSB8 (by decide) rfl rfl h2 rfl
  exact ⟨m₁, l₁, step_cast_f16_f128_constant_fail_closed l₁.2.2.1 hph2 true
    annealChooseQuietedNaN rfl rfl rfl rfl rfl rfl wfcVSB8 (by decide) rfl
    (Or.inr ⟨Or.inr ⟨Or.inl rfl, _, rfl⟩, Or.inr rfl⟩)⟩

/-- **(W5d') uninitialized `f16` source body** `bb0: _0 = copy _1 as f32; return` (`_0 : f32`,
`_1 : f16` uninitialized). -/
def wfcW5UninitF16SrcBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_f16_src" [wfcDecl wfcF32Ty, wfcDecl wfcF16Ty] 4
    [.assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) wfcF32Ty)]

def wfcW5UninitF16SrcS0 : MachineState := wfcAt wfcW5UninitF16SrcBody 0 [.uninit, .uninit]

/-- **(W5d') uninitialized `f32 → f128` target body** `bb0: _1 = copy _0 as f128; return`
(`_0 : f32` uninitialized, `_1 : f128`). -/
def wfcW5UninitF128DstBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_uninit_f128_dst" [wfcDecl wfcF32Ty, wfcDecl wfcF128Ty] 4
    [.assign (local_ 1) (.cast .floatToFloat (.copy (local_ 0)) wfcF128Ty)]

def wfcW5UninitF128DstS0 : MachineState := wfcAt wfcW5UninitF128DstBody 0 [.uninit, .uninit]

/-- **(W5d') source-vs-target evaluation-order contrast on uninitialized `f16` / `f128` casts**
(`step_cast_f16_f128_uninit_source_divergence` vs `step_cast_f16_f128_uninit_target_ub_lockstep`):
* on `_0 = copy _1_f16 as f32` with uninitialized `_1`, Anneal rejects the uninitialized read with
  `.fail .ub` whereas `lean-miri`'s `Cast.cast` checks `h.typeInfo` on the `f16` source *before*
  reading `_1` and fails closed with `.error (.unsupported _)` (`¬ StepRelLM3_1`);
* on `_1 = copy _0_f32 as f128` with uninitialized `_0`, `lean-miri`'s `Cast.cast` reads the modeled
  `f32` source *before* checking `h.typeInfo` on the `f128` target, so **both** machines report UB
  in lockstep (`WfcUB`, `StepRelLM3_1.ub`). -/
theorem wfcW5_f16_f128_uninit_source_vs_target :
    let mSrc := wfcMiriInit wfcW5UninitF16SrcBody wfcF32Ty
    let mDst := wfcMiriInit wfcW5UninitF128DstBody wfcF32Ty
    (stepMirFn wfcW5UninitF16SrcBody wfcW5UninitF16SrcS0 = .fail .ub ∧
      (∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooksFloat wfcW5UninitF16SrcBody.localDecls wfcW5UninitF16SrcBody.layouts)
          () mSrc = (m', .error (.unsupported msg))) ∧
      ¬ StepRelLM3_1 wfcW5UninitF16SrcBody mSrc []
          (stepMirFn wfcW5UninitF16SrcBody wfcW5UninitF16SrcS0)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat wfcW5UninitF16SrcBody.localDecls wfcW5UninitF16SrcBody.layouts)
            () mSrc)) ∧
    WfcUB wfcW5UninitF128DstBody wfcW5UninitF128DstS0 mDst := by
  intro mSrc mDst
  have hdiv := step_cast_f16_f128_uninit_source_divergence
    (wfc_stateRel_init wfcW5UninitF16SrcBody wfcF32Ty wfcW5UninitF16SrcS0 rfl rfl rfl rfl rfl rfl)
    (fun _ h => nomatch h) true annealChooseQuietedNaN rfl rfl rfl rfl rfl (Or.inl rfl) rfl rfl
  have hub := step_cast_f16_f128_uninit_target_ub_lockstep
    (wfc_stateRel_init wfcW5UninitF128DstBody wfcF32Ty wfcW5UninitF128DstS0 rfl rfl rfl rfl rfl rfl)
    (fun _ h => nomatch h) true annealChooseQuietedNaN rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩)
    (Or.inr rfl) rfl rfl (fun tf htf => wfc_allImm_init _ _ tf htf 0)
  exact ⟨hdiv, hub.1, hub.2, wfc_ub_of_stepRel hub.2 hub.1⟩

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

/-- **(W5f-1a) uninitialized promoted-local UB body** (`_0 : f64`, `_1 : i64`, `_2 : *mut i64`):
`bb0: _2 = &raw mut _1; _0 = copy _1 as f64; return`. -/
def wfcW5PromUBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_promoted_uninit_ub"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty] 8
    [.assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty)]

def wfcW5PromUS0 : MachineState := wfcAt wfcW5PromUBody 0 [.uninit, .uninit, .uninit]

abbrev wfcW5PromUE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5PromUBody.localDecls wfcW5PromUBody.layouts .mut 1 1 floatWitAllocId1

def wfcW5PromUS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { wfcW5PromUS0.memory with borrows := [wfcW5PromUE1.toBorrowEntry], nextTag := 2 } }

/-- **(W5f-1a) reading an uninitialized `&raw`-promoted local in a float cast faults with UB in
both machines**: `_2 = &raw mut _1` promotes `.uninit` `_1 : i64` into `allocMap = [wfcW5PromUE1]`
at `AllocId 1` (`MiriHoldsIndirectUninit`), and `_0 = copy _1 as f64` faults with `.ub` in both
`stepMirFn` and `Step.step` (`WfcUB ... [wfcW5PromUE1]`). -/
theorem wfcW5_promoted_uninit_ub :
    ∃ m₁ : AnnealStepState,
      let b := wfcW5PromUBody
      stepMirFn b wfcW5PromUS0 = .step wfcW5PromUS1 ∧
      Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) ()
        (wfcMiriInit b wfcF64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b wfcW5PromUS1 m₁ [wfcW5PromUE1] ∧
      MiriHoldsIndirectUninit m₁ 1 floatWitAllocId1 (Miri.ABI.Size.ofBytes 8) ∧
      WfcUB b wfcW5PromUS1 m₁ [wfcW5PromUE1] := by
  have hph : ∀ p, wfcW5PromUBody.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ := wfc_stateRel_init wfcW5PromUBody wfcF64Ty wfcW5PromUS0 rfl rfl rfl rfl rfl rfl
  have himm₀ := wfc_allImm_init wfcW5PromUBody wfcF64Ty
  have hs₁ : stepMirFn wfcW5PromUBody wfcW5PromUS0 = .step wfcW5PromUS1 := rfl
  have hs₂ : stepMirFn wfcW5PromUBody wfcW5PromUS1 = .fail .ub := rfl
  have hm_eq₁ := step_float_eq_annealStepHooks_at_stmt hrel₀ true annealChooseQuietedNaN rfl rfl rfl
  have hr₁ := step_rawPtr_addrOf_lm3_1_simulation hrel₀ hph rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁_base, hrel₁⟩ := wfc_step_of_stepRel hr₁ hs₁
  have hm₁ : Miri.Interpreter.Step.step
      (annealStepHooksFloat wfcW5PromUBody.localDecls wfcW5PromUBody.layouts) ()
      (wfcMiriInit wfcW5PromUBody wfcF64Ty) = (m₁, .ok true) := hm_eq₁.trans hm₁_base
  have htag₀ : wfcW5PromUS0.memory.nextTag = 1 := rfl
  have hid₀ : (⟨(wfcMiriInit wfcW5PromUBody wfcF64Ty).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = floatWitAllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty (by decide)
    (fun h => nomatch h) hm₁_base
  have himm₁_0 : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 0 :=
    fun tf₁ htf₁ => himm₁_step _ tf₁ rfl htf₁ 0 (by decide) (himm₀ _ rfl 0)
  have hr₂ : StepRelLM3_1 wfcW5PromUBody m₁ [wfcW5PromUE1]
      (stepMirFn wfcW5PromUBody wfcW5PromUS1)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat wfcW5PromUBody.localDecls wfcW5PromUBody.layouts) () m₁) :=
    step_cast_float_copy_anyLocal_simulation hrel₁ hph rfl rfl rfl rfl
      (.intToFloat (t := .signed .i64) rfl rfl) rfl
      (fun _ _ => Or.inr ⟨wfcW5PromUE1, .head _, rfl⟩)
      (fun tf₁ htf₁ => Or.inl (himm₁_0 tf₁ htf₁))
  have hun₁ := wfc_miri_promoted_uninit hrel₁ (.head _) rfl (Or.inr ⟨.signed .i64, rfl⟩) rfl
  exact ⟨m₁, hs₁, hm₁, hrel₁, hun₁, hs₂, hr₂, wfc_ub_of_stepRel hr₂ hs₂⟩

/-- **(W5f-1b) multi-step `&raw`-promoted local + float-cast pipeline ending in `return`**
(`_0 : f64` returned, `_1 : i64`, `_2 : *mut i64`, `_3 : f32`):
```text
bb0: _2 = &raw mut _1                             // promotes _1 into allocMap = [e₁] at AllocId 1
     _1 = const -42.75_f64 as i64                 // writes -42_i64 to AllocId 1, disables e₁
     _3 = copy _1 as f32                          // reads AllocId 1 ↦ -42.0_f32 (0xC228_0000)
     _1 = move _3 as i64                          // writes -42_i64 to AllocId 1, deinitializes _3
     _0 = copy _1 as f64                          // reads AllocId 1 ↦ -42.0_f64 (0xC045_0000_0000_0000)
     return
``` -/
def wfcW5PromBody : CapturedMir :=
  wfcBody "wit_float_cast_lm::w5_promoted_raw_pipeline"
    [wfcDecl wfcF64Ty, wfcDecl (wfcIntTy .i64), wfcDecl wfcRawPtrMutI64Ty, wfcDecl wfcF32Ty] 8
    [.assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 1) (.cast .floatToInt (.constant (wfcConst wfcF64Ty 0xC045600000000000 8))
       (wfcIntTy .i64)),
     .assign (local_ 3) (.cast .intToFloat (.copy (local_ 1)) wfcF32Ty),
     .assign (local_ 1) (.cast .floatToInt (.move (local_ 3)) (wfcIntTy .i64)),
     .assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) wfcF64Ty)]

def wfcW5PromE1 : AllocMapEntry :=
  rawPtrAllocMapEntry wfcW5PromBody.localDecls wfcW5PromBody.layouts .mut 1 1 floatWitAllocId1

def wfcW5PromMap2 : List AllocMapEntry :=
  updateAllocMapOnWrite [wfcW5PromE1] 1 none

def wfcW5PromBor1 : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }

def wfcW5PromBor2 : BorrowEntry :=
  { tag := 1, targetLocal := 1, targetProjection := [], perm := .disabled, allocDead := false }

def wfcW5PromS0 : MachineState := wfcAt wfcW5PromBody 0 [.uninit, .uninit, .uninit, .uninit]
def wfcW5PromS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                          .uninit] }
    memory := { wfcW5PromS0.memory with borrows := [wfcW5PromBor1], nextTag := 2 } }
def wfcW5PromS2 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 2,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := { wfcW5PromS1.memory with borrows := [wfcW5PromBor2] } }
def wfcW5PromS3 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                          .init (.scalar ⟨0xC2280000, 4⟩)] }
    memory := wfcW5PromS2.memory }
def wfcW5PromS4 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 4,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := wfcW5PromS3.memory }
def wfcW5PromS5 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 5,
               locals := [.init (.scalar ⟨0xC045000000000000, 8⟩),
                          .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] }
    memory := wfcW5PromS4.memory }

set_option maxRecDepth 200000 in
theorem wfcW5Prom_anneal_run :
    stepMirFn wfcW5PromBody wfcW5PromS0 = .step wfcW5PromS1 ∧
    stepMirFn wfcW5PromBody wfcW5PromS1 = .step wfcW5PromS2 ∧
    stepMirFn wfcW5PromBody wfcW5PromS2 = .step wfcW5PromS3 ∧
    stepMirFn wfcW5PromBody wfcW5PromS3 = .step wfcW5PromS4 ∧
    stepMirFn wfcW5PromBody wfcW5PromS4 = .step wfcW5PromS5 ∧
    stepMirFn wfcW5PromBody wfcW5PromS5 =
      .retNormal (.scalar ⟨0xC045000000000000, 8⟩)
        { wfcW5PromS5.memory with
          borrows := disableFrameBorrows wfcW5PromS5.memory.borrows 0 4 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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
`return` witness**: from `wfcMiriInit`, `_2 = &raw mut _1` promotes `_1 : i64` into
`allocMap = [wfcW5PromE1]` at `AllocId 1`; `_1 = const -42.75_f64 as i64` writes `-42_i64` into
`lean-miri`'s stack allocation at `AllocId 1` (`MiriHoldsIndirectScalar`) and disables `wfcW5PromE1`
(`perm = .disabled`); `_3 = copy _1 as f32` reads the promoted stack allocation into immediate `_3`
(`-42.0_f32`); `_1 = move _3 as i64` deinitializes `_3` (`MiriHoldsUninit`) and writes `-42_i64`
back into `AllocId 1`; `_0 = copy _1 as f64` reads `AllocId 1` into immediate `_0` (`-42.0_f64`);
and `wfc_step_return_any` pops the root frame and returns `-42.0_f64` in both machines despite
`allocMap ≠ []` and memory-backed `_1`! -/
theorem wfcW5_promoted_raw_pipeline_end_to_end :
    ∃ m₁ m₂ m₃ m₄ m₅ : AnnealStepState,
      let b := wfcW5PromBody
      let hooks := annealStepHooksFloat b.localDecls b.layouts
      stepMirFn b wfcW5PromS0 = .step wfcW5PromS1 ∧
      Miri.Interpreter.Step.step hooks () (wfcMiriInit b wfcF64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS1 m₁ [wfcW5PromE1] ∧
      MiriHoldsIndirectUninit m₁ 1 floatWitAllocId1 (Miri.ABI.Size.ofBytes 8) ∧
      stepMirFn b wfcW5PromS1 = .step wfcW5PromS2 ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS2 m₂ wfcW5PromMap2 ∧
      wfcW5PromMap2 = [{ wfcW5PromE1 with perm := .disabled, allocDead := false }] ∧
      MiriHoldsIndirectScalar m₂ 1 floatWitAllocId1 ⟨0xFFFFFFFFFFFFFFD6, 8⟩ ∧
      stepMirFn b wfcW5PromS2 = .step wfcW5PromS3 ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS3 m₃ wfcW5PromMap2 ∧
      MiriHoldsScalar m₃ 3 ⟨0xC2280000, 4⟩ ∧
      stepMirFn b wfcW5PromS3 = .step wfcW5PromS4 ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS4 m₄ wfcW5PromMap2 ∧
      MiriHoldsUninit m₄ 3 ∧
      MiriHoldsIndirectScalar m₄ 1 floatWitAllocId1 ⟨0xFFFFFFFFFFFFFFD6, 8⟩ ∧
      stepMirFn b wfcW5PromS4 = .step wfcW5PromS5 ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b wfcW5PromS5 m₅ wfcW5PromMap2 ∧
      MiriHoldsScalar m₅ 0 ⟨0xC045000000000000, 8⟩ ∧
      WfcReturns b wfcW5PromS5 m₅ (.scalar ⟨0xC045000000000000, 8⟩) := by
  have hph : ∀ p, wfcW5PromBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hs₁, hs₂, hs₃, hs₄, hs₅, hret⟩ := wfcW5Prom_anneal_run
  have hrel₀ := wfc_stateRel_init wfcW5PromBody wfcF64Ty wfcW5PromS0 rfl rfl rfl rfl rfl rfl
  have himm₀ := wfc_allImm_init wfcW5PromBody wfcF64Ty
  -- Step 1: `_2 = &raw mut _1`
  have hm_eq₁ := step_float_eq_annealStepHooks_at_stmt hrel₀ true annealChooseQuietedNaN rfl rfl rfl
  have hr₁ := step_rawPtr_addrOf_lm3_1_simulation hrel₀ hph rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁_base, hrel₁⟩ := wfc_step_of_stepRel hr₁ hs₁
  have hm₁ : Miri.Interpreter.Step.step
      (annealStepHooksFloat wfcW5PromBody.localDecls wfcW5PromBody.layouts) ()
      (wfcMiriInit wfcW5PromBody wfcF64Ty) = (m₁, .ok true) := hm_eq₁.trans hm₁_base
  have hmap₁_eq :
      [rawPtrAllocMapEntry wfcW5PromBody.localDecls wfcW5PromBody.layouts .mut 1
        wfcW5PromS0.memory.nextTag
        ⟨(wfcMiriInit wfcW5PromBody wfcF64Ty).machine.memory.nextAllocId,
          AllocIdSupplyReady.empty.nonzero⟩] = [wfcW5PromE1] := rfl
  have hrel₁' : StateRelLM3_1 wfcW5PromBody wfcW5PromS1 m₁ [wfcW5PromE1] :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS1 m₁) hmap₁_eq).mp hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inl ⟨.i64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty (by decide)
    (fun h => nomatch h) hm₁_base
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀ _ rfl k)
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
  have hrel₃ : StateRelLM3_1 wfcW5PromBody wfcW5PromS3 m₃ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS3 m₃) hmap₃_eq).mp hrel₃_raw
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
  have hrel₄ : StateRelLM3_1 wfcW5PromBody wfcW5PromS4 m₄ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS4 m₄) hmap₄_eq).mp hrel₄_raw
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
  have hrel₅ : StateRelLM3_1 wfcW5PromBody wfcW5PromS5 m₅ wfcW5PromMap2 :=
    (congrArg (StateRelLM3_1 wfcW5PromBody wfcW5PromS5 m₅) hmap₅_eq).mp hrel₅_raw
  have hp₅ := step_cast_float_copy_anyLocal_preserves hrel₄ true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl rfl (.intToFloat (t := .signed .i64) rfl rfl) rfl
    (fun h => nomatch h) (fun _ _ => Or.inr ⟨_, he₂, rfl⟩)
    (fun tf₄ htf₄ => Or.inl (himm₄ tf₄ htf₄ 0 (by decide))) rfl m₅ hm₅
  have himm₅ := wfc_preserves_imm_ne hrel₄ hp₅.2 himm₄
  have himm₅_0 : ∀ tf₅, m₅.stack.frames = #[tf₅] → IsImmediateFrameLocal tf₅ 0 :=
    fun tf₅ htf₅ => himm₅ tf₅ htf₅ 0 (by decide)
  exact ⟨m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁',
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
    wfc_step_return_any hrel₅ himm₅_0 hph rfl rfl rfl rfl rfl rfl (Or.inl ⟨_, rfl⟩) hret⟩

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
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW1_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW1_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_end_to_end

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW2_deterministic_canonicalization' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW2_deterministic_canonicalization

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
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW3_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW3_stateRel_init

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
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_anneal_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_anneal_run

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_stateRel_init' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_stateRel_init

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW4_end_to_end' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW4_end_to_end

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
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageLive' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageLive

/--
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfc_step_storageDead' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfc_step_storageDead

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
info: 'LeanMiriSpec.Correspondence.WitFloatCast.wfcW5_promoted_uninit_ub' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wfcW5_promoted_uninit_ub

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
