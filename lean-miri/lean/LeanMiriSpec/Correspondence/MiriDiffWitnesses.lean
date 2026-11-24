/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.Correspondence.MiriDiffWitnessesPart3

/-!
# `LM-4.3`: `miri-diff` Formal Witness Suite (Final Part)

Continuation of `MiriDiffWitnessesPart1`..`MiriDiffWitnessesPart3` in the
`LeanMiriSpec.Correspondence.MiriDiffWitnesses` namespace.
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
      .running retWriteBytesOobPreAnneal := by kernel_rfl

/-- The entry block of `retWriteBytesOobBody`, from `miriEntryState`. -/
theorem retWriteBytesOob_prefix_miri :
    runLoopFuel (annealMiriHooks retWriteBytesOobBody) 5 (miriEntryState retWriteBytesOobBody) =
      .running retWriteBytesOobPreMiri := by kernel_rfl

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

/-- **Out-of-bounds `write_bytes`, whole program from entry, undefined behavior in
both machines** (`retWriteBytesOobBody`): `StorageLive(_1.._3); _1 = const 42_u64;
goto bb1; bb1: _2 = &raw mut _1; _3 = write_bytes::<u64>(copy _2, 0xAB, 2) -> bb2;
bb2: _0 = copy (*_2); return`, run from `initMachineState` / `miriEntryState`.

* `lean-miri` takes the entry block and `_2 = &raw mut _1` in lockstep with Anneal
  (`step_rawPtr_addrOf_simulation`), then reports the `16`-byte write into the
  `8`-byte allocation of `_1` as undefined behavior (in lockstep with the
  pre-Stage-1 reference model `stepMirFnLM4_2`, `call_intrinsic_write_bytes_simulation`):
  `miriSystem` reaches `.undefinedBehavior` and is not `System.Safe`.
* Stage-1 `stepMirFn` executes `write_bytes` inline
  (`Trusted.Rustc.V2026_06_01.MirSemantics.evalWriteBytesCall`, since
  `ws-repatriate-leaked-ground-semantics-to-tcb`): the write extends past the end
  of the whole local `_1`, a separate allocation, so Anneal's whole program
  reaches undefined behavior and is not `TreeSafe` (`AgreeUB`). (Before that
  episode, Stage-1 handed the call to the environment and returned the unchanged
  `42_u64`.) -/
theorem w6_write_bytes_oob_ub :
    AgreeUB retWriteBytesOobBody (annealMiriHooks retWriteBytesOobBody)
      (initMachineState retWriteBytesOobBody []) (miriEntryState retWriteBytesOobBody) := by
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
  have hs₁ : stepMirFn b retWriteBytesOobPreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFnLM4_2 b s₁ = .fail .ub := by kernel_rfl
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
  -- Anneal: the whole program reaches undefined behavior at the out-of-bounds write.
  have hA := anneal_ub_of_obs (body := b) (N := 30) (s := initMachineState b []) (by kernel_decide)
  exact ⟨hA.1, hA.2, ⟨_, h.1⟩, h.2⟩

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

/-- Entry-to-return MIR body for Stage-1 multi-element `copyBytesSubplace`:
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
      .running retCopyFullBytesPreAnneal := by kernel_rfl

private theorem retCopyFullBytes_prefix_miri :
    runLoopFuel (annealMiriHooks retCopyFullBytesEntryBody) 8
      (miriEntryState retCopyFullBytesEntryBody) =
      .running retCopyFullBytesPreMiri := by kernel_rfl

/-- **Stage-1 multi-element `copyBytesSubplace` lockstep return from entry**
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
  have hs₁ : stepMirFn b retCopyFullBytesPreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
  have hs₃ : stepMirFn b s₂ = .step s₃ := by kernel_rfl
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
  have hs₄ : stepMirFn b s₃ = .step s₄ := by kernel_rfl
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
  have hs₅ : stepMirFn b s₄ = .step s₅ := by kernel_rfl
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
  have hmap_eq : copyStage1FullBytesNextAllocMap s₄.frame.locals [e₂, e₁] 5 6
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
  have hs₆ : stepMirFn b s₅ = .step s₆ := by kernel_rfl
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
  have hs₇ : stepMirFn b s₆ = .retNormal (.scalar ⟨0x0102030405060708, 8⟩)
      { s₆.memory with borrows := disableFrameBorrows s₆.memory.borrows 0 b.localDecls.length } := by kernel_rfl
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

/-- Entry-prefixed `copyStage1RawPtrCastLockstepBody` (`bb0: StorageLive(_1.._5);
_1 = 0x0102030405060708_u64; _2 = 0_u64; goto -> bb1; bb1: _0 = &raw const _1;
_3 = &raw mut _2; _4 = copy _0 as *const *mut u64; _5 = copy _3 as *mut *mut u64;
copy_nonoverlapping::<*mut u64>(copy _4, copy _5, 1); return`). -/
def copyStage1RawPtrCastEntryBody : CapturedMir where
  defPath := "lm_4_3_witness::copy_stage1_rawptr_cast_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := WitnessLM4_2.copyStage1RawPtrCastLockstepBody.localDecls
  basicBlocks := [
    { statements := [
        WitnessLM4_2.mkStmt42 (.storageLive 1), WitnessLM4_2.mkStmt42 (.storageLive 2),
        WitnessLM4_2.mkStmt42 (.storageLive 3), WitnessLM4_2.mkStmt42 (.storageLive 4),
        WitnessLM4_2.mkStmt42 (.storageLive 5),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 1)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 0x0102030405060708 8)))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2)
          (.use (.constant (WitnessLM4_2.constInt WitnessLM4_2.u64K 0 8))))]
      terminator := WitnessLM4_2.mkTerm42 (.goto 1), isCleanup := false },
    { statements := [
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 0) (.rawPtr .not (WitnessLM4_2.local42 1))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 3) (.rawPtr .mut (WitnessLM4_2.local42 2))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 4)
          (.cast .ptrToPtr (.copy (WitnessLM4_2.local42 0))
            (WitnessLM4_2.tyOf (.rawPtr .not WitnessLM4_2.rawMutU64K)))),
        WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 5)
          (.cast .ptrToPtr (.copy (WitnessLM4_2.local42 3))
            (WitnessLM4_2.tyOf (.rawPtr .mut WitnessLM4_2.rawMutU64K)))),
        WitnessLM4_2.copyStmt 4 5 1]
      terminator := WitnessLM4_2.mkTerm42 .return_, isCleanup := false }]
  fnAbi := Witness.fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Post-entry-block Anneal state of `copyStage1RawPtrCastEntryBody` (at `bb1`). -/
def copyStage1RawPtrCastEntryPreAnneal : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨0x0102030405060708, 8⟩),
                          .init (.scalar ⟨0, 8⟩), .uninit, .uninit, .uninit] }
    memory := (initMachineState copyStage1RawPtrCastEntryBody []).memory }

/-- Post-entry-block `lean-miri` root frame of `copyStage1RawPtrCastEntryBody`. -/
def copyStage1RawPtrCastEntryPreMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (miriEntryFrame copyStage1RawPtrCastEntryBody) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarSrc))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarZero))),
        layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    location := .mir ⟨1, 0⟩ }

/-- Post-entry-block `lean-miri` state of `copyStage1RawPtrCastEntryBody`. -/
def copyStage1RawPtrCastEntryPreMiri : AnnealStepState :=
  { stack := ⟨#[copyStage1RawPtrCastEntryPreMiriFrame]⟩, machine := AnnealMachine.empty }

/-- The entry block of `copyStage1RawPtrCastEntryBody`, from `initMachineState`. -/
theorem copyStage1RawPtrCastEntry_prefix_anneal :
    runAnnealBounded copyStage1RawPtrCastEntryBody 8
      (initMachineState copyStage1RawPtrCastEntryBody []) =
      .running copyStage1RawPtrCastEntryPreAnneal := by kernel_rfl

/-- The entry block of `copyStage1RawPtrCastEntryBody`, from `miriEntryState`. -/
theorem copyStage1RawPtrCastEntry_prefix_miri :
    runLoopFuel (annealMiriHooks copyStage1RawPtrCastEntryBody) 8
      (miriEntryState copyStage1RawPtrCastEntryBody) =
      .running copyStage1RawPtrCastEntryPreMiri := by kernel_rfl

/-- Post-entry-block `StateRel` and immediateness for `copyStage1RawPtrCastEntryBody`. -/
theorem copyStage1RawPtrCastEntry_stateRel_and_imm :
    StateRel copyStage1RawPtrCastEntryBody
      copyStage1RawPtrCastEntryPreAnneal copyStage1RawPtrCastEntryPreMiri ∧
    ∀ tf, copyStage1RawPtrCastEntryPreMiri.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  refine ⟨?_, ?_⟩
  · refine StateRel.mk copyStage1RawPtrCastEntryPreMiriFrame rfl rfl
      ⟨translateTy (WitnessLM4_2.tyOf WitnessLM4_2.rawConstU64K), rfl⟩ ?_
      rfl rfl rfl rfl rfl (by
        intro i _ _ _ _ _ _ hi _
        match i with
        | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => simp [copyStage1RawPtrCastEntryPreMiriFrame] at hi)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 3 | 4 | 5 =>
      have hs : slot = .uninit := by
        simpa [copyStage1RawPtrCastEntryPreAnneal, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [copyStage1RawPtrCastEntryPreMiriFrame] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [copyStage1RawPtrCastEntryBody, WitnessLM4_2.copyStage1RawPtrCastLockstepBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0x0102030405060708, 8⟩) := by
        simpa [copyStage1RawPtrCastEntryPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarSrc))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [copyStage1RawPtrCastEntryPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ WitnessLM4_2.lm42_scalarRelSrc rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | 2 =>
      have hd : decl = WitnessLM4_2.declOf WitnessLM4_2.u64K := by
        simpa [copyStage1RawPtrCastEntryBody, WitnessLM4_2.copyStage1RawPtrCastLockstepBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0, 8⟩) := by
        simpa [copyStage1RawPtrCastEntryPreAnneal, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt WitnessLM4_2.lm42ScalarZero))),
            layout := some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)) } := by
        simpa [copyStage1RawPtrCastEntryPreMiriFrame] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy (WitnessLM4_2.tyOf WitnessLM4_2.u64K)))
        (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ WitnessLM4_2.lm42_scalarRelZero rfl
          (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 6 => simp [copyStage1RawPtrCastEntryBody, WitnessLM4_2.copyStage1RawPtrCastLockstepBody, get?] at hdecl
  · intro tf h k mls hmls mp hv
    have htf : copyStage1RawPtrCastEntryPreMiriFrame = tf := by
      simpa [copyStage1RawPtrCastEntryPreMiri] using h
    subst htf
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 => simp [copyStage1RawPtrCastEntryPreMiriFrame] at hmls; subst hmls; cases hv
    | _ + 6 => simp [copyStage1RawPtrCastEntryPreMiriFrame] at hmls

/-- Post-entry lockstep trace of `copyStage1RawPtrCastEntryBody` through all 4 setup
steps in `bb1` to the `TyId 80` `lean-miri` `.unsupported` step. -/
theorem copyStage1RawPtrCastEntry_trace :
    let b := copyStage1RawPtrCastEntryBody
    let hooks := annealStepHooks b.localDecls b.layouts
    let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
    let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      stepMirFn b copyStage1RawPtrCastEntryPreAnneal = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () copyStage1RawPtrCastEntryPreMiri = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [e₂, e₁] ∧
      get? s₄.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₄ =
        (m₅, .error (.unsupported "pointee of TyId 80 is not encoded")) := by
  let b := copyStage1RawPtrCastEntryBody
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  obtain ⟨hrel₀, himm₀_all⟩ := copyStage1RawPtrCastEntry_stateRel_and_imm
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, copyStage1RawPtrCastEntryPreMiri.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨himm₀_all tf htf 0, himm₀_all tf htf 1⟩
  let s₁ := WitnessLM4_2.mkPtrState b 1 1
    [.init ptr1, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .uninit, .uninit, .uninit] [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b copyStage1RawPtrCastEntryPreAnneal = .step s₁ := by kernel_rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  rw [hs₁] at hsim₁
  obtain ⟨m₁, hm₁, hrel₁⟩ := hsim₁.miri_step_of_anneal_step
  have htag₀ : copyStage1RawPtrCastEntryPreAnneal.memory.nextTag = 1 := rfl
  have hid₀ : (⟨copyStage1RawPtrCastEntryPreMiri.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = Witness.lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by show 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  let s₂ := WitnessLM4_2.mkPtrState b 1 2
    [.init ptr1, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr2, .uninit, .uninit] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 3 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
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
    (by rw [hnext₁]; show (1 + 1 : UInt32).toNat + 1 < 2 ^ 32; decide)
    (by rw [hsrc₁]; intro h; cases h) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  let s₃ := WitnessLM4_2.mkPtrState b 1 3
    [.init ptr1, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr2, .init ptr1, .uninit] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := by kernel_rfl
  have hsim₃ := step_cast_ptrToPtr_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₂ htf₂ =>
      ⟨himm₂ tf₂ htf₂ 4 (by decide) (by decide), himm₂ tf₂ htf₂ 0 (by decide) (by decide)⟩)
    (fun _ h => by simp [s₂, WitnessLM4_2.mkPtrState, get?] at h)
  rw [hs₃] at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := hsim₃.miri_step_of_anneal_step
  obtain ⟨_, himm₃_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hk₁ hk₂
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hk₁ hk₂)
  let s₄ := WitnessLM4_2.mkPtrState b 1 4
    [.init ptr1, .init (.scalar ⟨0x0102030405060708, 8⟩), .init (.scalar ⟨0, 8⟩),
     .init ptr2, .init ptr1, .init ptr2] [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₄ : stepMirFn b s₃ = .step s₄ := by kernel_rfl
  have hsim₄ := step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₃ htf₃ =>
      ⟨himm₃ tf₃ htf₃ 5 (by decide) (by decide), himm₃ tf₃ htf₃ 3 (by decide) (by decide)⟩)
    (fun _ h => by simp [s₃, WitnessLM4_2.mkPtrState, get?] at h)
  rw [hs₄] at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := hsim₄.miri_step_of_anneal_step
  obtain ⟨_, himm₄_step⟩ := Witness.step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hk₁ hk₂
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hk₁ hk₂)
  obtain ⟨m₅, hm₅⟩ := step_intrinsic_copyNonOverlapping_rawPtr_miri_unsupported
    hrel₄ rfl rfl rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 4 (by decide) (by decide)) (by nofun)
    rfl rfl (fun tf₄ htf₄ => himm₄ tf₄ htf₄ 5 (by decide) (by decide)) (by nofun)
    WitnessLM4_2.usize_integral
    (fun tf₄ _ => WitnessLM4_2.constInt_wellTyped WitnessLM4_2.usize_integral WitnessLM4_2.valid8
      (by decide) rfl b rfl tf₄)
    (Or.inl ⟨_, rfl, rfl⟩)
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, rfl, rfl, hm₅⟩

/-- **Stage-1 provenance-preserving pointer `CopyNonOverlapping` vs. `lean-miri`'s
`TyId 80` encoding boundary (both halves from program entry)**:
* From `initMachineState copyRawPtrDerefEntryBody []`, Stage-1 `stepMirFn`
  copies the provenance-carrying pointer `&raw const _1` across
  `copy_nonoverlapping::<*const u64>` into `_5`, dereferences `*_5`, is `TreeSafe`,
  and returns `42_u64`.
* From `initMachineState copyStage1RawPtrCastEntryBody []` and
  `miriEntryState copyStage1RawPtrCastEntryBody`, both machines run in lockstep
  (`AgreeReaches`) through the `8`-step entry block `bb0` and the `4` setup steps in
  `bb1` to `(s₄, m₄)` where `_4` and `_5` are initialized pointer-to-pointer values;
  Stage-1 `mirCallTree` is `TreeSafe` and returns `.ptr ⟨1, 0⟩ 8`, whereas `lean-miri`
  stops at `StepError.unsupported "pointee of TyId 80 is not encoded"`. -/
theorem w6_copy_nonoverlapping_rawPtr_tyId80_boundary :
    (TreeSafe (mirCallTree copyRawPtrDerefEntryBody []) ∧
      ∃ tr mem, ReachesRet (mirCallTree copyRawPtrDerefEntryBody []) tr
        (.normal (.scalar ⟨42, 8⟩, mem))) ∧
    (let b := copyStage1RawPtrCastEntryBody
     ∃ s₄ m₄,
       AgreeReaches b (annealMiriHooks b) (initMachineState b []) s₄ (miriEntryState b) m₄ ∧
       get? s₄.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
       get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
       TreeSafe (mirCallTree b []) ∧
       (∃ tr mem, ReachesRet (mirCallTree b []) tr
         (.normal (.ptr { allocId := 1, offsetBytes := 0 } 8, mem))) ∧
       (miriSystem (annealMiriHooks b)).ReachesOutcome (miriEntryState b)
         (.unsupported (.unsupported "pointee of TyId 80 is not encoded")) ∧
       ¬ (miriSystem (annealMiriHooks b)).Safe (miriEntryState b)) := by
  refine ⟨anneal_returns_of_bits (N := 12) (by kernel_rfl), ?_⟩
  let b := copyStage1RawPtrCastEntryBody
  obtain ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, hl4, hl5, hm₅⟩ :=
    copyStage1RawPtrCastEntry_trace
  obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
  have hpathA : AnnealPath b copyStage1RawPtrCastEntryPreAnneal s₄ :=
    .step .silent hs₁ (.step .silent hs₂ (.step .silent hs₃ (.step .silent hs₄ (.refl _))))
  have hpathM : MiriPath (annealMiriHooks b) copyStage1RawPtrCastEntryPreMiri m₄ :=
    .step hm₁ (frames_ne_of_step_ok_true hm₂)
      (.step hm₂ (frames_ne_of_step_ok_true hm₃)
        (.step hm₃ (frames_ne_of_step_ok_true hm₄)
          (.step hm₄ (frames_ne_of_eq_singleton htf₄) (.refl _))))
  let memA : Memory :=
    match runAnnealBounded b 14 (initMachineState b []) with
    | .returned _ m => m
    | _ => emptyMemory
  have hretA : runAnnealBounded b 14 (initMachineState b []) =
      .returned (.ptr { allocId := 1, offsetBytes := 0 } 8) memA := by kernel_rfl
  obtain ⟨hsafeA, ⟨trA, hrrA⟩, _⟩ := anneal_safe_of_runAnnealBounded_returned hretA
  have hfullM : MiriPath (annealMiriHooks b) (miriEntryState b) m₄ :=
    (MiriPath.of_runLoopFuel copyStage1RawPtrCastEntry_prefix_miri).trans hpathM
  have houtM := miri_outcome_of_path_error hfullM hm₅
  exact ⟨s₄, m₄,
    agreeReaches_of_prefix_paths copyStage1RawPtrCastEntry_prefix_anneal
      copyStage1RawPtrCastEntry_prefix_miri hpathA hpathM,
    hl4, hl5, hsafeA, ⟨trA, memA, hrrA⟩, houtM.1, houtM.2⟩

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
