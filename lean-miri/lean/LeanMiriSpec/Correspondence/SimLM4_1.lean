/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.CallLM4_1
import LeanMiriSpec.Correspondence.ProjLM2_2
import LeanMiriSpec.Correspondence.SimLM2_1

/-!
# Multi-Frame Terminator & `CallId` Protector Simulation (`LM-4.1`)

Proves the five core `LM-4.1` correspondence theorems (plus divergence lemmas)
between Anneal's `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` and
`lean-miri`'s `Miri.Interpreter.Step.step` under `MultiFrameStateRel`
(`CallStackStateRel`) and `StepRelMultiFrame` in the pointer-free scalar,
scalar-pair, unit, and array fragment (`ImmediateRel` / `MemPlaceRel`):

1. `step_terminator_unreachable_ub_simulation`: `TerminatorKind.unreachable`
   faults with undefined behavior in both machines at arbitrary stack depth.
2. `step_terminator_drop_noop_simulation` (and
   `canonical_drop_no_glue_preserves_local_divergence`):
   `TerminatorKind.drop ⟨localId, .nil⟩ target unwind` faults with UB on a
   `.dead` local and deinitializes a live immediate local while advancing the
   active frame's PC to `(target, 0)` at arbitrary stack depth (`annealEvalDropLM4_1`),
   whereas canonical `lean-miri`'s `ExecutionMachine.stepHooks.drop` with
   `dropGlue = none` performs a plain `ControlFlow.goToBlock target` that
   preserves the local's value. Projected drops `⟨localId, [.field i _]⟩` keep
   canonical no-glue behavior in the hooks (`step_terminator_drop_projected_simulation`
   for `.dead` and initialized scalar-pair roots;
   `step_terminator_drop_projected_uninit_divergence` for the residual Stage-1
   fault on an `.uninit` root).
3. `step_terminator_return_root_simulation`: `TerminatorKind.return_` from the
   root frame (`s.memory.callStack = []`) faults with UB on `.dead`/`.uninit` `_0`
   and produces the terminal `.retNormal retVal s.memory` outcome in Anneal and
   an empty call stack (`m'.stack.frames = #[]`) with `ImmediateRel` or
   `MemPlaceRel`-related return operand in `lean-miri` (covering ZST `()`,
   scalars, scalar pairs, and `.indirect` `_0`). Note on `hzst_init`: in
   optimized MIR where `RemoveZsts` strips `_0 = const ()` leaving a zero-sized
   `_0` as `.uninit`, Anneal's `Trusted` `TerminatorKind.return_`
   (`Terminators.lean:3005-3039`) faults with UB on `.uninit` regardless of size,
   whereas canonical `lean-miri` returns a ZST operand normally; the `hzst_init`
   hypothesis captures the agreeing initialized-ZST / non-ZST fragment.
4. `step_terminator_return_callee_simulation`: `TerminatorKind.return_` from a
   non-root callee frame (`s.memory.callStack = cf :: restStack`) copies `_0`
   (covering ZST `()` under `hzst_init`, scalars, scalar pairs, and `.indirect` `_0`)
   into the caller's `cf.destination` (supporting both `.immediate` and `.indirect`
   caller destination places), deallocates all live `.indirect` stack allocations
   belonging to the popped callee frame via `Stack.cleanupStackFrame`, releases
   the callee frame's `CallId` protectors via `Miri.TreeBorrows.GlobalState.endCall`
   on `annealPoppedFrameState s` in `m.machine.borrowTracker`
   (`BorrowTrackerStackRel`, leaving `rootPointerTags` untouched), and advances
   the caller frame to `(cf.returnTarget, 0)`.
5. `step_terminator_call_simulation`, `step_terminator_call_diverging_simulation`
   (and `step_terminator_call_unreachable_unchecked_ub_simulation`):
   `TerminatorKind.call` resolves the callee in `s.memory.callees`, evaluates
   arguments left-to-right (propagating `.dead`/`.uninit` UB and deinitializing
   `.move` locals), resolves both `.immediate` and `.indirect` caller destination
   places (`CallerDestinationRel`), pushes the callee frame via
   `Stack.pushStackFrameRaw` and `Stack.pushStackFrameDone` with `returnPlace`
   and `returnContinuation = .goto (some targetBb) unwind` (returning call,
   Stage-1 `pushCalleeFrame`) or `.goto none unwind` (diverging call, Stage-1
   `pushDivergingCalleeFrame` with `isDiverging = true`), and steps to
   `MultiFrameStateRel`-related states at depth `d + 1`; a diverging call to an
   unlinked unreachable call target faults with UB in both machines.
6. `unwindFromCallStack_miri_multiStep_simulation`,
   `step_terminator_unwindResume_multiFrame_simulation`, and
   `step_terminator_unwindTerminate_abort_vs_unsupported`: arbitrary-depth
   `UnwindAction.continue_` stuttering unwinding (1 Stage-1 step vs. `k` Miri
   `.unwinding` steps via `UnwindingStateRel` and `MiriUnwindSteps`, grounding
   `releaseCallProtectors k` and `popFrameBorrowTrackerAtDepth` across `.cleanup`,
   `.unreachable`, `.terminate`, and root `.panic` vs. UB), plus `UnwindTerminate`.
7. `step_terminator_assert_local_simulation` and
   `step_terminator_call_diverging_panic_vs_unlinked`: multi-frame `Assert`
   correspondence (`.dead`/`.uninit` condition UB, passing jump to `(target, 0)`,
   and failed `applyUnwindAction` vs. unlinked panic lang item) and diverging
   unlinked panic calls.
8. `step_terminator_call_fnDef_local_simulation`,
   `step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation`,
   `step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`,
   `step_terminator_call_indirect_fnPtr_move_simulation`,
   `step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence`, and
   `step_terminator_call_indirect_layoutCompat_fnPtr_divergence`: non-constant
   ZST `FnDef` local calls, `ReifyFnPointer` coercion assignments bridging
   `MultiFrameStateRel` to `IndirectFnPtrMovePre`, indirect `FnPtr` calls
   (dangling integer UB, non-zero offset / non-function `allocId` / ABI mismatch
   UB, and valid provenance-bearing `FnPtr` `.move` call pushing `calleeBody`
   into `MultiFrameStateRel`), and the Stage-1 `safetyCompatible .unsafe_ .safe`
   and `rigidTyEq` vs. canonical `lean-miri` `FnAbi` / `LayoutCompat`
   divergences.
9. `step_terminator_call_linked_panic_unwind_simulation`,
   `step_terminator_unwindTerminate_termination_abort_simulation`, and
   `step_terminator_assert_failed_directUnwind_simulation`: 2-step simulation
   when `"core::panicking::panic"` is linked in `s.memory.callees` under
   `annealStepHooksForState`, plus direct-unwind failed `Assert` (`unwindToBlock`)
   and `UnwindTerminate` (`TerminationInfo.abort`) simulation under
   `annealStepHooksWithDirectUnwind`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Multi-Frame `stepMirFn`, `Step.step`, and Stack Array Helpers -/

/-- Unfold `stepMirFn rootBody s` at arbitrary stack depth in terms of
`activeMirBody rootBody s`. -/
theorem stepMirFn_activeMirBody_eq
    (rootBody : CapturedMir) (s : MachineState)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) :
    stepMirFn rootBody s =
      let currentBody := activeMirBody rootBody s
      match get? currentBody.basicBlocks s.frame.blockIdx with
      | none => MirStepNode.fail .ub
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => evalStmt s stmt currentBody.localDecls currentBody.layouts
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminator s bb.terminator (some currentBody)
          else
            MirStepNode.fail .ub := by
  unfold stepMirFn activeMirBody
  simp +zetaHave only []
  cases hp : (s.memory.activeCallee.getD rootBody).phase with
  | runtimePostCleanup => rfl
  | runtimeOptimized => rfl
  | other p => exact False.elim (hphase p hp)

/-- Unfold `Miri.Interpreter.Step.step` under `annealStepHooksLM4_1` at a
terminator at arbitrary stack depth whenever `m.stack.frames.back? = some topFrame`. -/
theorem miri_step_at_terminator_multiFrame
    {currentBody : CapturedMir} {callees : List CapturedMir}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {fnPtrs : List FnPtrEntry}
    {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hback : m.stack.frames.back? = some topFrame)
    (hbody : topFrame.body = translateBody currentBody)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData}
    (hbb : get? currentBody.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs) () m =
      let res := Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooksLM4_1 currentBody callees poppedFrame fnPtrs) () (translateTerminator bb.terminator) m
      (res.1, res.2.map fun _ => true) := by
  unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt_none]
  rfl

theorem array_eq_of_toList_reverse_cons {α : Type _}
    {arr : Array α} {tf : α} {rest : List α}
    (h : arr.toList.reverse = tf :: rest) :
    arr = ⟨rest.reverse ++ [tf]⟩ := by
  apply Array.ext'
  have h' := congrArg List.reverse h
  simpa [List.reverse_reverse] using h'

@[simp]
theorem array_back?_append_singleton {α : Type _} (xs : List α) (tf : α) :
    (⟨xs ++ [tf]⟩ : Array α).back? = some tf := by
  unfold Array.back?
  simp

@[simp]
theorem array_pop_append_singleton {α : Type _} (xs : List α) (tf : α) :
    (⟨xs ++ [tf]⟩ : Array α).pop = ⟨xs⟩ := by
  apply Array.ext'
  simp

@[simp]
theorem array_set_last_append_singleton {α : Type _}
    (xs : List α) (tf tf' : α)
    (h : xs.length < (⟨xs ++ [tf]⟩ : Array α).size) :
    (⟨xs ++ [tf]⟩ : Array α).set xs.length tf' h = ⟨xs ++ [tf']⟩ := by
  apply Array.ext'
  simp

@[simp]
theorem array_toList_reverse_append_singleton {α : Type _} (rest : List α) (tf : α) :
    (⟨rest.reverse ++ [tf]⟩ : Array α).toList.reverse = tf :: rest := by
  simp

theorem array_push_append_singleton {α : Type _} (rest : List α) (tf newTf : α) :
    (⟨rest.reverse ++ [tf]⟩ : Array α).push newTf =
      ⟨(tf :: rest).reverse ++ [newTf]⟩ := by
  apply Array.ext'
  simp

theorem array_getElem?_append_singleton_of_lt {α : Type _}
    (xs : List α) (tf : α) {i : Nat} (hi : i < xs.length) :
    (⟨xs ++ [tf]⟩ : Array α)[i]? = (⟨xs⟩ : Array α)[i]? := by
  have hi_arr : i < (⟨xs⟩ : Array α).size := hi
  have hi_app : i < (⟨xs ++ [tf]⟩ : Array α).size := by simp; omega
  rw [Array.getElem?_eq_getElem hi_app, Array.getElem?_eq_getElem hi_arr]
  congr 1
  exact List.getElem_append_left hi

theorem array_getElem?_append_singleton_last {α : Type _}
    (xs : List α) (tf : α) :
    (⟨xs ++ [tf]⟩ : Array α)[xs.length]? = some tf := by
  have hlt : xs.length < (⟨xs ++ [tf]⟩ : Array α).size := by simp
  rw [Array.getElem?_eq_getElem hlt]
  simp

/-- Replacing only the top frame `tf` with `tf'` in `⟨rest.reverse ++ [tf]⟩`
preserves `MultiFrameAllocDisjoint` whenever `MemoryAllocDisjoint tf'` holds and
every `.indirect` local in `tf'` was already an `.indirect` local with the same
`MemPlace` in `tf`. -/
theorem MultiFrameAllocDisjoint.replace_top
    {rest : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MultiFrameAllocDisjoint ⟨rest.reverse ++ [tf]⟩)
    (hd_tf' : MemoryAllocDisjoint tf')
    (hsub : ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout),
      tf'.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
      ∃ lay₀, tf.locals[i]? = some { value := .live (.indirect mp), layout := lay₀ }) :
    MultiFrameAllocDisjoint ⟨rest.reverse ++ [tf']⟩ where
  intra_frame mf hmf := by
    simp only [List.mem_append, List.mem_singleton] at hmf
    rcases hmf with hmem | rfl
    · apply hdisj.intra_frame mf
      simp [hmem]
    · exact hd_tf'
  inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj := by
    have hsz₁ : f₁ < rest.reverse.length + 1 := by
      have ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hf₁
      simpa using hlt
    have hsz₂ : f₂ < rest.reverse.length + 1 := by
      have ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hf₂
      simpa using hlt
    by_cases h1 : f₁ = rest.reverse.length
    · subst h1
      rw [array_getElem?_append_singleton_last] at hf₁
      injection hf₁ with hmf₁; subst hmf₁
      have hlt₂ : f₂ < rest.reverse.length := by omega
      rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
      obtain ⟨lay₀, hi₀⟩ := hsub i mp₁ lay₁ hi
      exact hdisj.inter_frame rest.reverse.length f₂ i j tf mf₂ mp₁ mp₂ lay₀ lay₂ hne
        (array_getElem?_append_singleton_last _ _)
        (by rw [array_getElem?_append_singleton_of_lt _ _ hlt₂]; exact hf₂)
        hi₀ hj
    · have hlt₁ : f₁ < rest.reverse.length := by omega
      rw [array_getElem?_append_singleton_of_lt _ _ hlt₁] at hf₁
      by_cases h2 : f₂ = rest.reverse.length
      · subst h2
        rw [array_getElem?_append_singleton_last] at hf₂
        injection hf₂ with hmf₂; subst hmf₂
        obtain ⟨lay₀, hj₀⟩ := hsub j mp₂ lay₂ hj
        exact hdisj.inter_frame f₁ rest.reverse.length i j mf₁ tf mp₁ mp₂ lay₁ lay₀ hne
          (by rw [array_getElem?_append_singleton_of_lt _ _ hlt₁]; exact hf₁)
          (array_getElem?_append_singleton_last _ _)
          hi hj₀
      · have hlt₂ : f₂ < rest.reverse.length := by omega
        rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
        exact hdisj.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne
          (by rw [array_getElem?_append_singleton_of_lt _ _ hlt₁]; exact hf₁)
          (by rw [array_getElem?_append_singleton_of_lt _ _ hlt₂]; exact hf₂)
          hi hj

/-- Updating the location of the top frame in `CallerStackLinksRel` preserves
`CallerStackLinksRel` with the updated Anneal frame `{ curAf with blockIdx := target, stmtIdx := 0 }`
and Miri frame `{ topFrame with location := .mir ⟨target, 0⟩ }`. -/
theorem CallerStackLinksRel.update_top_frame
    {rootBody : CapturedMir} {mach : AnnealMachine}
    {curBody : CapturedMir} {curAf curAf' : StackFrame}
    {cs : List SavedCallerFrame} {prots : List Nat}
    {topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    (hlinks : CallerStackLinksRel rootBody mach curBody curAf cs prots (topFrame :: restMfs))
    (hrc : topFrame'.returnContinuation = topFrame.returnContinuation)
    (hrp : topFrame'.returnPlace = topFrame.returnPlace)
    (hid : topFrame'.localsIdentity = topFrame.localsIdentity)
    (hfr' : FrameRel curBody mach curAf' topFrame')
    (hret0 :
      ∀ (mp0 : Miri.Interpreter.MemPlace AnnealProv)
        (lay0 : Option Miri.Interpreter.LocalLayout),
        topFrame'.locals[0]? = some { value := .live (.indirect mp0), layout := lay0 } →
        (∃ lay0', topFrame.locals[0]? = some { value := .live (.indirect mp0), layout := lay0' }) ∧
        (get? curAf'.locals 0 = get? curAf.locals 0 ∨
          ∃ sc0, get? curAf'.locals 0 = some (.init (.scalar sc0)))) :
    CallerStackLinksRel rootBody mach curBody curAf' cs prots (topFrame' :: restMfs) := by
  cases hlinks with
  | root _ _ _ hretCont hretPlace _ =>
    refine .root curAf' topFrame' prots (by rw [hrc]; exact hretCont) ?_ hfr'
    obtain ⟨retLay, hrp₀⟩ := hretPlace
    exact ⟨retLay, by rw [hrp, hid]; exact hrp₀⟩
  | cons _ _ cf cs' curProts callerProts _ callerMf restMfs' hretCont hdest _ hretWf hcp hdisj hrest =>
    refine .cons curBody curAf' cf cs' curProts callerProts topFrame' callerMf restMfs'
      (by rw [hrc]; exact hretCont)
      (by rw [hrp]; exact hdest)
      hfr' ?_ hcp hdisj hrest
    intro mp0 lay0 decl0 destDecl destIdx h0 hdecl0 hcf hdecl_d
    obtain ⟨⟨lay0', h0'⟩, haf0⟩ := hret0 mp0 lay0 h0
    obtain ⟨hnodup, hprim, hlay, hinit, huninit⟩ :=
      hretWf mp0 lay0' decl0 destDecl destIdx h0' hdecl0 hcf hdecl_d
    refine ⟨hnodup, hprim, hlay, ?_, ?_⟩
    · intro retVal hval
      rcases haf0 with heq | ⟨sc0, hsc0⟩
      · rw [heq] at hval
        exact hinit retVal hval
      · rw [hsc0] at hval
        injection hval with hval'
        injection hval' with hval''
        exact ⟨sc0, hval''.symm⟩
    · intro hun
      rcases haf0 with heq | ⟨sc0, hsc0⟩
      · rw [heq] at hun
        exact huninit hun
      · rw [hsc0] at hun
        cases hun

/-! ## 2. `Terminator.Unreachable` and `Terminator.Drop` Simulation at Arbitrary Stack Depth -/

/-- **Theorem 1 (`step_terminator_unreachable_ub_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.unreachable` faults with undefined behavior in both Anneal
(`stepMirFn rootBody s = MirStepNode.fail .ub`) and `lean-miri`
(`Step.step ... = (m, .error (.undefinedBehavior "Unreachable"))`). -/
theorem step_terminator_unreachable_ub_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .unreachable)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
      rw [hterm]
      dsimp only [translateTerminatorKind, Except.map, Id.run]
      exact StepRelMultiFrame.ub _ _

/-- **Theorem 2 (`step_terminator_drop_noop_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.drop ⟨localId, .nil⟩ target unwind` on a declared immediate local
`localId` in `activeMirBody rootBody s`:
* faults with undefined behavior in both machines if `localId` is `.dead`;
* deinitializes `localId` to `.uninit` / `.live (.immediate .uninit)` and advances
  the active top frame's location to `(target, 0)` in both machines if `localId`
  is live (`annealEvalDropLM4_1`), preserving `MultiFrameStateRel`.
  (Compare `canonical_drop_no_glue_preserves_local_divergence` for canonical
  `lean-miri`'s `Drop` with `dropGlue = none`, which jumps via `ControlFlow.goToBlock`
  without deinitializing `localId`.) -/
theorem step_terminator_drop_noop_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {localId : Local} {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {decl : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .drop ⟨localId, .nil⟩ target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls localId = some decl)
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf localId)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hget := frame_getLocal_of_getElem? topFrame localId mls hmls
      have himm' := himm topFrame hback mls hmls
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
        annealTerminatorHooksLM4_1 annealEvalDropLM4_1
      rw [hterm]
      dsimp only [translateTerminatorKind, translatePlace, List.map, List.toArray,
        Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Miri.Interpreter.Stack.currentFrame?, Id.run]
      rw [hslot, hback]
      dsimp only
      rw [hget]
      cases hloc with
      | dead cachedLayout _ =>
        dsimp only [Except.map]
        exact StepRelMultiFrame.ub _ _
      | indirect slot0 mp cachedLayout hlay hne_dead hmemRel0 =>
        exact False.elim (himm' mp rfl)
      | immediate _ imm cachedLayout hcache hval =>
        have ha_drop :
            evalTerminator s bb.terminator (some (activeMirBody rootBody s)) =
              MirStepNode.step
                { s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals.set localId .uninit } } := by
          unfold evalTerminator
          rw [hterm]
          dsimp only
          rw [hslot, set?_eq_some_set hlt_af]
          rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
        have hrep_mf :=
          frame_replaceLocalValue_of_lt topFrame localId hlt_mf (.live (.immediate .uninit))
        rw [hrep_mf]
        dsimp only
        have hidx_lt : m.stack.frames.size - 1 < m.stack.frames.size := by
          rw [harr]; simp
        simp +zetaHave only [hidx_lt, ↓reduceDIte, Except.map, pure, Pure.pure]
        let topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
          { topFrame with
            locals := topFrame.locals.set localId
              { topFrame.locals[localId]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf
            location := .mir ⟨target, 0⟩ }
        have hset_frames :
            m.stack.frames.set (m.stack.frames.size - 1) topFrame' hidx_lt =
              ⟨restMfs.reverse ++ [topFrame']⟩ := by
          apply Array.ext'
          simp [harr]
        rw [hset_frames]
        have ha_drop' := ha_drop
        unfold evalTerminator at ha_drop'
        rw [hterm] at ha_drop'
        dsimp only at ha_drop'
        rw [hslot] at ha_drop'
        rw [ha_drop']
        apply StepRelMultiFrame.step
        have hnew_loc :
            LocalRel m.machine decl (activeMirBody rootBody s).layouts .uninit
              { topFrame.locals[localId]'hlt_mf with value := .live (.immediate .uninit) } := by
          rw [hmls_eq]
          exact .immediate .uninit .uninit cachedLayout hcache (Or.inl ⟨rfl, rfl⟩)
        have hfr₁ := hframe.update_local hdecl .uninit (.live (.immediate .uninit)) hnew_loc
        have hfr' :
            FrameRel (activeMirBody rootBody s) m.machine
              { blockIdx := target, stmtIdx := 0, locals := s.frame.locals.set localId .uninit }
              topFrame' :=
          ⟨hfr₁.body_eq, rfl, hfr₁.af_locals_len, hfr₁.mf_locals_size, hfr₁.locals_rel⟩
        have hlinks' :
            CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s)
              { blockIdx := target, stmtIdx := 0, locals := s.frame.locals.set localId .uninit }
              s.memory.callStack s.memory.activeProtectors
              (topFrame' :: restMfs) := by
          refine hlinks.update_top_frame rfl rfl rfl hfr' ?_
          intro mp0 lay0 h0
          dsimp only [topFrame'] at h0
          by_cases hloc0_eq : localId = 0
          · subst hloc0_eq
            rw [Array.getElem?_set_self] at h0
            cases h0
          · rw [Array.getElem?_set_ne _ hloc0_eq] at h0
            refine ⟨⟨lay0, h0⟩, Or.inl ?_⟩
            dsimp only
            rw [get?_eq_getElem?, get?_eq_getElem?, List.getElem?_set_ne hloc0_eq]
        have hdisj_tf' : MemoryAllocDisjoint topFrame' := by
          have hd_tf : MemoryAllocDisjoint topFrame := by
            apply hdisj.intra_frame topFrame
            rw [harr]; simp
          apply MemoryAllocDisjoint.mono_immediate hd_tf
          intro k
          by_cases hk : localId = k
          · subst hk
            right
            exact ⟨.uninit, (topFrame.locals[localId]'hlt_mf).layout, by
              dsimp only [topFrame']; rw [Array.getElem?_set_self]⟩
          · left
            dsimp only [topFrame']
            rw [Array.getElem?_set_ne _ hk]
        have hdisj' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [topFrame']⟩ := by
          rw [harr] at hdisj
          apply hdisj.replace_top hdisj_tf'
          intro i mp lay hi
          dsimp only [topFrame'] at hi
          by_cases hi_loc : localId = i
          · subst hi_loc
            rw [Array.getElem?_set_self] at hi
            cases hi
          · rw [Array.getElem?_set_ne _ hi_loc] at hi
            exact ⟨lay, hi⟩
        refine .mk topFrame' (by simp) hcal_root hcal_nonroot
          (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody] using hlinks'.toForall2)
          (by simpa [activeMirBody] using hlinks')
          hdisj' htb hvalid hcid_pos hcid_act hcid_bor hbt

/-- **Divergence Lemma (`H3`, `canonical_drop_no_glue_preserves_local_divergence`)**:
When dropping an unprojected live immediate local `localId` with value
`.live (.immediate (.scalar msc))`:
1. Canonical `lean-miri`'s `Drop` transition with `dropGlue = none`
   (`ExecutionMachine.lean:327-335`, `ControlFlow.goToBlock target m`) advances
   the top frame's location to `.mir ⟨target, 0⟩` and preserves the local's
   value (`gf.locals[localId]? = some ⟨.live (.immediate (.scalar msc)), lay⟩`);
2. Anneal's `Trusted` `TerminatorKind.drop` (`Terminators.lean:3041-3066`, mirrored
   by `annealEvalDropLM4_1`) deinitializes `localId` to `.uninit` /
   `.live (.immediate .uninit)`. -/
theorem canonical_drop_no_glue_preserves_local_divergence
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {localId : Local} {target : Miri.MIR.BasicBlockId}
    {unwind : Miri.MIR.UnwindAction}
    {msc : Miri.Memory.Scalar AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : localId < topFrame.locals.size)
    (hmls : topFrame.locals[localId]'hlt = ⟨.live (.immediate (.scalar msc)), lay⟩) :
    let goRes := Miri.Interpreter.ControlFlow.goToBlock target m
    let dropRes := annealEvalDropLM4_1 ⟨localId, #[]⟩ target unwind m
    goRes.2 = .ok () ∧
    dropRes.2 = .ok () ∧
    (∃ gf, goRes.1.stack.frames.back? = some gf ∧
      gf.location = .mir ⟨target, 0⟩ ∧
      gf.locals[localId]? = some ⟨.live (.immediate (.scalar msc)), lay⟩) ∧
    (∃ df, dropRes.1.stack.frames.back? = some df ∧
      df.location = .mir ⟨target, 0⟩ ∧
      df.locals[localId]? = some ⟨.live (.immediate .uninit), lay⟩) := by
  have hcurr : m.stack.currentFrame? = some topFrame := by
    unfold Miri.Interpreter.Stack.currentFrame?
    rw [hframes]
    exact array_back?_append_singleton restMfs.reverse topFrame
  have hget : topFrame.getLocal localId = .ok ⟨.live (.immediate (.scalar msc)), lay⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, hmls, pure, Except.pure]
  have hrep := frame_replaceLocalValue_of_lt topFrame localId hlt (.live (.immediate .uninit))
  have hidx_lt : m.stack.frames.size - 1 < m.stack.frames.size := by
    rw [hframes]; simp
  have hpush_go :
      m.stack.frames.pop.push { topFrame with location := .mir ⟨target, 0⟩ } =
        ⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨target, 0⟩ }]⟩ := by
    apply Array.ext'
    simp [hframes]
  let df : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { topFrame with
      locals := topFrame.locals.set localId
        { topFrame.locals[localId]'hlt with value := .live (.immediate .uninit) } hlt
      location := .mir ⟨target, 0⟩ }
  have hset_drop :
      m.stack.frames.set (m.stack.frames.size - 1) df hidx_lt =
        ⟨restMfs.reverse ++ [df]⟩ := by
    apply Array.ext'
    simp [hframes]
  dsimp only [Miri.Interpreter.ControlFlow.goToBlock, Miri.Interpreter.ControlFlow.setLocation,
    annealEvalDropLM4_1, Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hcurr]
  dsimp only []
  rw [hpush_go, hget, hrep]
  dsimp only []
  simp +zetaHave only [hidx_lt, ↓reduceDIte]
  rw [hset_drop]
  refine ⟨trivial, rfl,
    ⟨{ topFrame with location := .mir ⟨target, 0⟩ },
      array_back?_append_singleton restMfs.reverse _, rfl, ?_⟩,
    ⟨df, array_back?_append_singleton restMfs.reverse df, rfl, ?_⟩⟩
  · dsimp only
    rw [Array.getElem?_eq_getElem hlt, hmls]
  · dsimp only [df]
    rw [Array.getElem?_set_self, hmls]

/-- **Theorem 2b (`step_terminator_drop_projected_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing a
projected `TerminatorKind.drop ⟨localId, .field fieldIdx :: .nil⟩ target unwind`
(`fieldIdx = 0 ∨ fieldIdx = 1`) on a declared immediate local `localId` whose
Stage-1 slot is either `.dead` or an initialized 2-field scalar aggregate
`.init (.aggregate 0 [.scalar sc₁, .scalar sc₂])` (`hroot`):
* faults with undefined behavior in both machines if `localId` is `.dead`
  (Stage-1 `Terminators.lean:3044`; Miri's dead-local place evaluation);
* when `localId` holds the 2-field aggregate (necessarily related by
  `ImmediateRel.scalarPair` to a `lean-miri` `.scalarPair` immediate), both
  Stage-1 `Trusted` (`Terminators.lean:3055-3066`, `readProjectedValue`) and
  `lean-miri` (`annealEvalDropLM4_1` / `ControlFlow.goToBlock target m`, matching
  canonical `ExecutionMachine.stepHooks.drop` at `ExecutionMachine.lean:327-335`)
  advance `(blockIdx, stmtIdx)` to `(target, 0)` without deinitializing
  `localId`, preserving `MultiFrameStateRel`.

The remaining `.uninit` root case is a genuine Stage-1 divergence (Stage-1
faults, canonical `lean-miri` jumps), certified separately by
`step_terminator_drop_projected_uninit_divergence`. -/
theorem step_terminator_drop_projected_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {localId : Local} {fieldIdx : Nat} {fieldTy : Ty}
    {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {decl : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .drop ⟨localId, .field fieldIdx fieldTy :: .nil⟩ target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls localId = some decl)
    (hfield : fieldIdx = 0 ∨ fieldIdx = 1)
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf localId)
    (hroot :
      get? s.frame.locals localId = some .dead ∨
        ∃ sc₁ sc₂,
          get? s.frame.locals localId = some (.init (.aggregate 0 [.scalar sc₁, .scalar sc₂])))
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hget := frame_getLocal_of_getElem? topFrame localId mls hmls
      have himm' := himm topFrame hback mls hmls
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
        annealTerminatorHooksLM4_1 annealEvalDropLM4_1
      rw [hterm]
      have hproj_ne :
          (!(translatePlace ⟨localId, .field fieldIdx fieldTy :: .nil⟩).projection.isEmpty) = true :=
        rfl
      dsimp only [translateTerminatorKind, Id.run]
      rw [hslot, hproj_ne]
      dsimp only [↓reduceIte, translatePlace, translateProjectionElem, List.map, List.toArray,
        Miri.Interpreter.Stack.currentFrame?]
      rw [hback]
      dsimp only
      rw [hget]
      cases hloc with
      | dead cachedLayout _ =>
        dsimp only [Except.map]
        exact StepRelMultiFrame.ub _ _
      | indirect slot0 mp cachedLayout hlay hne_dead hmemRel0 =>
        exact False.elim (himm' mp rfl)
      | immediate _ imm cachedLayout hcache hval =>
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · exfalso
          rcases hroot with hdead | ⟨_, _, hpair⟩
          · rw [hslot] at hdead; cases hdead
          · rw [hslot] at hpair; cases hpair
        · have hv : ∃ sc₁ sc₂, v = .aggregate 0 [.scalar sc₁, .scalar sc₂] := by
            rcases hroot with hdead | ⟨sc₁, sc₂, hpair⟩
            · rw [hslot] at hdead; cases hdead
            · rw [hslot] at hpair
              injection hpair with hpair'
              injection hpair' with hv
              exact ⟨sc₁, sc₂, hv⟩
          obtain ⟨sc₁, sc₂, rfl⟩ := hv
          cases himmRel with
          | scalarPair _ _ msc₁ msc₂ _ _ _ _ =>
          have hpush_go :
              m.stack.frames.pop.push { topFrame with location := .mir ⟨target, 0⟩ } =
                ⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨target, 0⟩ }]⟩ := by
            apply Array.ext'
            simp [harr]
          let topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { topFrame with location := .mir ⟨target, 0⟩ }
          have hfr' :
              FrameRel (activeMirBody rootBody s) m.machine
                { s.frame with blockIdx := target, stmtIdx := 0 }
                topFrame' :=
            ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
          have hlinks' :
              CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s)
                { s.frame with blockIdx := target, stmtIdx := 0 }
                s.memory.callStack s.memory.activeProtectors
                (topFrame' :: restMfs) :=
            hlinks.update_top_frame rfl rfl rfl hfr' (fun mp0 lay0 h0 => ⟨⟨lay0, h0⟩, Or.inl rfl⟩)
          have hdisj' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [topFrame']⟩ := by
            rw [harr] at hdisj
            refine hdisj.replace_top ?_ (fun _ _ lay hi => ⟨lay, hi⟩)
            exact hdisj.intra_frame topFrame (by simp)
          rcases hfield with rfl | rfl <;>
          · dsimp only [readProjectedValue, get?, Miri.Interpreter.ControlFlow.goToBlock,
              Miri.Interpreter.ControlFlow.setLocation, Miri.Interpreter.Stack.currentFrame?]
            rw [hback]
            dsimp only [Except.map, pure, Pure.pure]
            rw [hpush_go]
            apply StepRelMultiFrame.step
            exact .mk topFrame' (array_back?_append_singleton restMfs.reverse topFrame') hcal_root hcal_nonroot
              (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody] using hlinks'.toForall2)
              (by simpa [activeMirBody] using hlinks')
              hdisj' htb hvalid hcid_pos hcid_act hcid_bor hbt

/-- **Divergence (`step_terminator_drop_projected_uninit_divergence`)**: on a
projected `TerminatorKind.drop ⟨localId, .field fieldIdx :: .nil⟩ target unwind`
(`fieldIdx = 0 ∨ fieldIdx = 1`) whose immediate root local `localId` is
uninitialized (`get? s.frame.locals localId = some .uninit`) under
`MultiFrameStateRel rootBody s m`:
1. Stage-1 `Trusted` faults (`stepMirFn rootBody s = .fail .ub`), because a
   projected drop requires an `.init` root slot (`Terminators.lean:3055-3066`);
2. `lean-miri` (`annealEvalDropLM4_1`, keeping canonical
   `ExecutionMachine.stepHooks.drop`'s no-glue behavior: place evaluation then
   `ControlFlow.goToBlock`, which never reads the dropped value) steps normally
   (`.ok true`) to a state whose top frame sits at `(target, 0)` and still holds
   the uninitialized `localId`. -/
theorem step_terminator_drop_projected_uninit_divergence
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {localId : Local} {fieldIdx : Nat} {fieldTy : Ty}
    {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {decl : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .drop ⟨localId, .field fieldIdx fieldTy :: .nil⟩ target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls localId = some decl)
    (hfield : fieldIdx = 0 ∨ fieldIdx = 1)
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf localId)
    (huninit : get? s.frame.locals localId = some .uninit)
    (fnPtrs : List FnPtrEntry := .nil) :
    stepMirFn rootBody s = .fail .ub ∧
    ∃ m' tf',
      Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m =
        (m', .ok true) ∧
      m'.stack.frames.back? = some tf' ∧
      tf'.location = .mir ⟨target, 0⟩ ∧
      ∃ lay, tf'.locals[localId]? = some ⟨.live (.immediate .uninit), lay⟩ := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hslot_eq : slot = .uninit := Option.some.inj (hslot.symm.trans huninit)
      subst hslot_eq
      have himm' := himm topFrame hback mls hmls
      have hmls_uninit :
          ∃ lay, topFrame.locals[localId]'hlt_mf = ⟨.live (.immediate .uninit), lay⟩ := by
        cases hloc with
        | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
        | immediate _ imm cachedLayout _ hval =>
          rcases hval with ⟨_, rfl⟩ | ⟨v, hv, _⟩
          · exact ⟨cachedLayout, hmls_eq⟩
          · cases hv
      obtain ⟨lay, hmls_u⟩ := hmls_uninit
      have hget : topFrame.getLocal localId = .ok ⟨.live (.immediate .uninit), lay⟩ := by
        unfold Miri.Interpreter.Frame.getLocal
        simp [hlt_mf, hmls_u, pure, Except.pure]
      refine ⟨?_, ?_⟩
      · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm]
        dsimp only
        rw [huninit]
      · have hpush_go :
            m.stack.frames.pop.push { topFrame with location := .mir ⟨target, 0⟩ } =
              ⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨target, 0⟩ }]⟩ := by
          apply Array.ext'
          simp [harr]
        have hcurr : m.stack.currentFrame? = some topFrame := hback
        have hdrop :
            annealEvalDropLM4_1 (translatePlace ⟨localId, .field fieldIdx fieldTy :: .nil⟩) target
                (translateUnwindAction unwind) m =
              ({ m with stack := ⟨⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨target, 0⟩ }]⟩⟩ },
               .ok ()) := by
          have hproj_ne :
              (!(translatePlace ⟨localId, .field fieldIdx fieldTy :: .nil⟩).projection.isEmpty) = true :=
            rfl
          have hgo :
              annealEvalDropLM4_1 (translatePlace ⟨localId, .field fieldIdx fieldTy :: .nil⟩) target
                  (translateUnwindAction unwind) m =
                Miri.Interpreter.ControlFlow.goToBlock target m := by
            unfold annealEvalDropLM4_1
            simp only [hproj_ne, ↓reduceIte]
            rw [hcurr]
            dsimp only
            have hloc_id :
                (translatePlace ⟨localId, .field fieldIdx fieldTy :: .nil⟩).localId = localId := rfl
            rw [hloc_id, hget]
            rcases hfield with rfl | rfl <;> rfl
          rw [hgo]
          unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
          rw [hcurr]
          dsimp only
          rw [hpush_go]
        refine ⟨{ m with stack := ⟨⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨target, 0⟩ }]⟩⟩ },
          { topFrame with location := .mir ⟨target, 0⟩ }, ?_,
          array_back?_append_singleton restMfs.reverse _, rfl, lay, ?_⟩
        · rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
          unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
            annealTerminatorHooksLM4_1
          rw [hterm]
          dsimp only [translateTerminatorKind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Id.run]
          rw [hdrop]
          rfl
        · dsimp only
          rw [Array.getElem?_eq_getElem hlt_mf, hmls_u]

/-- **Theorem 2c (`step_terminator_drop_canonical_no_glue_step_divergence`)**:
Bi-side step-level divergence between Stage-1 `Trusted` `stepMirFn` (mirrored by
`annealStepHooksLM4_1`) and canonical `lean-miri`'s no-drop-glue `Drop` step
(`ExecutionMachine.lean:327-335`, where `drop` delegates to `ControlFlow.goToBlock target`)
on `TerminatorKind.drop ⟨localId, .nil⟩ target unwind` when `localId` holds a live
immediate scalar `sc` (`msc`):
1. `stepMirFn rootBody s` steps to `s'` at `(target, 0)` and deinitializes
   `localId` (`get? s'.frame.locals localId = some .uninit`);
2. `Step.step (annealStepHooksLM4_1 ...) () m` steps in lockstep to `(m', .ok true)`
   with `localId` deinitialized to `.live (.immediate .uninit)`;
3. Canonical no-glue `Step.step` (`drop := fun _ _ tgt _ st => ControlFlow.goToBlock tgt st`)
   steps to `(m_canon, .ok true)` at `(target, 0)` while leaving `localId`
   initialized to `.live (.immediate (.scalar msc)) ≠ .live (.immediate .uninit)`. -/
theorem step_terminator_drop_canonical_no_glue_step_divergence
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {localId : Local} {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {decl : LocalDecl} {sc : MirAst.ScalarInt}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .drop ⟨localId, .nil⟩ target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls localId = some decl)
    (hslot_sc : get? s.frame.locals localId = some (.init (.scalar sc)))
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf localId) :
    let curBody := activeMirBody rootBody s
    let canonHooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
        AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
      { annealStepHooksLM4_1 curBody s.memory.callees (annealPoppedFrameState s) with
        terminator := fun choice term state =>
          Miri.Interpreter.ControlFlow.evalTerminator
            { annealTerminatorHooksLM4_1 curBody s.memory.callees (annealPoppedFrameState s) with
              drop := fun _ _ tgt _ st => Miri.Interpreter.ControlFlow.goToBlock tgt st }
            choice term state }
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 curBody s.memory.callees (annealPoppedFrameState s)) () m) ∧
    (∃ s',
      stepMirFn rootBody s = .step s' ∧
      get? s'.frame.locals localId = some .uninit) ∧
    (∃ m_canon gf msc lay,
      Miri.Interpreter.Step.step canonHooks () m = (m_canon, .ok true) ∧
      m_canon.stack.frames.back? = some gf ∧
      gf.location = .mir ⟨target, 0⟩ ∧
      gf.locals[localId]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), lay⟩) := by
  have hsim :=
    step_terminator_drop_noop_simulation hstate hphase hbb hstmt_none hstmt_len hterm hdecl himm
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hslot_eq : slot = .init (.scalar sc) := Option.some.inj (hslot.symm.trans hslot_sc)
      subst hslot_eq
      have himm' := himm topFrame hback mls hmls
      cases hloc with
      | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
      | immediate _ imm cachedLayout _ hval =>
        rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
        · cases h
        · injection hv with hv_eq; subst hv_eq
          cases himmRel with
          | scalar _ msc _ _ _ _ =>
            refine ⟨hsim, ?_, ?_⟩
            · refine ⟨{ s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals.set localId .uninit } }, ?_, ?_⟩
              · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
                have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
                simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
                unfold evalTerminator
                rw [hterm]
                dsimp only
                rw [hslot_sc, set?_eq_some_set hlt_af]
              · dsimp only
                rw [get?_eq_getElem?, List.getElem?_set_self hlt_af]
            · have hmls' : topFrame.locals[localId]'hlt_mf =
                  ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cachedLayout⟩ :=
                hmls_eq
              obtain ⟨hgo_ok, _, ⟨gf, hgf_back, hgf_loc, hgf_local⟩, _⟩ :=
                canonical_drop_no_glue_preserves_local_divergence harr hlt_mf hmls'
                  (target := target) (unwind := translateUnwindAction unwind)
              refine ⟨(Miri.Interpreter.ControlFlow.goToBlock target m).1, gf, msc, cachedLayout, ?_,
                hgf_back, hgf_loc, hgf_local⟩
              unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?
              rw [hback]
              dsimp only
              rw [hframe.location_eq, hframe.body_eq]
              dsimp only
              rw [translateBody_basicBlocks_getElem?, hbb]
              dsimp only [Option.map]
              rw [translateBasicBlockData_statements_getElem?, hstmt_none]
              dsimp only [Option.map, translateBasicBlockData, annealStepHooksLM4_1, annealStepHooks]
              unfold Miri.Interpreter.ControlFlow.evalTerminator translateTerminator
              rw [hterm]
              dsimp only [translateTerminatorKind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                Id.run]
              have hgo_pair :
                  Miri.Interpreter.ControlFlow.goToBlock target m =
                    ((Miri.Interpreter.ControlFlow.goToBlock target m).1, .ok ()) :=
                Prod.ext rfl hgo_ok
              rw [hgo_pair]
              rfl

/-! ## 3. Root-Frame `Terminator.Return` Simulation (`step_terminator_return_root_simulation`) -/

theorem annealPopFrameLM4_1_singleton
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame]) :
    annealPopFrameLM4_1 poppedFrame m = ({ m with stack := ⟨#[]⟩ }, .ok topFrame) := by
  unfold annealPopFrameLM4_1 Miri.Interpreter.Stack.popFrame
  rw [hframes]
  rfl

theorem annealControlHooks_returnOperand_dead_back
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hback : m.stack.frames.back? = some topFrame)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.dead, lay⟩) :
    (annealControlHooksLM4_1 localDecls layouts poppedFrame).returnOperand () m =
      (m, .error (.undefinedBehavior "return with uninitialized or dead _0")) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1 Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_uninit_back
    {body : CapturedMir}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {decl0 : LocalDecl}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {lay : Option Miri.Interpreter.LocalLayout}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    (hback : m.stack.frames.back? = some topFrame)
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate .uninit), lay⟩)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hsz0 : (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO) :
    (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m =
      (m, .error (.undefinedBehavior "return with uninitialized or dead _0")) := by
  have hbeq : ((translateTy decl0.ty body.layouts).layout.size == Miri.ABI.Size.ZERO) = false :=
    beq_false_of_ne hsz0
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1
    lookupLocalDeclLayout Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0, hdecl0]
  dsimp only
  rw [hbeq]
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  rw [hcleanup]
  rfl

theorem annealControlHooks_returnOperand_cleanup_live_back
    {body : CapturedMir}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {decl0 : LocalDecl}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    (hback : m.stack.frames.back? = some topFrame)
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live op, lay⟩)
    (hdecl0 : get? body.localDecls 0 = some decl0) :
    (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m =
      (m, .ok op) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1
    lookupLocalDeclLayout Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]
  dsimp only
  rcases op with imm | mp
  · cases imm with
    | scalar _ => rfl
    | scalarPair _ _ => rfl
    | uninit =>
      dsimp only
      rw [hdecl0]
      dsimp only
      by_cases hsz : ((translateTy decl0.ty body.layouts).layout.size == Miri.ABI.Size.ZERO) = true
      · rw [hsz]; rfl
      · have hsz_f : ((translateTy decl0.ty body.layouts).layout.size == Miri.ABI.Size.ZERO) = false :=
          Bool.eq_false_iff.mpr hsz
        rw [hsz_f]
        rw [hloc, hbody]
        dsimp only
        rw [translateBody_basicBlocks_getElem?, hbb]
        dsimp only [Option.map, translateBasicBlockData]
        rw [hcleanup]
        rfl
  · rfl

theorem annealControlHooks_returnOperand_zst_unit_back
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {decl0 : LocalDecl}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hback : m.stack.frames.back? = some topFrame)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate .uninit), lay⟩)
    (hdecl0 : get? localDecls 0 = some decl0)
    (hzero : (translateTy decl0.ty layouts).layout.size = Miri.ABI.Size.ZERO) :
    (annealControlHooksLM4_1 localDecls layouts poppedFrame).returnOperand () m =
      (m, .ok (.immediate .uninit)) := by
  have hbeq : ((translateTy decl0.ty layouts).layout.size == Miri.ABI.Size.ZERO) = true :=
    beq_iff_eq.mpr hzero
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1
    lookupLocalDeclLayout Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0, hdecl0]
  dsimp only
  rw [hbeq]
  rfl

theorem annealControlHooks_returnOperand_scalar_back
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {msc : Miri.Memory.Scalar AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (hback : m.stack.frames.back? = some topFrame)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate (.scalar msc)), lay⟩) :
    (annealControlHooksLM4_1 localDecls layouts poppedFrame).returnOperand () m =
      (m, .ok (.immediate (.scalar msc))) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1 Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_indirect_back
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (hback : m.stack.frames.back? = some topFrame)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.indirect mp), lay⟩) :
    (annealControlHooksLM4_1 localDecls layouts poppedFrame).returnOperand () m =
      (m, .ok (.indirect mp)) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1 Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_scalarPair_back
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {msc₁ msc₂ : Miri.Memory.Scalar AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (hback : m.stack.frames.back? = some topFrame)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate (.scalarPair msc₁ msc₂)), lay⟩) :
    (annealControlHooksLM4_1 localDecls layouts poppedFrame).returnOperand () m =
      (m, .ok (.immediate (.scalarPair msc₁ msc₂))) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1 Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]

theorem returnFromCurrentFrame_of_error_back
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {err : Miri.Interpreter.StepError}
    (hback : m.stack.frames.back? = some topFrame)
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hop : hooks.returnOperand () m = (m, .error err)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () false m = (m, .error err) := by
  rcases hooks with ⟨bodySpan, returnOperand, popFrame, copyReturn, cleanupFrame, unwindTerminate⟩
  dsimp only at hop
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  rw [hcleanup, hop]
  rfl

theorem returnFromCurrentFrame_of_copy_error_back
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m m' m'' : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {err : Miri.Interpreter.StepError} {op : Miri.Interpreter.Operand AnnealProv}
    (hback : m.stack.frames.back? = some topFrame)
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hclean : bb.isCleanup = false)
    (hop : hooks.returnOperand () m = (m', .ok op))
    (hpop : hooks.popFrame () m' = (m'', .ok topFrame))
    (hcopy : hooks.copyReturn () op topFrame.returnPlace m'' = (m'', .error err)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () false m =
      (m'', .error err) := by
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  dsimp only [bind, pure, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.run]
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  unfold translateBasicBlockData
  rw [hclean]
  simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have h_op : (hooks.returnOperand () m) = (m', Except.ok op) := hop
  simp only [h_op]
  have h_pop : (hooks.popFrame () m') = (m'', Except.ok topFrame) := hpop
  simp only [h_pop]
  have h_copy : (hooks.copyReturn () op topFrame.returnPlace m'') = (m'', Except.error err) := hcopy
  simp only [h_copy]
  rfl

theorem returnFromCurrentFrame_lm4_1_root_ok
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hretCont : topFrame.returnContinuation = .stop false)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts).returnOperand () m = (m, .ok op))
    (hcopy :
      (annealControlHooksLM4_1 body.localDecls body.layouts).copyReturn () op
        topFrame.returnPlace { m with stack := ⟨#[]⟩ } =
        ({ m with stack := ⟨#[]⟩ }, .ok ())) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts) () false m =
      ({ m with stack := ⟨#[]⟩ }, .ok ()) := by
  have hpop :
      (annealControlHooksLM4_1 body.localDecls body.layouts).popFrame () m =
        ({ m with stack := ⟨#[]⟩ }, .ok topFrame) :=
    annealPopFrameLM4_1_singleton hframes
  have hclean :
      (annealControlHooksLM4_1 body.localDecls body.layouts).cleanupFrame () false
        topFrame { m with stack := ⟨#[]⟩ } =
        ({ m with stack := ⟨#[]⟩ }, .ok .noCleanup) := by
    unfold annealControlHooksLM4_1
    dsimp only
    rw [cleanupStackFrame_root_stop body.localDecls body.layouts ⟨#[]⟩ m.machine.memory topFrame hretCont]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    hcleanup, hop, hpop, hcopy, hclean]
  rfl

/-- **Theorem 3 (`step_terminator_return_root_simulation`)**:
From a root-frame state (`s.memory.callStack = []`) satisfying
`MultiFrameStateRel rootBody s m`, executing `TerminatorKind.return_`:
* faults with undefined behavior in both machines if `_0` is `.dead` or `.uninit`;
* returns `MirStepNode.retNormal retVal s.memory` (`ITree.ret (.normal (retVal, s.memory))`)
  in Anneal and empties `lean-miri`'s call stack (`m'.stack.frames = #[]`) after
  reading an `ImmediateRel` or `MemPlaceRel`-related return operand from `_0`
  (covering ZST `()`, scalars, scalar pairs, and `.indirect` `_0`) and running
  `Stack.cleanupStackFrame` (`.ok .noCleanup`) if `_0` is `.init retVal`. -/
theorem step_terminator_return_root_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = .nil)
    (hphase : ∀ p, rootBody.phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? rootBody.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm : bb.terminator.kind = .return_)
    (hdecl0 : get? rootBody.localDecls 0 = some decl0)
    (hzst_init :
      (translateTy decl0.ty rootBody.layouts).layout.size = Miri.ABI.Size.ZERO →
        get? s.frame.locals 0 ≠ some .uninit)
    (hret0 : ∀ tf, m.stack.frames.back? = some tf →
      RootIndirectRetWf m.machine rootBody s.frame tf)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with ⟨topFrame, hback, hcal_root, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hact_body : activeMirBody rootBody s = rootBody := by
    unfold activeMirBody
    rcases hcal_root hstack with hnone | hsome
    · simp [hnone]
    · simp [hsome]
  have hpopped_root : annealPoppedFrameState s = {} := by
    unfold annealPoppedFrameState
    rw [hstack]
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  rw [hstack, hact_body] at hlinks
  cases hlinks with
  | root _ rootMf _ hretCont hretPlace hframe =>
    obtain ⟨retLay, hretPlace⟩ := hretPlace
    have hframes : m.stack.frames = #[rootMf] := by
      have h := array_eq_of_toList_reverse_cons hmfs
      simpa using h
    have hback_root : m.stack.frames.back? = some rootMf := by rw [hframes]; rfl
    have htf_eq : rootMf = topFrame := Option.some.inj (hback_root.symm.trans hback)
    subst htf_eq
    have hphase' : ∀ p, (activeMirBody rootBody s).phase ≠ .other p := by
      rw [hact_body]; exact hphase
    have hbb' : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb := by
      rw [hact_body]; exact hbb
    rw [stepMirFn_activeMirBody_eq rootBody s hphase']
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb', hstmt_none, hbeq_len, ↓reduceIte]
    rw [miri_step_at_terminator_multiFrame hback (by rw [hact_body]; exact hframe.body_eq)
      hframe.location_eq hbb' hstmt_none]
    rw [hact_body, hpopped_root]
    obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? rootMf 0 mls0 hmls0
    have hretWf0 := hret0 rootMf hback
    unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, hstack, hslot0]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    cases hloc0 with
    | dead cachedLayout _ =>
      rw [returnFromCurrentFrame_of_error_back
        (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts)
        hback hframe.body_eq hframe.location_eq hbb hcleanup
        (annealControlHooks_returnOperand_dead_back hback hget0)]
      exact StepRelMultiFrame.ub _ _
    | indirect slot0 mp0 cachedLayout hlay hne_dead hmemRel0 =>
      have hop0 :
          (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
            (m, .ok (.indirect mp0)) :=
        annealControlHooks_returnOperand_indirect_back hback hget0
      have hpop0 :
          (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).popFrame () m =
            ({ m with stack := ⟨#[]⟩ }, .ok rootMf) :=
        annealPopFrameLM4_1_singleton hframes
      obtain ⟨hnodup0, hprim0, hretPlace0, hinit_sc0, huninit0⟩ :=
        hretWf0 mp0 cachedLayout decl0 hmls0 hdecl0
      have hmemRel0_save := hmemRel0
      rcases hmemRel0 with
        ⟨allocId0, tag0, baseAddr0, off0, localAlloc0,
          hprov0, _, _, hlive0, hbase0, _, hptr0,
          _, _, _, _, _, hscalar_cons0, _⟩
      have hfind0 := array_find?_of_nodup_fst hnodup0 hlive0
      cases slot0 with
      | dead => exact False.elim (hne_dead rfl)
      | uninit =>
        obtain ⟨badRange, hmask_err0⟩ :=
          huninit0 hslot0 allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0 hlive0 hbase0 hptr0
        let m₁ : AnnealStepState := { m with stack := ⟨#[]⟩ }
        have hread_ub :
            annealReadIndirectImmediate mp0
              (translateTy decl0.ty rootBody.layouts) m₁ =
            .error (.undefinedBehavior "read of uninitialized memory field") m₁ :=
          annealReadIndirectImmediate_scalar_uninit_ub
            (m := m₁) hprim0 hprov0 hbase0 hptr0 hfind0 hmask_err0
        have hcopy_err :
            (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).copyReturn ()
              (.indirect mp0) rootMf.returnPlace m₁ =
            (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
          have hcurr_m₁ : m₁.stack.currentFrame? = none := rfl
          unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
          rw [hretPlace0]
          dsimp only []
          rw [hcurr_m₁]
          dsimp only []
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hread_ub]
        rw [returnFromCurrentFrame_of_copy_error_back
          (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts)
          hback hframe.body_eq hframe.location_eq hbb hcleanup hop0 hpop0 hcopy_err]
        exact StepRelMultiFrame.ub _ _
      | init retVal =>
        obtain ⟨sc0, rfl⟩ := hinit_sc0 retVal hslot0
        obtain ⟨_, _, _, msc0, _, hread0⟩ := hscalar_cons0 sc0 rfl
        let m₁ : AnnealStepState := { m with stack := ⟨#[]⟩ }
        have hread_ok :
            annealReadIndirectImmediate mp0
              (translateTy decl0.ty rootBody.layouts) m₁ =
            .ok ⟨.scalar (.fromScalarInt msc0), translateTy decl0.ty rootBody.layouts⟩ m₁ :=
          annealReadIndirectImmediate_scalar_ok
            (m := m₁) hprim0 hprov0 hbase0 hptr0 hfind0 hread0
        have hcopy_ok :
            (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).copyReturn ()
              (.indirect mp0) rootMf.returnPlace m₁ =
            (m₁, .ok ()) := by
          have hcurr_m₁ : m₁.stack.currentFrame? = none := rfl
          unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
          rw [hretPlace0]
          dsimp only []
          rw [hcurr_m₁]
          dsimp only []
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hread_ok]
          rfl
        rw [returnFromCurrentFrame_lm4_1_root_ok hframes hframe.body_eq hframe.location_eq
          hbb hcleanup hretCont hop0 hcopy_ok]
        exact StepRelMultiFrame.retRoot decl0 (.scalar sc0) (.indirect mp0) s.memory _
          hdecl0 hop0 (Or.inr ⟨mp0, rfl, hmemRel0_save⟩) rfl
    | immediate _ imm cachedLayout _ hval =>
      rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
      · have hsz0 : (translateTy decl0.ty rootBody.layouts).layout.size ≠ Miri.ABI.Size.ZERO :=
          fun hz => hzst_init hz hslot0
        rw [returnFromCurrentFrame_of_error_back
          (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts)
          hback hframe.body_eq hframe.location_eq hbb hcleanup
          (annealControlHooks_returnOperand_uninit_back hback hframe.body_eq hframe.location_eq
            hbb hcleanup hget0 hdecl0 hsz0)]
        exact StepRelMultiFrame.ub _ _
      · have hcopy_imm :
            ∀ imm0,
              (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).copyReturn ()
                (.immediate imm0) rootMf.returnPlace { m with stack := ⟨#[]⟩ } =
              ({ m with stack := ⟨#[]⟩ }, .ok ()) := by
          intro imm0
          unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
          rw [hretPlace]
          rfl
        cases himmRel with
        | unit hzero =>
          have hop0 :
              (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
                (m, .ok (.immediate .uninit)) :=
            annealControlHooks_returnOperand_zst_unit_back hback hget0 hdecl0 hzero
          rw [returnFromCurrentFrame_lm4_1_root_ok hframes hframe.body_eq hframe.location_eq
            hbb hcleanup hretCont hop0 (hcopy_imm .uninit)]
          exact StepRelMultiFrame.retRoot decl0 .unit (.immediate .uninit) s.memory _
            hdecl0 hop0 (Or.inl ⟨.uninit, rfl, .unit hzero⟩) rfl
        | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
          have hop0 :
              (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
                (m, .ok (.immediate (.scalar (.fromScalarInt msc)))) :=
            annealControlHooks_returnOperand_scalar_back hback hget0
          rw [returnFromCurrentFrame_lm4_1_root_ok hframes hframe.body_eq hframe.location_eq
            hbb hcleanup hretCont hop0 (hcopy_imm _)]
          exact StepRelMultiFrame.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (Or.inl ⟨_, rfl, .scalar sc msc hsc hsz_sc hbool_sc hchar_sc⟩) rfl
        | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
          have hop0 :
              (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
                (m, .ok (.immediate (.scalarPair (.fromScalarInt msc₁) (.fromScalarInt msc₂)))) :=
            annealControlHooks_returnOperand_scalarPair_back hback hget0
          rw [returnFromCurrentFrame_lm4_1_root_ok hframes hframe.body_eq hframe.location_eq
            hbb hcleanup hretCont hop0 (hcopy_imm _)]
          exact StepRelMultiFrame.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (Or.inl ⟨_, rfl, .scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair⟩) rfl

/-! ## 4. Non-Root Callee `Terminator.Return` Simulation (`step_terminator_return_callee_simulation`) -/

theorem annealPopFrameLM4_1_callee_append_singleton
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = ⟨(restMfs.reverse ++ [callerMf]) ++ [calleeMf]⟩) :
    annealPopFrameLM4_1 poppedFrame m =
      ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
         machine :=
           { m.machine with
             borrowTracker := popFrameBorrowTracker poppedFrame m.machine.borrowTracker } },
       .ok calleeMf) := by
  unfold annealPopFrameLM4_1 Miri.Interpreter.Stack.popFrame Array.isEmpty
  rw [hframes]
  simp [pure, Except.pure]

theorem returnFromCurrentFrame_lm4_1_callee_ok
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ m₂ : AnnealStepState}
    {mach₃ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf' calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx targetBb : Nat} {bb : BasicBlockData}
    {unwind : Miri.MIR.UnwindAction}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hback : m.stack.frames.back? = some calleeMf)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hretCont : calleeMf.returnContinuation = .goto (some targetBb) unwind)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hcopy : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).copyReturn () op calleeMf.returnPlace m₁ =
      (m₂, .ok ()))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () false calleeMf m₂ =
      ({ stack := ⟨⟨xs ++ [callerMf']⟩⟩, machine := mach₃ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () false m =
      ({ stack := ⟨⟨xs ++ [{ callerMf' with location := .mir ⟨targetBb, 0⟩ }]⟩⟩
         machine := mach₃ }, .ok ()) := by
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    hcleanup, hop, hpop, hcopy, hclean, hretCont,
    Miri.Interpreter.ControlFlow.returnToBlock,
    Miri.Interpreter.ControlFlow.goToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_lm4_1_callee_div_ub
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ m₂ : AnnealStepState}
    {mach₃ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf' calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {unwind : Miri.MIR.UnwindAction}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hback : m.stack.frames.back? = some calleeMf)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hretCont : calleeMf.returnContinuation = .goto none unwind)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hcopy : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).copyReturn () op calleeMf.returnPlace m₁ =
      (m₂, .ok ()))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () false calleeMf m₂ =
      ({ stack := ⟨⟨xs ++ [callerMf']⟩⟩, machine := mach₃ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () false m =
      ({ stack := ⟨⟨xs ++ [callerMf']⟩⟩, machine := mach₃ },
       .error (.undefinedBehavior "Unreachable")) := by
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    hcleanup, hop, hpop, hcopy, hclean, hretCont,
    Miri.Interpreter.ControlFlow.returnToBlock]

theorem returnFromCurrentFrame_of_unwind_error_back
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m : AnnealStepState}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {err : Miri.Interpreter.StepError}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [topFrame]⟩)
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hop : hooks.returnOperand () m = (m, .error err)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () true m = (m, .error err) := by
  have hback : m.stack.frames.back? = some topFrame := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  rcases hooks with ⟨bodySpan, returnOperand, popFrame, copyReturn, cleanupFrame, unwindTerminate⟩
  dsimp only at hop
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, hcleanup, hsize_ne, hop]

theorem returnFromCurrentFrame_lm4_1_unwind_cleanup_ok
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {retOpt : Option Miri.MIR.BasicBlockId} {cleanupBb : Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hretCont : calleeMf.returnContinuation = .goto retOpt (.Cleanup cleanupBb))
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .mir ⟨cleanupBb, 0⟩ }]⟩⟩
         machine := mach₂ },
       .ok ()) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hcleanup, hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.goToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_lm4_1_unwind_unreachable_ub
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {retOpt : Option Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hretCont : calleeMf.returnContinuation = .goto retOpt .Unreachable)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ },
       .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hcleanup, hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock]

/-- Popping the top frame `calleeMf` from `⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩`
preserves `MultiFrameAllocDisjoint` on `⟨restMfs.reverse ++ [callerMf]⟩`. -/
theorem MultiFrameAllocDisjoint.pop_top
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩) :
    MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ where
  intra_frame mf hmf := by
    apply hdisj.intra_frame mf
    have hmf' : mf ∈ (callerMf :: restMfs).reverse := by
      simpa [List.reverse_cons] using hmf
    exact List.mem_append_left [calleeMf] hmf'
  inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj := by
    have hlt₁ : f₁ < (restMfs.reverse ++ [callerMf]).length := by
      have ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hf₁
      simpa using hlt
    have hlt₂ : f₂ < (restMfs.reverse ++ [callerMf]).length := by
      have ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hf₂
      simpa using hlt
    have heq_list :
        (callerMf :: restMfs).reverse ++ [calleeMf] =
          (restMfs.reverse ++ [callerMf]) ++ [calleeMf] := by
      simp [List.reverse_cons]
    have hf₁' : (⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ : Array _)[f₁]? = some mf₁ := by
      rw [heq_list, array_getElem?_append_singleton_of_lt _ _ hlt₁]
      exact hf₁
    have hf₂' : (⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ : Array _)[f₂]? = some mf₂ := by
      rw [heq_list, array_getElem?_append_singleton_of_lt _ _ hlt₂]
      exact hf₂
    exact hdisj.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁' hf₂' hi hj

/-- Every frame `mf` in `callerMf :: restMfs` has `.indirect` allocations disjoint
from `calleeMf`'s `.indirect` allocations under `MultiFrameAllocDisjoint`. -/
theorem MultiFrameAllocDisjoint.disjoint_with_popped_top
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩)
    (hmf : mf ∈ callerMf :: restMfs) :
    ∀ (i j : Nat) (mp₁ mp₂ : Miri.Interpreter.MemPlace AnnealProv)
      (lay₁ lay₂ : Option Miri.Interpreter.LocalLayout),
      mf.locals[i]? = some { value := .live (.indirect mp₁), layout := lay₁ } →
      calleeMf.locals[j]? = some { value := .live (.indirect mp₂), layout := lay₂ } →
      mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId := by
  intro i j mp₁ mp₂ lay₁ lay₂ hi hj
  have hmem_rev : mf ∈ (callerMf :: restMfs).reverse := List.mem_reverse.mpr hmf
  obtain ⟨f₁, hf₁_lt, rfl⟩ := List.getElem_of_mem hmem_rev
  let f₂ := (callerMf :: restMfs).reverse.length
  have hne : f₁ ≠ f₂ := Nat.ne_of_lt hf₁_lt
  have hf₁_get :
      (⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ : Array _)[f₁]? =
        some ((callerMf :: restMfs).reverse[f₁]'hf₁_lt) := by
    rw [array_getElem?_append_singleton_of_lt _ _ hf₁_lt]
    exact Array.getElem?_eq_getElem hf₁_lt
  have hf₂_get :
      (⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ : Array _)[f₂]? = some calleeMf :=
    array_getElem?_append_singleton_last (callerMf :: restMfs).reverse calleeMf
  exact hdisj.inter_frame f₁ f₂ i j _ calleeMf mp₁ mp₂ lay₁ lay₂ hne hf₁_get hf₂_get hi hj

theorem mem_live_of_deallocFrameLocalsList
    {id : Miri.Memory.AllocId}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind} :
    ∀ (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (mem : AnnealMemory),
      (id, la) ∈ mem.live.toList →
      (∀ s ∈ slots, ∀ mp_s, s.value = .live (.indirect mp_s) →
        mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) →
      (id, la) ∈ (deallocFrameLocalsList mem slots).live.toList
  | [], _, hmem, _ => hmem
  | slot :: rest, mem, hmem, hdisj => by
    have hmem' : (id, la) ∈ (deallocLocalMemory mem slot.value).live.toList := by
      cases hs : slot.value with
      | dead => simpa [deallocLocalMemory, hs] using hmem
      | live op =>
        cases op with
        | immediate _ => simpa [deallocLocalMemory, hs] using hmem
        | indirect mp_s =>
          have hne := hdisj slot List.mem_cons_self mp_s hs
          cases hid : mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
          | none => simpa [deallocLocalMemory, hs, hid] using hmem
          | some id_s =>
            have hne_id : id ≠ id_s := by
              intro heq; apply hne; rw [hid, heq]
            simp only [deallocLocalMemory, hid, Array.toList_filter, List.mem_filter]
            exact ⟨hmem, bne_iff_ne.mpr hne_id⟩
    exact mem_live_of_deallocFrameLocalsList rest (deallocLocalMemory mem slot.value) hmem'
      (fun s hs => hdisj s (List.mem_cons_of_mem _ hs))

theorem nodup_live_of_deallocFrameLocalsList :
    ∀ (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (mem : AnnealMemory),
      (mem.live.toList.map Prod.fst).Nodup →
      ((deallocFrameLocalsList mem slots).live.toList.map Prod.fst).Nodup
  | [], _, hnodup => hnodup
  | slot :: rest, mem, hnodup => by
    have hnodup' : ((deallocLocalMemory mem slot.value).live.toList.map Prod.fst).Nodup := by
      cases hs : slot.value with
      | dead => simpa [deallocLocalMemory, hs] using hnodup
      | live op =>
        cases op with
        | immediate _ => simpa [deallocLocalMemory, hs] using hnodup
        | indirect mp_s =>
          cases hid : mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
          | none => simpa [deallocLocalMemory, hs, hid] using hnodup
          | some id_s =>
            simp only [deallocLocalMemory, hid, Array.toList_filter]
            exact hnodup.sublist (List.Sublist.map Prod.fst (List.filter_sublist))
    exact nodup_live_of_deallocFrameLocalsList rest (deallocLocalMemory mem slot.value) hnodup'

theorem CallerDestinationRel.of_deallocFrameLocals
    {mach : AnnealMachine} {callerFrameIdx : Nat}
    {cf : SavedCallerFrame}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv}
    (hdest : CallerDestinationRel mach callerFrameIdx cf callerMf returnPlace)
    (hdisj :
      ∀ (i j : Nat) (mp₁ mp₂ : Miri.Interpreter.MemPlace AnnealProv)
        (lay₁ lay₂ : Option Miri.Interpreter.LocalLayout),
        callerMf.locals[i]? = some { value := .live (.indirect mp₁), layout := lay₁ } →
        calleeMf.locals[j]? = some { value := .live (.indirect mp₂), layout := lay₂ } →
        mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
          mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    CallerDestinationRel
      { mach with memory := deallocFrameLocals mach.memory calleeMf }
      callerFrameIdx cf callerMf returnPlace := by
  cases hdest with
  | immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls =>
    exact .immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls
  | indirect destIdx destDecl slot mp cachedLayout _ allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hnot_arr hslot hne hmls hretPlace hprov hmis hmeta hmem_live
      hnodup hbase hovf hptr hmut hlen hpmap hmask halign hbnd hmp =>
    have hdisj_slots :
        ∀ s ∈ calleeMf.locals.toList, ∀ mp_s, s.value = .live (.indirect mp_s) →
          mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
            mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId := by
      intro s hs mp₂ hs_val
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      have hj_sz : j < calleeMf.locals.size := by simpa using hj
      have hget_j : calleeMf.locals[j]? =
          some { value := .live (.indirect mp₂), layout := (calleeMf.locals[j]'hj_sz).layout } := by
        rw [Array.getElem?_eq_getElem hj_sz]
        have hv₂ : (calleeMf.locals[j]'hj_sz).value = .live (.indirect mp₂) := hs_val
        cases hls : calleeMf.locals[j]'hj_sz with
        | mk val lay =>
          rw [hls] at hv₂
          dsimp only at hv₂ ⊢
          rw [hv₂]
      exact hdisj destIdx j mp mp₂ cachedLayout _ hmls hget_j
    have hmem_live' :
        (allocId, localAlloc) ∈ (deallocFrameLocals mach.memory calleeMf).live.toList := by
      apply mem_live_of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hmem_live
      intro s hs mp_s hs_val
      have hne_prov := hdisj_slots s hs mp_s hs_val
      rw [hprov] at hne_prov
      exact Ne.symm hne_prov
    have hnodup' :
        ((deallocFrameLocals mach.memory calleeMf).live.toList.map Prod.fst).Nodup :=
      nodup_live_of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hnodup
    have hmp' :
        MemPlaceRel { mach with memory := deallocFrameLocals mach.memory calleeMf }
          destDecl.ty cf.callerBody.layouts
          (slotOptVal slot) mp :=
      MemPlaceRel.of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hmp hdisj_slots
    exact .indirect destIdx destDecl slot mp cachedLayout returnPlace allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hnot_arr hslot hne hmls hretPlace hprov hmis hmeta hmem_live'
      hnodup' hbase hovf hptr hmut hlen hpmap hmask halign hbnd hmp'

theorem mem_of_deallocFrameLocalsList
    {e : Miri.Memory.AllocId × Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind} :
    ∀ (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (mem : AnnealMemory),
      e ∈ (deallocFrameLocalsList mem slots).live.toList →
      e ∈ mem.live.toList
  | [], _, hmem => hmem
  | slot :: rest, mem, hmem => by
    have hmem' := mem_of_deallocFrameLocalsList rest (deallocLocalMemory mem slot.value) hmem
    cases hs : slot.value with
    | dead => simpa [deallocLocalMemory, hs] using hmem'
    | live op =>
      cases op with
      | immediate _ => simpa [deallocLocalMemory, hs] using hmem'
      | indirect mp_s =>
        cases hid : mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => simpa [deallocLocalMemory, hs, hid] using hmem'
        | some id_s =>
          simp only [deallocLocalMemory, hs, hid, Array.toList_filter, List.mem_filter] at hmem'
          exact hmem'.1

theorem CalleeIndirectRetWf.of_deallocFrameLocals
    {mach : AnnealMachine}
    {curBody : CapturedMir} {curAf : StackFrame}
    {cf : SavedCallerFrame}
    {topMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hwf : CalleeIndirectRetWf mach curBody curAf cf topMf) :
    CalleeIndirectRetWf
      { mach with memory := deallocFrameLocals mach.memory calleeMf }
      curBody curAf cf topMf := by
  intro mp0 lay0 decl0 destDecl destIdx h0 hdecl0 hcf hdecl_d
  obtain ⟨hnodup, hprim, hlay, hinit, huninit⟩ :=
    hwf mp0 lay0 decl0 destDecl destIdx h0 hdecl0 hcf hdecl_d
  refine ⟨nodup_live_of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hnodup,
    hprim, hlay, hinit, ?_⟩
  intro hun allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0 hlive0 hbase0 hptr0
  exact huninit hun allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0
    (mem_of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hlive0)
    hbase0 hptr0

theorem CallerStackLinksRel.of_deallocFrameLocals
    {rootBody : CapturedMir} {mach : AnnealMachine}
    {calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {curBody : CapturedMir} {curAf : StackFrame}
    {cs : List SavedCallerFrame} {prots : List Nat}
    {mfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    (hlinks : CallerStackLinksRel rootBody mach curBody curAf cs prots mfs)
    (hdisj : ∀ mf ∈ mfs,
      ∀ (i j : Nat) (mp₁ mp₂ : Miri.Interpreter.MemPlace AnnealProv)
        (lay₁ lay₂ : Option Miri.Interpreter.LocalLayout),
        mf.locals[i]? = some { value := .live (.indirect mp₁), layout := lay₁ } →
        calleeMf.locals[j]? = some { value := .live (.indirect mp₂), layout := lay₂ } →
        mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
          mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    CallerStackLinksRel rootBody
      { mach with memory := deallocFrameLocals mach.memory calleeMf }
      curBody curAf cs prots mfs := by
  induction hlinks with
  | root af rootMf rootProts hrc hrp hfr =>
    exact .root af rootMf rootProts hrc hrp
      (hfr.of_deallocFrameLocals (hdisj rootMf (List.mem_singleton.mpr rfl)))
  | cons cb af cf cs' curProts callerProts topMf callerMf restMfs hrc hdest hfr hretWf hcp hpdisj _ ih =>
    have hdest' := hdest.of_deallocFrameLocals
      (hdisj callerMf (List.mem_cons_of_mem topMf List.mem_cons_self))
    have hfr' := hfr.of_deallocFrameLocals (hdisj topMf List.mem_cons_self)
    have hrest' := ih (fun mf hmf => hdisj mf (List.mem_cons_of_mem topMf hmf))
    exact .cons cb af cf cs' curProts callerProts topMf callerMf restMfs
      hrc hdest' hfr' hretWf.of_deallocFrameLocals hcp hpdisj hrest'

theorem MultiFrameStateRel_callStack_length
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : MultiFrameStateRel rootBody s m) :
    s.memory.callStack.length + 1 = m.stack.frames.size := by
  rcases h with ⟨_, _, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hlen := List.Forall₂.length_eq hlinks.toForall2
  simp only [List.length_cons, List.length_map] at hlen
  have hrev : m.stack.frames.toList.reverse.length = m.stack.frames.size := by
    simp
  omega

theorem list_forall2_head {α β} {R : α → β → Prop} {a : α} {as : List α} {b : β} {bs : List β} (h : List.Forall₂ R (a :: as) (b :: bs)) : R a b := by
  cases h; assumption

theorem get?_eq_some_lt_length {α : Type u} {xs : List α} {i : Nat} {a : α} (h : get? xs i = some a) : i < xs.length := by
  induction xs generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i
    · exact Nat.zero_lt_succ _
    · apply Nat.succ_lt_succ
      apply ih
      exact h

theorem writePlaceValue_not_dead_ok
    {locals : List LocalSlot} {borrows : List BorrowEntry} {destIdx : Local} {val : Value}
    {slot : LocalSlot}
    (hget : get? locals destIdx = some slot)
    (hnd : slot ≠ .dead) :
    writePlaceValue locals borrows ⟨destIdx, .nil⟩ val =
      .ok (locals.set destIdx (.init val)) := by
  unfold writePlaceValue
  simp only [hget]
  have hlt : destIdx < locals.length := get?_eq_some_lt_length hget
  cases slot with
  | dead => exact False.elim (hnd rfl)
  | uninit =>
    rw [set?_eq_some_set hlt]
  | init _ =>
    rw [set?_eq_some_set hlt]

theorem CallerDestinationRel.exists_destDecl
    {mach : AnnealMachine} {callerFrameIdx : Nat}
    {cf : SavedCallerFrame}
    {callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv}
    (h : CallerDestinationRel mach callerFrameIdx cf callerMf returnPlace) :
    ∃ destIdx destDecl,
      cf.destination = ⟨destIdx, .nil⟩ ∧
      get? cf.callerBody.localDecls destIdx = some destDecl := by
  cases h with
  | immediate destIdx destDecl _ _ _ hcf hdecl _ _ _ =>
    exact ⟨destIdx, destDecl, hcf, hdecl⟩
  | indirect destIdx destDecl _ _ _ _ _ _ _ _ _ _ hcf hdecl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨destIdx, destDecl, hcf, hdecl⟩

theorem updateAllocMachine_live_map_fst_eq
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa)) :
    (updateAllocMachine mach u updId kind alloc').memory.live.toList.map Prod.fst =
      mach.memory.live.toList.map Prod.fst := by
  dsimp [updateAllocMachine]
  rw [Array.toList_setIfInBounds, List.map_set]
  have hu_list : u < (mach.memory.live.toList.map Prod.fst).length := by simp [hu_lt]
  have hfst : (mach.memory.live.toList.map Prod.fst)[u]'hu_list = updId := by
    simp [Array.getElem_toList, hu_eq]
  rw [← hfst, List.set_getElem_self]

theorem mem_live_self_of_updateAllocMachine
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hu_lt : u < mach.memory.live.size) :
    (updId, ({ kind := kind, allocation := alloc' } : AnnealLocalAlloc)) ∈
      (updateAllocMachine mach u updId kind alloc').memory.live.toList := by
  dsimp [updateAllocMachine]
  rw [Array.toList_setIfInBounds]
  have hu_list : u < (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩)).length := by
    rw [List.length_set]; simpa using hu_lt
  have hmem := List.getElem_mem hu_list
  rwa [List.getElem_set_self] at hmem

theorem mem_live_ne_of_updateAllocMachine
    {mach : AnnealMachine} {u : Nat} {updId allocId : Miri.Memory.AllocId}
    {oldLa la : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : updId ≠ allocId)
    (hmem : (allocId, la) ∈ mach.memory.live.toList) :
    (allocId, la) ∈ (updateAllocMachine mach u updId kind alloc').memory.live.toList := by
  dsimp [updateAllocMachine]
  rw [Array.toList_setIfInBounds]
  obtain ⟨j, hj, hget_j⟩ := List.mem_iff_getElem.mp hmem
  have hju : j ≠ u := by
    intro rfl
    simp only [Array.getElem_toList] at hget_j
    rw [hu_eq] at hget_j
    injection hget_j with hid_eq
    exact hne hid_eq
  have hj_set : j < (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩)).length := by
    rw [List.length_set]; exact hj
  have hget_set : (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩))[j]'hj_set =
      (allocId, la) := by
    rw [List.getElem_set_ne (Ne.symm hju)]; exact hget_j
  rw [← hget_set]
  exact List.getElem_mem hj_set

theorem mem_live_inv_of_updateAllocMachine
    {mach : AnnealMachine} {u : Nat} {updId allocId : Miri.Memory.AllocId}
    {la : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hne : updId ≠ allocId)
    (hmem : (allocId, la) ∈ (updateAllocMachine mach u updId kind alloc').memory.live.toList) :
    (allocId, la) ∈ mach.memory.live.toList := by
  dsimp [updateAllocMachine] at hmem
  rw [Array.toList_setIfInBounds] at hmem
  obtain ⟨j, hj, hget_j⟩ := List.mem_iff_getElem.mp hmem
  have hj_orig : j < mach.memory.live.toList.length := by
    rw [List.length_set] at hj; exact hj
  by_cases hju : u = j
  · subst hju
    rw [List.getElem_set_self] at hget_j
    injection hget_j with hid_eq
    exact False.elim (hne hid_eq)
  · rw [List.getElem_set_ne hju] at hget_j
    have hmem_orig := List.getElem_mem hj_orig
    rwa [hget_j] at hmem_orig

theorem AllSlotsAllocLive.of_updateAllocMachine
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)}
    (hlive : AllSlotsAllocLive mach.memory slots)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa)) :
    AllSlotsAllocLive (updateAllocMachine mach u updId kind alloc').memory slots := by
  intro s hs mp hv
  obtain ⟨id, hid, hany⟩ := hlive s hs mp hv
  refine ⟨id, hid, ?_⟩
  rw [← Array.any_toList, List.any_eq_true] at hany ⊢
  obtain ⟨x, hx, hbeq⟩ := hany
  have hx_id : x.1 = id := eq_of_beq hbeq
  have hmem_fst : id ∈ (updateAllocMachine mach u updId kind alloc').memory.live.toList.map Prod.fst := by
    rw [updateAllocMachine_live_map_fst_eq hu_lt hu_eq, List.mem_map]
    exact ⟨x, hx, hx_id⟩
  obtain ⟨y, hy, hy_id⟩ := List.mem_map.mp hmem_fst
  exact ⟨y, hy, beq_iff_eq.mpr hy_id⟩

theorem MemPlaceRel.of_updateAllocMachine_ne
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : MemPlaceRel mach ty layouts optVal mp)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    MemPlaceRel (updateAllocMachine mach u updId kind alloc') ty layouts optVal mp := by
  cases h with
  | mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem hbase hovf hptr
      hmut halign hbnd huninit hval hsc harr =>
    have hne_id : updId ≠ allocId := by
      intro heq
      apply hne
      rw [hprov, heq]; rfl
    exact .mk allocId tag baseAddr relOffset la hprov hmis hmeta
      (mem_live_ne_of_updateAllocMachine hu_lt hu_eq hne_id hmem)
      hbase hovf hptr hmut halign hbnd huninit hval hsc harr

theorem LocalRel.of_updateAllocMachine_ne
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ mp', mls.value = .live (.indirect mp') →
      mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    LocalRel (updateAllocMachine mach u updId kind alloc') decl layouts slot mls := by
  cases h with
  | dead c hc => exact .dead c hc
  | immediate _ i c hc hv => exact .immediate slot i c hc hv
  | indirect _ mp c hc hne hmp =>
    exact .indirect slot mp c hc hne
      (hmp.of_updateAllocMachine_ne hu_lt hu_eq (hdisj mp rfl))

theorem FrameRel.of_updateAllocMachine_ne
    {body : CapturedMir} {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af mf)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout),
      mf.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    FrameRel body (updateAllocMachine mach u updId kind alloc') af mf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls := by
    apply (hfr.locals_rel i decl slot mls hdecl hslot hmls).of_updateAllocMachine_ne hu_lt hu_eq
    intro mp' hv
    have hmls' : mf.locals[i]? = some { value := .live (.indirect mp'), layout := mls.layout } := by
      cases mls with
      | mk val lay =>
        dsimp only at hv ⊢
        rw [hv] at hmls
        exact hmls
    exact hdisj i mp' mls.layout hmls'

theorem CallerDestinationRel.of_updateAllocMachine_ne
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {callerFrameIdx : Nat} {cf : SavedCallerFrame}
    {callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv}
    (hdest : CallerDestinationRel mach callerFrameIdx cf callerMf returnPlace)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout),
      callerMf.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    CallerDestinationRel (updateAllocMachine mach u updId kind alloc')
      callerFrameIdx cf callerMf returnPlace := by
  cases hdest with
  | immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls =>
    exact .immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls
  | indirect destIdx destDecl slot mp cachedLayout _ allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hprim hslot hne hmls hretPlace hprov hmis hmeta hmem_live
      hnodup hbase hovf hptr hmut hlen hpmap hmask halign hbnd hmp =>
    have hne_prov := hdisj destIdx mp cachedLayout hmls
    have hne_id : updId ≠ allocId := by
      intro heq
      apply hne_prov
      rw [hprov, heq]; rfl
    have hnodup' :
        ((updateAllocMachine mach u updId kind alloc').memory.live.toList.map Prod.fst).Nodup := by
      rw [updateAllocMachine_live_map_fst_eq hu_lt hu_eq]
      exact hnodup
    exact .indirect destIdx destDecl slot mp cachedLayout returnPlace allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hprim hslot hne hmls hretPlace hprov hmis hmeta
      (mem_live_ne_of_updateAllocMachine hu_lt hu_eq hne_id hmem_live)
      hnodup' hbase hovf hptr hmut hlen hpmap hmask halign hbnd
      (hmp.of_updateAllocMachine_ne hu_lt hu_eq hne_prov)

theorem CalleeIndirectRetWf.of_updateAllocMachine_ne
    {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {curBody : CapturedMir} {curAf : StackFrame} {cf : SavedCallerFrame}
    {topMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hwf : CalleeIndirectRetWf mach curBody curAf cf topMf)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj0 : ∀ (mp0 : Miri.Interpreter.MemPlace AnnealProv)
      (lay0 : Option Miri.Interpreter.LocalLayout),
      topMf.locals[0]? = some { value := .live (.indirect mp0), layout := lay0 } →
      mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    CalleeIndirectRetWf (updateAllocMachine mach u updId kind alloc') curBody curAf cf topMf := by
  intro mp0 lay0 decl0 destDecl destIdx h0 hdecl0 hcf hdecl_d
  obtain ⟨hnodup, hprim, hlay, hinit, huninit⟩ :=
    hwf mp0 lay0 decl0 destDecl destIdx h0 hdecl0 hcf hdecl_d
  have hnodup' :
      ((updateAllocMachine mach u updId kind alloc').memory.live.toList.map Prod.fst).Nodup := by
    rw [updateAllocMachine_live_map_fst_eq hu_lt hu_eq]
    exact hnodup
  refine ⟨hnodup', hprim, hlay, hinit, ?_⟩
  intro hun allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0 hlive0 hbase0 hptr0
  have hne_prov := hdisj0 mp0 lay0 h0
  have hne_id : updId ≠ allocId0 := by
    intro heq
    apply hne_prov
    rw [hprov0, heq]; rfl
  exact huninit hun allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0
    (mem_live_inv_of_updateAllocMachine hne_id hlive0) hbase0 hptr0

theorem CallerStackLinksRel.of_updateAllocMachine_ne
    {rootBody : CapturedMir} {mach : AnnealMachine} {u : Nat} {updId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {curBody : CapturedMir} {curAf : StackFrame}
    {cs : List SavedCallerFrame} {prots : List Nat}
    {mfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    (hlinks : CallerStackLinksRel rootBody mach curBody curAf cs prots mfs)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ mf ∈ mfs,
      ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (lay : Option Miri.Interpreter.LocalLayout),
        mf.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    CallerStackLinksRel rootBody (updateAllocMachine mach u updId kind alloc')
      curBody curAf cs prots mfs := by
  induction hlinks with
  | root af rootMf rootProts hrc hrp hfr =>
    exact .root af rootMf rootProts hrc hrp
      (hfr.of_updateAllocMachine_ne hu_lt hu_eq
        (hdisj rootMf (List.mem_singleton.mpr rfl)))
  | cons cb af cf cs' curProts callerProts topMf callerMf restMfs
      hrc hdest hfr hretWf hcp hpdisj _ ih =>
    have hdest' := hdest.of_updateAllocMachine_ne (kind := kind) (alloc' := alloc') hu_lt hu_eq
      (hdisj callerMf (List.mem_cons_of_mem topMf List.mem_cons_self))
    have hfr' := hfr.of_updateAllocMachine_ne (kind := kind) (alloc' := alloc') hu_lt hu_eq
      (hdisj topMf List.mem_cons_self)
    have hretWf' := hretWf.of_updateAllocMachine_ne (kind := kind) (alloc' := alloc') hu_lt hu_eq
      (fun mp0 lay0 h0 => hdisj topMf List.mem_cons_self 0 mp0 lay0 h0)
    have hrest' := ih (fun mf hmf => hdisj mf (List.mem_cons_of_mem topMf hmf))
    exact .cons cb af cf cs' curProts callerProts topMf callerMf restMfs
      hrc hdest' hfr' hretWf' hcp hpdisj hrest'

theorem MemPlaceRel.of_borrowTracker
    {mach : AnnealMachine} {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : MemPlaceRel mach ty layouts optVal mp) :
    MemPlaceRel { mach with borrowTracker := bt' } ty layouts optVal mp := by
  cases h with
  | mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem hbase hovf hptr
      hmut halign hbnd huninit hval hsc harr =>
    exact .mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem hbase hovf hptr
      hmut halign hbnd huninit hval hsc harr

theorem LocalRel.of_borrowTracker
    {mach : AnnealMachine} {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls) :
    LocalRel { mach with borrowTracker := bt' } decl layouts slot mls := by
  cases h with
  | dead c hc => exact .dead c hc
  | immediate _ i c hc hv => exact .immediate slot i c hc hv
  | indirect _ mp c hc hne hmp => exact .indirect slot mp c hc hne hmp.of_borrowTracker

theorem FrameRel.of_borrowTracker
    {body : CapturedMir} {mach : AnnealMachine}
    {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af mf) :
    FrameRel body { mach with borrowTracker := bt' } af mf :=
  ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
   fun i decl slot mls hdecl hslot hmls =>
     (hfr.locals_rel i decl slot mls hdecl hslot hmls).of_borrowTracker⟩

theorem CallerDestinationRel.of_borrowTracker
    {mach : AnnealMachine} {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {callerFrameIdx : Nat} {cf : SavedCallerFrame}
    {callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv}
    (h : CallerDestinationRel mach callerFrameIdx cf callerMf returnPlace) :
    CallerDestinationRel { mach with borrowTracker := bt' } callerFrameIdx cf callerMf returnPlace := by
  cases h with
  | immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls =>
    exact .immediate destIdx destDecl slot imm cachedLayout hcf hdecl hslot hne hmls
  | indirect destIdx destDecl slot mp cachedLayout _ allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hprim hslot hne hmls hretPlace hprov hmis hmeta hmem_live
      hnodup hbase hovf hptr hmut hlen hpmap hmask halign hbnd hmp =>
    exact .indirect destIdx destDecl slot mp cachedLayout returnPlace allocId tag baseAddr relOffset
      localAlloc words hcf hdecl hprim hslot hne hmls hretPlace hprov hmis hmeta hmem_live
      hnodup hbase hovf hptr hmut hlen hpmap hmask halign hbnd hmp.of_borrowTracker

theorem CalleeIndirectRetWf.of_borrowTracker
    {mach : AnnealMachine} {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {curBody : CapturedMir} {curAf : StackFrame} {cf : SavedCallerFrame}
    {topMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hwf : CalleeIndirectRetWf mach curBody curAf cf topMf) :
    CalleeIndirectRetWf { mach with borrowTracker := bt' } curBody curAf cf topMf :=
  hwf

theorem CallerStackLinksRel.of_borrowTracker
    {rootBody : CapturedMir} {mach : AnnealMachine}
    {bt' : Option Miri.Interpreter.MachineHooks.BorrowState}
    {curBody : CapturedMir} {curAf : StackFrame}
    {cs : List SavedCallerFrame} {prots : List Nat}
    {mfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    (hlinks : CallerStackLinksRel rootBody mach curBody curAf cs prots mfs) :
    CallerStackLinksRel rootBody { mach with borrowTracker := bt' } curBody curAf cs prots mfs := by
  induction hlinks with
  | root af rootMf rootProts hrc hrp hfr =>
    exact .root af rootMf rootProts hrc hrp hfr.of_borrowTracker
  | cons cb af cf cs' curProts callerProts topMf callerMf restMfs
      hrc hdest hfr hretWf hcp hpdisj _ ih =>
    exact .cons cb af cf cs' curProts callerProts topMf callerMf restMfs
      hrc hdest.of_borrowTracker hfr.of_borrowTracker hretWf.of_borrowTracker
      hcp hpdisj ih

/-- **Theorem 4 (`step_terminator_return_callee_simulation`)**:
Returning from a non-root callee frame (`s.memory.callStack = cf :: restStack`)
when the caller destination `cf.destination = ⟨destIdx, .nil⟩` is either an
`.immediate` or `.indirect` local (`CallerDestinationRel`):
* faults with undefined behavior in both machines if `_0` is `.dead` or `.uninit`;
* if `_0` is `.init retVal` (covering ZST `()`, scalars, scalar pairs, and
  `.indirect` `_0`), copies `_0` into the caller's `destIdx` place, deallocates
  all live `.indirect` stack allocations of the popped callee frame via
  `Stack.cleanupStackFrame`, releases the callee frame's `CallId` protectors via
  `Miri.TreeBorrows.GlobalState.endCall` in `m.machine.borrowTracker`
  (`BorrowTrackerStackRel`), and advances the caller frame to
  `(cf.returnTarget, 0)`, preserving `MultiFrameStateRel`. -/
theorem step_terminator_return_callee_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {cf : SavedCallerFrame} {restStack : List SavedCallerFrame}
    (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = cf :: restStack)
    (hva : ∀ tf, m.stack.frames.back? = some tf → tf.vaList = #[])
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm : bb.terminator.kind = .return_)
    (hdecl0 : get? (activeMirBody rootBody s).localDecls 0 = some decl0)
    (hzst_init :
      (translateTy decl0.ty (activeMirBody rootBody s).layouts).layout.size = Miri.ABI.Size.ZERO →
        get? s.frame.locals 0 ≠ some .uninit)
    (hty_compat : ∀ destIdx destDecl,
      cf.destination = ⟨destIdx, .nil⟩ →
      get? cf.callerBody.localDecls destIdx = some destDecl →
      ∀ v imm,
        ImmediateRel decl0.ty (activeMirBody rootBody s).layouts v imm →
        ImmediateRel destDecl.ty cf.callerBody.layouts v imm)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with
    ⟨_, _, _, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  generalize hprots : s.memory.activeProtectors = prots at hlinks hvalid hcid_act hbt
  generalize hcur : activeMirBody rootBody s = curBody at hlinks
  rw [hstack] at hlinks hbt
  cases hlinks with
  | cons _ _ _ _ curFrameProts callerProts calleeMf callerMf restMfs
      hretCont hdest hfr_callee hretWf hcp _ hlinks_caller =>
    subst hcur
    have harr := array_eq_of_toList_reverse_cons hmfs
    have hback : m.stack.frames.back? = some calleeMf := by rw [harr]; simp
    have harr_two :
        m.stack.frames = ⟨( restMfs.reverse ++ [callerMf] ) ++ [calleeMf]⟩ := by
      rw [harr]
      apply Array.ext'
      simp [List.reverse_cons]
    let poppedFrame := annealPoppedFrameState s
    have hpopped_eq :
        poppedFrame =
          poppedCalleeFrameState s.memory.borrows (curFrameProts ++ callerProts)
            (callerRestoredProtectors [cf]) := by
      dsimp only [poppedFrame, annealPoppedFrameState]
      rw [hstack, hprots]
    let bt' := popFrameBorrowTracker poppedFrame m.machine.borrowTracker
    let m₀ : AnnealStepState :=
      { stack := m.stack, machine := { m.machine with borrowTracker := bt' } }
    have hbt_post :
        BorrowTrackerStackRel s.memory.borrows
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors)
          restStack bt' := by
      dsimp only [bt']
      rw [hpopped_eq]
      exact hbt.of_popFrame
    have hdest := hdest.of_borrowTracker (bt' := bt')
    have hfr_callee := hfr_callee.of_borrowTracker (bt' := bt')
    have hretWf := hretWf.of_borrowTracker (bt' := bt')
    have hlinks_caller := hlinks_caller.of_borrowTracker (bt' := bt')
    obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hfr_callee.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? calleeMf 0 mls0 hmls0
    rw [stepMirFn_activeMirBody_eq rootBody s hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
    rw [miri_step_at_terminator_multiFrame hback hfr_callee.body_eq hfr_callee.location_eq hbb hstmt_none]
    unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, hstack, hslot0]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    have hpop :
        (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).popFrame () m =
          ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }, .ok calleeMf) :=
      annealPopFrameLM4_1_callee_append_singleton harr_two
    have hd_callee : MemoryAllocDisjoint calleeMf := by
      apply hdisj.intra_frame calleeMf
      rw [harr]; simp
    have hdisj_orig :
        MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ := by
      rw [← harr]; exact hdisj
    have hdisj_pop : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ :=
      hdisj_orig.pop_top
    have hvalid_post : ActiveProtectorsValid s.memory.borrows callerProts := by
      apply hvalid.mono_protectors
      intro cid hcid
      exact natListContainsBool_append_right curFrameProts callerProts cid hcid
    have hcid_act_post : ∀ cid ∈ callerProts, cid < s.memory.nextProtector := by
      intro cid hcid
      exact hcid_act cid (List.mem_append_right curFrameProts hcid)
    have hcal_root_post :
        restStack = [] →
          some cf.callerBody = none ∨ some cf.callerBody = some rootBody := by
      intro hnil
      subst hnil
      cases hlinks_caller with
      | root _ _ _ _ _ _ => exact Or.inr rfl
    have hvalid_post' :
        ActiveProtectorsValid s.memory.borrows
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors) := by
      have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
      rw [← hcp_rev]; exact hvalid_post
    have hcid_act_post' :
        ∀ cid ∈ (match cf.callerProtector with
                 | some protId => protId :: cf.calleeProtectors
                 | none => cf.calleeProtectors),
          cid < s.memory.nextProtector := by
      have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
      rw [← hcp_rev]; exact hcid_act_post
    have htb_post :
        TreeBorrowsRel s.memory.borrows
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors)
          (basedNormalTree s.memory.borrows
            (match cf.callerProtector with
             | some protId => protId :: cf.calleeProtectors
             | none => cf.calleeProtectors)) :=
      htb.change_protectors _
    cases hloc0 with
    | dead cachedLayout _ =>
      rw [returnFromCurrentFrame_of_error_back
        (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame)
        hback hfr_callee.body_eq hfr_callee.location_eq hbb hcleanup
        (annealControlHooks_returnOperand_dead_back hback hget0)]
      exact StepRelMultiFrame.ub _ _
    | indirect slot0 mp0 cachedLayout hlay hne_dead hmemRel0 =>
      have hop0 :
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).returnOperand () m =
            (m, .ok (.indirect mp0)) :=
        annealControlHooks_returnOperand_indirect_back hback hget0
      obtain ⟨destIdx₀, destDecl₀, hcf₀, hdecl_d₀⟩ := hdest.exists_destDecl
      obtain ⟨hnodup0, hprim_d0, hlay_eq0, hinit_sc0, huninit0⟩ :=
        hretWf mp0 cachedLayout decl0 destDecl₀ destIdx₀ hmls0 hdecl0 hcf₀ hdecl_d₀
      rcases hmemRel0 with
        ⟨allocId0, tag0, baseAddr0, off0, localAlloc0,
          hprov0, hmis0, hmeta0, hlive0, hbase0, hovf0, hptr0,
          hmut0, halign0, hbnd0, huninit_cons0, hval_cons0, hscalar_cons0, _⟩
      have hfind0 := array_find?_of_nodup_fst hnodup0 hlive0
      cases slot0 with
      | dead => exact False.elim (hne_dead rfl)
      | uninit =>
        have hsz0 :
            (translateTy decl0.ty (activeMirBody rootBody s).layouts).layout.size ≠
              Miri.ABI.Size.ZERO :=
          fun hz => hzst_init hz hslot0
        have hnot_init :
            localAlloc0.allocation.initializationMask.isRangeInitialized
              (Miri.Memory.allocRange off0
                (translateTy decl0.ty (activeMirBody rootBody s).layouts).layout.size) ≠
              .ok (.ok ()) :=
          huninit_cons0 rfl hsz0
        obtain ⟨badRange, hmask_err0⟩ :=
          huninit0 hslot0 allocId0 tag0 localAlloc0 baseAddr0 off0 hprov0 hlive0 hbase0 hptr0
        rw [← hlay_eq0] at hmask_err0
        let m₁ : AnnealStepState := { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }
        have hread_ub :
            annealReadIndirectImmediate mp0
              (translateTy destDecl₀.ty cf.callerBody.layouts) m₁ =
            .error (.undefinedBehavior "read of uninitialized memory field") m₁ :=
          annealReadIndirectImmediate_scalar_uninit_ub
            (m := m₁) hprim_d0 hprov0 hbase0 hptr0 hfind0 hmask_err0
        have hcopy_err :
            (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).copyReturn ()
              (.indirect mp0) calleeMf.returnPlace m₁ =
              (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
          generalize hrp_callee : calleeMf.returnPlace = rp_callee at hdest ⊢
          cases hdest with
          | immediate destIdx destDecl slot_d imm_d cachedLayout_d hcf hdecl_d hslot_d hne_dead_d hmls_d =>
            have hd_eq : destIdx = destIdx₀ := by
              rw [hcf₀] at hcf; injection hcf with h_eq _; exact h_eq.symm
            subst hd_eq
            have hdd_eq : destDecl = destDecl₀ := by
              rw [hdecl_d₀] at hdecl_d; exact Option.some.inj hdecl_d.symm
            subst hdd_eq
            have hget_d := frame_getLocal_of_getElem? callerMf destIdx
              ⟨.live (.immediate imm_d), cachedLayout_d⟩ hmls_d
            have hne_false :
                (restMfs.length !=
                  (⟨restMfs.reverse ++ [callerMf]⟩ :
                    Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                false := by simp
            have hrun_err :
                Miri.Interpreter.runRvalue
                  (do
                    let rv ← annealReadIndirectImmediate mp0
                      (translateTy destDecl.ty cf.callerBody.layouts)
                    pure rv.imm) m₁ =
                (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
              unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_error hread_ub]
            unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
              Miri.Interpreter.Stack.currentFrame?
            dsimp only [m₁] at hrun_err ⊢
            simp +zetaHave only [array_back?_append_singleton, hne_false,
              Bool.false_eq_true, ↓reduceIte, hget_d, hrun_err]
          | indirect destIdx destDecl slot_d mp_d c_d _ allocId tag baseAddr relOffset
              localAlloc words hcf hdecl_d _ _ _ hmls_d hrp_or _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            have hd_eq : destIdx = destIdx₀ := by
              rw [hcf₀] at hcf; injection hcf with h_eq _; exact h_eq.symm
            subst hd_eq
            have hdd_eq : destDecl = destDecl₀ := by
              rw [hdecl_d₀] at hdecl_d; exact Option.some.inj hdecl_d.symm
            subst hdd_eq
            have hrun_err :
                Miri.Interpreter.runRvalue
                  (do
                    let imm ← do
                      let rv ← annealReadIndirectImmediate mp0
                        (translateTy destDecl.ty cf.callerBody.layouts)
                      pure rv.imm
                    annealWriteIndirectImmediate imm mp_d Miri.ABI.Size.ZERO
                      (translateTy destDecl.ty cf.callerBody.layouts)) m₁ =
                (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
              unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_error hread_ub]
            rcases hrp_or with rfl | rfl
            · unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
              exact hrun_err
            · have hget_d := frame_getLocal_of_getElem? callerMf destIdx
                ⟨.live (.indirect mp_d), c_d⟩ hmls_d
              have hne_false :
                  (restMfs.length !=
                    (⟨restMfs.reverse ++ [callerMf]⟩ :
                      Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                  false := by simp
              unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
                Miri.Interpreter.Stack.currentFrame?
              dsimp only [m₁] at hrun_err ⊢
              simp +zetaHave only [array_back?_append_singleton, hne_false,
                Bool.false_eq_true, ↓reduceIte, hget_d]
              exact hrun_err
        rw [returnFromCurrentFrame_of_copy_error_back
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame)
          hback hfr_callee.body_eq hfr_callee.location_eq hbb hcleanup hop0 hpop hcopy_err]
        dsimp only [Except.map]
        exact StepRelMultiFrame.ub _ _
      | init retVal =>
        obtain ⟨sc0, rfl⟩ := hinit_sc0 retVal hslot0
        obtain ⟨hsz0_eq, hbool0, hchar0, msc0, hrel0, hread0⟩ := hscalar_cons0 sc0 rfl
        have himmRel0 :
            ImmediateRel decl0.ty (activeMirBody rootBody s).layouts
              (.scalar sc0) (.scalar (.fromScalarInt msc0)) :=
          .scalar sc0 msc0 hrel0 hsz0_eq hbool0 hchar0
        have hread0' :
            localAlloc0.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange off0
                (translateTy destDecl₀.ty cf.callerBody.layouts).layout.size) false =
              .ok (Miri.Memory.Scalar.fromScalarInt msc0) := by
          rw [hlay_eq0]; exact hread0
        let m₁ : AnnealStepState := { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }
        have hread_ok :
            annealReadIndirectImmediate mp0
              (translateTy destDecl₀.ty cf.callerBody.layouts) m₁ =
            .ok ⟨.scalar (.fromScalarInt msc0), translateTy destDecl₀.ty cf.callerBody.layouts⟩ m₁ :=
          annealReadIndirectImmediate_scalar_ok
            (m := m₁) hprim_d0 hprov0 hbase0 hptr0 hfind0 hread0'
        have hread_bind :
            (do
              let rv ← annealReadIndirectImmediate mp0
                (translateTy destDecl₀.ty cf.callerBody.layouts)
              pure rv.imm) m₁ =
            .ok (.scalar (.fromScalarInt msc0)) m₁ := by
          rw [EStateM.bind_eq_ok hread_ok]
          rfl
        generalize hrp_callee : calleeMf.returnPlace = rp_callee at hdest
        cases hdest with
        | immediate destIdx destDecl slot_d imm_d cachedLayout_d hcf hdecl_d hslot_d hne_dead hmls_d =>
          have hd_eq : destIdx = destIdx₀ := by
            rw [hcf₀] at hcf; injection hcf with h_eq _; exact h_eq.symm
          subst hd_eq
          have hdd_eq : destDecl = destDecl₀ := by
            rw [hdecl_d₀] at hdecl_d; exact Option.some.inj hdecl_d.symm
          subst hdd_eq
          have hforall_caller := hlinks_caller.toForall2
          have hfr_caller := list_forall2_head hforall_caller
          obtain ⟨_, mls_d', hlt_af_d, hlt_mf_d, _, hmls_d', hmls_eq_d, hloc_d⟩ :=
            hfr_caller.lookup_local hdecl_d
          have hmls_eq2 : mls_d' = ⟨.live (.immediate imm_d), cachedLayout_d⟩ := by
            rw [hmls_d] at hmls_d'; exact Option.some.inj hmls_d'.symm
          subst hmls_eq2
          have hcache_d : ∀ l ∈ cachedLayout_d, l = translateTy destDecl.ty cf.callerBody.layouts :=
            hloc_d.cachedLayout_eq
          have hwrite_af :
              writePlaceValue cf.frame.locals s.memory.borrows cf.destination (.scalar sc0) =
                .ok (cf.frame.locals.set destIdx (.init (.scalar sc0))) := by
            rw [hcf]; exact writePlaceValue_not_dead_ok hslot_d hne_dead
          let imm0 : Miri.Interpreter.Immediate AnnealProv := .scalar (.fromScalarInt msc0)
          let callerMf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { callerMf with
              locals := callerMf.locals.set destIdx
                { callerMf.locals[destIdx]'hlt_mf_d with value := .live (.immediate imm0) } hlt_mf_d }
          have hrun_ok :
              Miri.Interpreter.runRvalue
                (do
                  let rv ← annealReadIndirectImmediate mp0
                    (translateTy destDecl.ty cf.callerBody.layouts)
                  pure rv.imm) m₁ =
              (m₁, .ok imm0) := by
            unfold Miri.Interpreter.runRvalue
            rw [hread_bind]
          have hcopy :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).copyReturn ()
                (.indirect mp0) calleeMf.returnPlace m₁ =
              ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ }, .ok ()) := by
            rw [hrp_callee]
            have hget_d := frame_getLocal_of_getElem? callerMf destIdx
              ⟨.live (.immediate imm_d), cachedLayout_d⟩ hmls_d
            have hrep_d := frame_replaceLocalValue_of_lt callerMf destIdx hlt_mf_d
              (.live (.immediate imm0))
            have hne_false :
                (restMfs.length !=
                  (⟨restMfs.reverse ++ [callerMf]⟩ :
                    Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                false := by simp
            have hidx_lt :
                (⟨restMfs.reverse ++ [callerMf]⟩ :
                  Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 <
                  (⟨restMfs.reverse ++ [callerMf]⟩ :
                    Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size := by simp
            unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
              Miri.Interpreter.Stack.currentFrame?
            dsimp only [m₁] at hrun_ok ⊢
            simp +zetaHave only [array_back?_append_singleton, hne_false,
              Bool.false_eq_true, ↓reduceIte, hget_d, hrun_ok, hrep_d,
              hidx_lt, ↓reduceDIte]
            congr 3
            apply Array.ext'
            simp
            rfl
          have hclean :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
                false calleeMf { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ } =
              ({ stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩
                 machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
               .ok .normal) := by
            unfold annealControlHooksLM4_1
            dsimp only
            rw [cleanupStackFrame_callee_goto
              (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
              ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ m₀.machine.memory calleeMf
              hretCont (hva calleeMf hback)
              hfr_callee.allSlotsAllocLive hd_callee.slotsAllocDisjoint]
          by_cases hdiv_true : cf.isDiverging = true
          · simp only [hdiv_true, ↓reduceIte] at hretCont ⊢
            rw [returnFromCurrentFrame_lm4_1_callee_div_ub hback hfr_callee.body_eq hfr_callee.location_eq
              hbb hcleanup hretCont hop0 hpop hcopy hclean]
            dsimp only [Except.map]
            exact StepRelMultiFrame.ub _ _
          have hdiv_false : cf.isDiverging = false := Bool.eq_false_iff.mpr hdiv_true
          simp only [hdiv_false, Bool.false_eq_true, ↓reduceIte] at hretCont ⊢
          simp only [hwrite_af, restoreCallerProtectors]
          rw [returnFromCurrentFrame_lm4_1_callee_ok hback hfr_callee.body_eq hfr_callee.location_eq
            hbb hcleanup hretCont hop0 hpop hcopy hclean]
          dsimp only [Except.map]
          apply StepRelMultiFrame.step
          let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { callerMf₁ with location := .mir ⟨cf.returnTarget, 0⟩ }
          let mach' : AnnealMachine :=
            { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf }
          have himmRel_d : ImmediateRel destDecl.ty cf.callerBody.layouts (.scalar sc0) imm0 :=
            hty_compat destIdx destDecl hcf hdecl_d (.scalar sc0) imm0 himmRel0
          have hnew_loc_d :
              LocalRel m₀.machine destDecl cf.callerBody.layouts (.init (.scalar sc0))
                { callerMf.locals[destIdx]'hlt_mf_d with value := .live (.immediate imm0) } := by
            rw [hmls_eq_d]
            exact .immediate (.init (.scalar sc0)) imm0 cachedLayout_d hcache_d
              (Or.inr ⟨.scalar sc0, rfl, himmRel_d⟩)
          have hfr_caller₁ :=
            hfr_caller.update_local hdecl_d (.init (.scalar sc0)) (.live (.immediate imm0)) hnew_loc_d
          have hfr_caller_loc :
              FrameRel cf.callerBody m₀.machine
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                callerMf' :=
            ⟨hfr_caller₁.body_eq, rfl, hfr_caller₁.af_locals_len,
             hfr_caller₁.mf_locals_size, hfr_caller₁.locals_rel⟩
          have hlinks_updated :
              CallerStackLinksRel rootBody m₀.machine cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                restStack callerProts (callerMf' :: restMfs) := by
            refine hlinks_caller.update_top_frame rfl rfl rfl hfr_caller_loc ?_
            intro mp_z lay_z hz
            dsimp only [callerMf', callerMf₁] at hz
            by_cases hz_d : destIdx = 0
            · subst hz_d
              rw [Array.getElem?_set_self] at hz
              cases hz
            · rw [Array.getElem?_set_ne _ hz_d] at hz
              refine ⟨⟨lay_z, hz⟩, Or.inl ?_⟩
              dsimp only
              rw [get?_eq_getElem?, get?_eq_getElem?, List.getElem?_set_ne hz_d]
          have hlinks_post :
              CallerStackLinksRel rootBody mach' cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                restStack callerProts (callerMf' :: restMfs) := by
            apply hlinks_updated.of_deallocFrameLocals
            intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
            rcases List.mem_cons.mp hmf with rfl | hmem_rest
            · dsimp only [callerMf', callerMf₁] at hi
              by_cases hi_d : destIdx = i
              · subst hi_d
                rw [Array.getElem?_set_self] at hi
                cases hi
              · rw [Array.getElem?_set_ne _ hi_d] at hi
                exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
            · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest)
                i j mp₁ mp₂ lay₁ lay₂ hi hj
          have hd_callerMf' : MemoryAllocDisjoint callerMf' := by
            have hd_callerMf : MemoryAllocDisjoint callerMf := by
              apply hdisj_pop.intra_frame callerMf
              simp
            apply MemoryAllocDisjoint.mono_immediate hd_callerMf
            intro k
            by_cases hk : destIdx = k
            · subst hk
              right
              exact ⟨imm0, (callerMf.locals[destIdx]'hlt_mf_d).layout, by
                dsimp only [callerMf', callerMf₁]; rw [Array.getElem?_set_self]⟩
            · left
              dsimp only [callerMf', callerMf₁]
              rw [Array.getElem?_set_ne _ hk]
          have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ := by
            apply hdisj_pop.replace_top hd_callerMf'
            intro i mp lay hi
            dsimp only [callerMf', callerMf₁] at hi
            by_cases hi_d : destIdx = i
            · subst hi_d
              rw [Array.getElem?_set_self] at hi
              cases hi
            · rw [Array.getElem?_set_ne _ hi_d] at hi
              exact ⟨lay, hi⟩
          refine .mk callerMf'
            (array_back?_append_singleton restMfs.reverse callerMf')
            hcal_root_post (fun _ => rfl)
            (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, hcp] using hlinks_post.toForall2)
            (by
              have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
              cases hcp_rev
              unfold activeMirBody
              have hrev_post :
                (⟨restMfs.reverse ++ [callerMf']⟩ : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).toList.reverse =
                  callerMf' :: restMfs :=
                array_toList_reverse_append_singleton restMfs callerMf'
              rw [hrev_post]
              exact hlinks_post)
            hdisj_post htb_post
            hvalid_post' hcid_pos hcid_act_post' hcid_bor hbt_post
        | indirect destIdx destDecl slot_d mp_d c_d rp_callee allocId tag baseAddr relOffset
            localAlloc words hcf hdecl_d hprim_d hslot_d hne_dead hmls_d hrp_or hprov hmis
            hmeta hlive hnodup hbase h_no_overflow h_offset hmut hlen hprovMap hmask_rel
            halign h_in_bounds hmem_rel =>
          have hd_eq : destIdx = destIdx₀ := by
            rw [hcf₀] at hcf; injection hcf with h_eq _; exact h_eq.symm
          subst hd_eq
          have hdd_eq : destDecl = destDecl₀ := by
            rw [hdecl_d₀] at hdecl_d; exact Option.some.inj hdecl_d.symm
          subst hdd_eq
          have hforall_caller := hlinks_caller.toForall2
          have hfr_caller := list_forall2_head hforall_caller
          obtain ⟨_, mls_d', hlt_af_d, hlt_mf_d, _, hmls_d', hmls_eq_d, hloc_d⟩ :=
            hfr_caller.lookup_local hdecl_d
          have hmls_eq2 : mls_d' = ⟨.live (.indirect mp_d), c_d⟩ := by
            rw [hmls_d] at hmls_d'; exact Option.some.inj hmls_d'.symm
          subst hmls_eq2
          have hcache_d : ∀ l ∈ c_d, l = translateTy destDecl.ty cf.callerBody.layouts :=
            hloc_d.cachedLayout_eq
          have hwrite_af :
              writePlaceValue cf.frame.locals s.memory.borrows cf.destination (.scalar sc0) =
                .ok (cf.frame.locals.set destIdx (.init (.scalar sc0))) := by
            rw [hcf]; exact writePlaceValue_not_dead_ok hslot_d hne_dead
          obtain ⟨u, hu_lt, hfidx, hget, _⟩ := array_findIdx?_of_nodup_fst hnodup hlive
          have himmRel_dest :=
            hty_compat destIdx destDecl hcf hdecl_d (.scalar sc0) (.scalar (.fromScalarInt msc0)) himmRel0
          have hsz_dest : (translateTy destDecl.ty cf.callerBody.layouts).layout.size = translateSizeBytes sc0.sizeBytes := by
            cases himmRel_dest with
            | scalar _ _ _ h _ _ => exact h
          have hbool_dest : destDecl.ty.kind = .bool → sc0.sizeBytes = 1 ∧ (sc0.bits = 0 ∨ sc0.bits = 1) := by
            cases himmRel_dest with
            | scalar _ _ _ _ hb _ => exact hb
          have hchar_dest : destDecl.ty.kind = .char → sc0.sizeBytes = 4 ∧ isValidCharCode sc0.bits = true := by
            cases himmRel_dest with
            | scalar _ _ _ _ _ hc => exact hc
          have hbnd :
              relOffset.bytes.toNat + (translateSizeBytes sc0.sizeBytes).bytes.toNat ≤
                localAlloc.allocation.byteSize.bytes.toNat := by
            rw [← hsz_dest]; exact h_in_bounds
          obtain ⟨alloc', words', hw, hbsize', hlen', hmut', hprov', hmask', _, _, hinit_i, hread_i⟩ :=
            alloc_writeScalar_at_offset_mask hrel0 hlen hmut hprovMap hmask_rel hbnd
          have hget' : m₀.machine.memory.live[u]'hu_lt = (allocId, localAlloc) := by
            have h1 := Array.getElem?_eq_getElem hu_lt
            exact Option.some.inj (h1.symm.trans hget)
          have hw_cast :
              Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOffset.bytes + Miri.ABI.Size.ZERO.bytes))
                  (@Miri.Memory.Scalar.size AnnealProv (@Miri.Memory.Scalar.fromScalarInt AnnealProv msc0)))
                (@Miri.Memory.Scalar.fromScalarInt AnnealProv msc0) localAlloc.allocation =
              EStateM.Result.ok () alloc' := by
            have h_off : Miri.ABI.Size.ofBytes (relOffset.bytes + Miri.ABI.Size.ZERO.bytes) = relOffset := by
              cases relOffset; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
            rw [h_off]; exact hw
          have hw_ind :=
            annealWriteIndirectImmediate_scalar_ok
              (m := m₁) (mpOff := relOffset)
              (fieldLay := translateTy destDecl.ty cf.callerBody.layouts)
              (relOffset := Miri.ABI.Size.ZERO)
              (alloc' := alloc') (u := u) (localAlloc := localAlloc)
              hprov hbase h_offset hu_lt hfidx hget' hw_cast
          let mach₁ := updateAllocMachine m₀.machine u allocId localAlloc.kind alloc'
          let m₂ : AnnealStepState :=
            { stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩, machine := mach₁ }
          have hbind_write :
              (do
                let imm ← do
                  let rv ← annealReadIndirectImmediate mp0
                    (translateTy destDecl.ty cf.callerBody.layouts)
                  pure rv.imm
                annealWriteIndirectImmediate imm mp_d Miri.ABI.Size.ZERO
                  (translateTy destDecl.ty cf.callerBody.layouts)) m₁ =
              .ok () m₂ := by
            rw [EStateM.bind_eq_ok hread_ok]
            exact hw_ind
          have hrun_ok :
              Miri.Interpreter.runRvalue
                (do
                  let imm ← do
                    let rv ← annealReadIndirectImmediate mp0
                      (translateTy destDecl.ty cf.callerBody.layouts)
                    pure rv.imm
                  annealWriteIndirectImmediate imm mp_d Miri.ABI.Size.ZERO
                    (translateTy destDecl.ty cf.callerBody.layouts)) m₁ =
              (m₂, .ok ()) := by
            unfold Miri.Interpreter.runRvalue
            rw [hbind_write]
          have hcopy :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).copyReturn ()
                (.indirect mp0) calleeMf.returnPlace m₁ =
              (m₂, .ok ()) := by
            rw [hrp_callee]
            rcases hrp_or with rfl | rfl
            · unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
              exact hrun_ok
            · have hget_d := frame_getLocal_of_getElem? callerMf destIdx
                ⟨.live (.indirect mp_d), c_d⟩ hmls_d
              have hne_false :
                  (restMfs.length !=
                    (⟨restMfs.reverse ++ [callerMf]⟩ :
                      Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                  false := by simp
              unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
                Miri.Interpreter.Stack.currentFrame?
              dsimp only [m₁] at hrun_ok ⊢
              simp +zetaHave only [array_back?_append_singleton, hne_false,
                Bool.false_eq_true, ↓reduceIte, hget_d]
              exact hrun_ok
          have hlive_callee₁ : AllSlotsAllocLive mach₁.memory calleeMf.locals.toList :=
            hfr_callee.allSlotsAllocLive.of_updateAllocMachine hu_lt hget'
          have hclean :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
                false calleeMf m₂ =
              ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
                 machine := { mach₁ with memory := deallocFrameLocals mach₁.memory calleeMf } },
               .ok .normal) := by
            unfold annealControlHooksLM4_1
            dsimp only
            rw [cleanupStackFrame_callee_goto
              (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
              ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ mach₁.memory calleeMf
              hretCont (hva calleeMf hback)
              hlive_callee₁ hd_callee.slotsAllocDisjoint]
          by_cases hdiv_true : cf.isDiverging = true
          · simp only [hdiv_true, ↓reduceIte] at hretCont ⊢
            rw [returnFromCurrentFrame_lm4_1_callee_div_ub hback hfr_callee.body_eq hfr_callee.location_eq
              hbb hcleanup hretCont hop0 hpop hcopy hclean]
            dsimp only [Except.map]
            exact StepRelMultiFrame.ub _ _
          have hdiv_false : cf.isDiverging = false := Bool.eq_false_iff.mpr hdiv_true
          simp only [hdiv_false, Bool.false_eq_true, ↓reduceIte] at hretCont ⊢
          simp only [hwrite_af, restoreCallerProtectors]
          rw [returnFromCurrentFrame_lm4_1_callee_ok hback hfr_callee.body_eq hfr_callee.location_eq
            hbb hcleanup hretCont hop0 hpop hcopy hclean]
          dsimp only [Except.map]
          apply StepRelMultiFrame.step
          let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { callerMf with location := .mir ⟨cf.returnTarget, 0⟩ }
          let mach' : AnnealMachine :=
            { mach₁ with memory := deallocFrameLocals mach₁.memory calleeMf }
          have hd_callerMf : MemoryAllocDisjoint callerMf := by
            apply hdisj_pop.intra_frame callerMf
            simp
          have hmp_new :
              MemPlaceRel mach₁ destDecl.ty cf.callerBody.layouts (some (.scalar sc0)) mp_d := by
            refine .mk allocId tag baseAddr relOffset ⟨localAlloc.kind, alloc'⟩
              hprov hmis hmeta (mem_live_self_of_updateAllocMachine hu_lt)
              hbase h_no_overflow h_offset hmut' halign
              (by dsimp only; rw [hbsize']; exact h_in_bounds)
              (fun h => nomatch h)
              (fun _ _ _ => by dsimp only; rw [hsz_dest]; exact hinit_i)
              (fun sc' hsc' => by
                injection hsc' with hsc_eq
                injection hsc_eq with hsc_eq'
                subst hsc_eq'
                exact ⟨hsz_dest, hbool_dest, hchar_dest, msc0, hrel0,
                  by dsimp only; rw [hsz_dest]; exact hread_i⟩)
              (fun ek cnt es hk _ => by
                rcases hprim_d with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h] at hk; cases hk))
          have hnew_loc_d :
              LocalRel mach₁ destDecl cf.callerBody.layouts (.init (.scalar sc0))
                (callerMf.locals[destIdx]'hlt_mf_d) := by
            rw [hmls_eq_d]
            exact .indirect (.init (.scalar sc0)) mp_d c_d hcache_d (fun h => nomatch h) hmp_new
          have hfr_caller_mach₁ : FrameRel cf.callerBody mach₁
              { cf.frame with
                blockIdx := cf.returnTarget
                stmtIdx := 0
                locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
              callerMf' :=
            ⟨hfr_caller.body_eq, rfl, by rw [List.length_set, hfr_caller.af_locals_len],
              hfr_caller.mf_locals_size, fun i decl_i slot_i mls_i hdecl_i hslot_i hmls_i => by
              rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
              by_cases hi_d : destIdx = i
              · subst hi_d
                simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot_i
                subst hslot_i
                have hd_eq2 : decl_i = destDecl := by
                  rw [hdecl_d] at hdecl_i; exact Option.some.inj hdecl_i.symm
                subst hd_eq2
                dsimp only [callerMf'] at hmls_i
                rw [Array.getElem?_eq_getElem hlt_mf_d] at hmls_i
                injection hmls_i with hm_eq
                subst hm_eq
                exact hnew_loc_d
              · simp only [hi_d, ↓reduceIte, ← get?_eq_getElem?] at hslot_i
                dsimp only [callerMf'] at hmls_i
                apply (hfr_caller.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_updateAllocMachine_ne hu_lt hget'
                intro mp' hv'
                have hmls_i' : callerMf.locals[i]? = some { value := .live (.indirect mp'), layout := mls_i.layout } := by
                  cases mls_i with
                  | mk val lay => dsimp only at hv' ⊢; rw [hv'] at hmls_i; exact hmls_i
                have hne_prov := hd_callerMf i destIdx mp' mp_d mls_i.layout c_d (Ne.symm hi_d) hmls_i' hmls_d
                rw [hprov] at hne_prov
                exact hne_prov⟩
          have hlinks_mach₁ :
              CallerStackLinksRel rootBody mach₁ cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                restStack callerProts (callerMf' :: restMfs) := by
            cases hlinks_caller with
            | root _ _ _ hrc_r hrp_r _ =>
              exact .root _ callerMf' callerProts hrc_r hrp_r hfr_caller_mach₁
            | cons _ _ cf_next cs_next curP_next callerP_next _ callerMf_next restMfs_next
                hrc_n hdest_n _ hretWf_n hcp_n hpdisj_n hrest_n =>
              have hdisj_rest : ∀ mf ∈ callerMf_next :: restMfs_next,
                  ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
                    (lay : Option Miri.Interpreter.LocalLayout),
                    mf.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
                    mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some allocId := by
                intro mf hmf i mp lay hi
                have hmem_rev : mf ∈ (callerMf_next :: restMfs_next).reverse := List.mem_reverse.mpr hmf
                obtain ⟨f₁, hf₁_lt, rfl⟩ := List.getElem_of_mem hmem_rev
                let f₂ := (callerMf_next :: restMfs_next).reverse.length
                have hne_f : f₁ ≠ f₂ := Nat.ne_of_lt hf₁_lt
                have hf₁_get :
                    (⟨(callerMf_next :: restMfs_next).reverse ++ [callerMf]⟩ : Array _)[f₁]? =
                      some ((callerMf_next :: restMfs_next).reverse[f₁]'hf₁_lt) := by
                  rw [array_getElem?_append_singleton_of_lt _ _ hf₁_lt]
                  exact Array.getElem?_eq_getElem hf₁_lt
                have hf₂_get :
                    (⟨(callerMf_next :: restMfs_next).reverse ++ [callerMf]⟩ : Array _)[f₂]? =
                      some callerMf :=
                  array_getElem?_append_singleton_last (callerMf_next :: restMfs_next).reverse callerMf
                have hne_prov := hdisj_pop.inter_frame f₁ f₂ i destIdx _ callerMf mp mp_d lay c_d
                  hne_f hf₁_get hf₂_get hi hmls_d
                rw [hprov] at hne_prov
                exact hne_prov
              have hdest_n' := hdest_n.of_updateAllocMachine_ne (kind := localAlloc.kind) (alloc' := alloc') hu_lt hget'
                (hdisj_rest callerMf_next List.mem_cons_self)
              have hrest_n' := hrest_n.of_updateAllocMachine_ne (kind := localAlloc.kind) (alloc' := alloc') hu_lt hget' hdisj_rest
              have hretWf_n' :
                  CalleeIndirectRetWf mach₁ cf.callerBody
                    { cf.frame with
                      blockIdx := cf.returnTarget
                      stmtIdx := 0
                      locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                    cf_next callerMf' := by
                intro mp_z lay_z decl_z destDecl_z destIdx_z hz hdecl_z hcf_z hdecl_dz
                dsimp only [callerMf'] at hz
                obtain ⟨hnodup_z, hprim_z, hlay_z, hinit_z, huninit_z⟩ :=
                  hretWf_n mp_z lay_z decl_z destDecl_z destIdx_z hz hdecl_z hcf_z hdecl_dz
                have hnodup_z' : (mach₁.memory.live.toList.map Prod.fst).Nodup := by
                  dsimp [mach₁]
                  rw [updateAllocMachine_live_map_fst_eq hu_lt hget']
                  exact hnodup_z
                refine ⟨hnodup_z', hprim_z, hlay_z, ?_, ?_⟩
                · intro retVal_z hval_z
                  dsimp only at hval_z
                  rw [get?_eq_getElem?, List.getElem?_set] at hval_z
                  by_cases hz_d : destIdx = 0
                  · subst hz_d
                    simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hval_z
                    injection hval_z with hv_eq
                    exact ⟨sc0, hv_eq.symm⟩
                  · simp only [hz_d, ↓reduceIte, ← get?_eq_getElem?] at hval_z
                    exact hinit_z retVal_z hval_z
                · intro hun_z allocId_z tag_z localAlloc_z baseAddr_z off_z hprov_z hlive_z hbase_z hptr_z
                  dsimp only at hun_z
                  rw [get?_eq_getElem?, List.getElem?_set] at hun_z
                  by_cases hz_d : destIdx = 0
                  · subst hz_d
                    simp only [↓reduceIte, hlt_af_d] at hun_z
                    cases hun_z
                  · simp only [hz_d, ↓reduceIte, ← get?_eq_getElem?] at hun_z
                    have hne_prov := hd_callerMf 0 destIdx mp_z mp_d lay_z c_d (Ne.symm hz_d) hz hmls_d
                    have hne_id : allocId ≠ allocId_z := by
                      intro heq
                      apply hne_prov
                      rw [hprov_z, hprov, heq]
                      rfl
                    exact huninit_z hun_z allocId_z tag_z localAlloc_z baseAddr_z off_z hprov_z
                      (mem_live_inv_of_updateAllocMachine hne_id hlive_z) hbase_z hptr_z
              exact .cons cf.callerBody _ cf_next cs_next curP_next callerP_next callerMf'
                callerMf_next restMfs_next hrc_n hdest_n' hfr_caller_mach₁
                hretWf_n' hcp_n hpdisj_n hrest_n'
          have hlinks_post :
              CallerStackLinksRel rootBody mach' cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc0)) }
                restStack callerProts (callerMf' :: restMfs) := by
            apply hlinks_mach₁.of_deallocFrameLocals
            intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
            rcases List.mem_cons.mp hmf with rfl | hmem_rest
            · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
            · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest)
                i j mp₁ mp₂ lay₁ lay₂ hi hj
          have hd_callerMf' : MemoryAllocDisjoint callerMf' := hd_callerMf
          have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
            hdisj_pop.replace_top hd_callerMf' (fun _ _ lay hi => ⟨lay, hi⟩)
          refine .mk callerMf'
            (array_back?_append_singleton restMfs.reverse callerMf')
            hcal_root_post (fun _ => rfl)
            (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, hcp] using hlinks_post.toForall2)
            (by
              have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
              cases hcp_rev
              unfold activeMirBody
              have hrev_post :
                (⟨restMfs.reverse ++ [callerMf']⟩ : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).toList.reverse =
                  callerMf' :: restMfs :=
                array_toList_reverse_append_singleton restMfs callerMf'
              rw [hrev_post]
              exact hlinks_post)
            hdisj_post htb_post
            hvalid_post' hcid_pos hcid_act_post' hcid_bor hbt_post
    | immediate _ imm0 cachedLayout _ hval0 =>
      rcases hval0 with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel0⟩
      · have hsz0 :
            (translateTy decl0.ty (activeMirBody rootBody s).layouts).layout.size ≠
              Miri.ABI.Size.ZERO :=
          fun hz => hzst_init hz hslot0
        rw [returnFromCurrentFrame_of_error_back
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame)
          hback hfr_callee.body_eq hfr_callee.location_eq hbb hcleanup
          (annealControlHooks_returnOperand_uninit_back hback hfr_callee.body_eq hfr_callee.location_eq
            hbb hcleanup hget0 hdecl0 hsz0)]
        exact StepRelMultiFrame.ub _ _
      · have hop0 :
            (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).returnOperand () m =
              (m, .ok (.immediate imm0)) := by
          cases himmRel0 with
          | unit hzero =>
            exact annealControlHooks_returnOperand_zst_unit_back hback hget0 hdecl0 hzero
          | scalar _ msc _ _ _ _ =>
            exact annealControlHooks_returnOperand_scalar_back hback hget0
          | scalarPair _ _ msc₁ msc₂ _ _ _ _ =>
            exact annealControlHooks_returnOperand_scalarPair_back hback hget0
        generalize hrp_callee : calleeMf.returnPlace = rp_callee at hdest
        cases hdest with
        | indirect destIdx destDecl slot_d mp_d c_d rp_callee allocId tag baseAddr relOffset
            localAlloc words hcf hdecl_d hprim_d hslot_d hne_dead hmls_d hrp_or hprov hmis
            hmeta hlive hnodup hbase h_no_overflow h_offset hmut hlen hprovMap hmask_rel
            halign h_in_bounds hmem_rel =>
          have hforall_caller := hlinks_caller.toForall2
          have hfr_caller := list_forall2_head hforall_caller
          obtain ⟨_, mls_d', hlt_af_d, hlt_mf_d, _, hmls_d', hmls_eq_d, hloc_d⟩ :=
            hfr_caller.lookup_local hdecl_d
          have hmls_eq2 : mls_d' = ⟨.live (.indirect mp_d), c_d⟩ := by
            rw [hmls_d] at hmls_d'; exact Option.some.inj hmls_d'.symm
          subst hmls_eq2
          have hcache_d : ∀ l ∈ c_d, l = translateTy destDecl.ty cf.callerBody.layouts :=
            hloc_d.cachedLayout_eq
          have hwrite_af :
              writePlaceValue cf.frame.locals s.memory.borrows cf.destination retVal =
                .ok (cf.frame.locals.set destIdx (.init retVal)) := by
            rw [hcf]; exact writePlaceValue_not_dead_ok hslot_d hne_dead
          have himmRel_dest := hty_compat destIdx destDecl hcf hdecl_d retVal imm0 himmRel0
          obtain ⟨sc, msc, rfl, rfl, hdata, hsz_dest, hbool_dest, hchar_dest⟩ :=
            ImmediateRel.of_primitive_scalar himmRel_dest hprim_d
          obtain ⟨u, hu_lt, hfidx, hget, _⟩ := array_findIdx?_of_nodup_fst hnodup hlive
          have hbnd :
              relOffset.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
                localAlloc.allocation.byteSize.bytes.toNat := by
            rw [← hsz_dest]; exact h_in_bounds
          obtain ⟨alloc', words', hw, hbsize', hlen', hmut', hprov', hmask', _, _, hinit_i, hread_i⟩ :=
            alloc_writeScalar_at_offset_mask hdata hlen hmut hprovMap hmask_rel hbnd
          have hget' : m₀.machine.memory.live[u]'hu_lt = (allocId, localAlloc) := by
            have h1 := Array.getElem?_eq_getElem hu_lt
            exact Option.some.inj (h1.symm.trans hget)
          have hw_cast :
              Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOffset.bytes + Miri.ABI.Size.ZERO.bytes))
                  (@Miri.Memory.Scalar.size AnnealProv (@Miri.Memory.Scalar.fromScalarInt AnnealProv msc)))
                (@Miri.Memory.Scalar.fromScalarInt AnnealProv msc) localAlloc.allocation =
              EStateM.Result.ok () alloc' := by
            have h_off : Miri.ABI.Size.ofBytes (relOffset.bytes + Miri.ABI.Size.ZERO.bytes) = relOffset := by
              cases relOffset; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
            rw [h_off]; exact hw
          let m₁ : AnnealStepState := { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }
          have hw_ind :=
            annealWriteIndirectImmediate_scalar_ok
              (m := m₁) (mpOff := relOffset)
              (fieldLay := translateTy destDecl.ty cf.callerBody.layouts)
              (relOffset := Miri.ABI.Size.ZERO)
              (alloc' := alloc') (u := u) (localAlloc := localAlloc)
              hprov hbase h_offset hu_lt hfidx hget' hw_cast
          let mach₁ := updateAllocMachine m₀.machine u allocId localAlloc.kind alloc'
          let m₂ : AnnealStepState :=
            { stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩, machine := mach₁ }
          have hcopy :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).copyReturn ()
                (.immediate (.scalar (.fromScalarInt msc))) calleeMf.returnPlace m₁ =
              (m₂, .ok ()) := by
            rw [hrp_callee]
            rcases hrp_or with rfl | rfl
            · unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
              dsimp only [m₁, Miri.Interpreter.runRvalue, bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure]
              rw [hw_ind]
            · have hget_d := frame_getLocal_of_getElem? callerMf destIdx
                ⟨.live (.indirect mp_d), c_d⟩ hmls_d
              have hne_false :
                  (restMfs.length !=
                    (⟨restMfs.reverse ++ [callerMf]⟩ :
                      Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                  false := by simp
              unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
                Miri.Interpreter.Stack.currentFrame?
              dsimp only [m₁, Miri.Interpreter.runRvalue, bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure]
              simp +zetaHave only [array_back?_append_singleton, hne_false,
                Bool.false_eq_true, ↓reduceIte, hget_d]
              rw [hw_ind]
          have hlive_callee₁ : AllSlotsAllocLive mach₁.memory calleeMf.locals.toList :=
            hfr_callee.allSlotsAllocLive.of_updateAllocMachine hu_lt hget'
          have hclean :
              (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
                false calleeMf m₂ =
              ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
                 machine := { mach₁ with memory := deallocFrameLocals mach₁.memory calleeMf } },
               .ok .normal) := by
            unfold annealControlHooksLM4_1
            dsimp only
            rw [cleanupStackFrame_callee_goto
              (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
              ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ mach₁.memory calleeMf
              hretCont (hva calleeMf hback)
              hlive_callee₁ hd_callee.slotsAllocDisjoint]
          by_cases hdiv_true : cf.isDiverging = true
          · simp only [hdiv_true, ↓reduceIte] at hretCont ⊢
            rw [returnFromCurrentFrame_lm4_1_callee_div_ub hback hfr_callee.body_eq hfr_callee.location_eq
              hbb hcleanup hretCont hop0 hpop hcopy hclean]
            dsimp only [Except.map]
            exact StepRelMultiFrame.ub _ _
          have hdiv_false : cf.isDiverging = false := Bool.eq_false_iff.mpr hdiv_true
          simp only [hdiv_false, Bool.false_eq_true, ↓reduceIte] at hretCont ⊢
          simp only [hwrite_af, restoreCallerProtectors]
          rw [returnFromCurrentFrame_lm4_1_callee_ok hback hfr_callee.body_eq hfr_callee.location_eq
            hbb hcleanup hretCont hop0 hpop hcopy hclean]
          dsimp only [Except.map]
          apply StepRelMultiFrame.step
          let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { callerMf with location := .mir ⟨cf.returnTarget, 0⟩ }
          let mach' : AnnealMachine :=
            { mach₁ with memory := deallocFrameLocals mach₁.memory calleeMf }
          have hd_callerMf : MemoryAllocDisjoint callerMf := by
            apply hdisj_pop.intra_frame callerMf
            simp
          have hmp_new :
              MemPlaceRel mach₁ destDecl.ty cf.callerBody.layouts (some (.scalar sc)) mp_d := by
            refine .mk allocId tag baseAddr relOffset ⟨localAlloc.kind, alloc'⟩
              hprov hmis hmeta (mem_live_self_of_updateAllocMachine hu_lt)
              hbase h_no_overflow h_offset hmut' halign
              (by dsimp only; rw [hbsize']; exact h_in_bounds)
              (fun h => nomatch h)
              (fun _ _ _ => by dsimp only; rw [hsz_dest]; exact hinit_i)
              (fun sc' hsc' => by
                injection hsc' with hsc_eq
                injection hsc_eq with hsc_eq'
                subst hsc_eq'
                exact ⟨hsz_dest, hbool_dest, hchar_dest, msc, hdata,
                  by dsimp only; rw [hsz_dest]; exact hread_i⟩)
              (fun ek cnt es hk _ => by
                rcases hprim_d with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h] at hk; cases hk))
          have hnew_loc_d :
              LocalRel mach₁ destDecl cf.callerBody.layouts (.init (.scalar sc))
                (callerMf.locals[destIdx]'hlt_mf_d) := by
            rw [hmls_eq_d]
            exact .indirect (.init (.scalar sc)) mp_d c_d hcache_d (fun h => nomatch h) hmp_new
          have hfr_caller_mach₁ : FrameRel cf.callerBody mach₁
              { cf.frame with
                blockIdx := cf.returnTarget
                stmtIdx := 0
                locals := cf.frame.locals.set destIdx (.init (.scalar sc)) }
              callerMf' :=
            ⟨hfr_caller.body_eq, rfl, by rw [List.length_set, hfr_caller.af_locals_len],
              hfr_caller.mf_locals_size, fun i decl_i slot_i mls_i hdecl_i hslot_i hmls_i => by
              rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
              by_cases hi_d : destIdx = i
              · subst hi_d
                simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot_i
                subst hslot_i
                have hd_eq2 : decl_i = destDecl := by
                  rw [hdecl_d] at hdecl_i; exact Option.some.inj hdecl_i.symm
                subst hd_eq2
                dsimp only [callerMf'] at hmls_i
                rw [Array.getElem?_eq_getElem hlt_mf_d] at hmls_i
                injection hmls_i with hm_eq
                subst hm_eq
                exact hnew_loc_d
              · simp only [hi_d, ↓reduceIte, ← get?_eq_getElem?] at hslot_i
                dsimp only [callerMf'] at hmls_i
                apply (hfr_caller.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_updateAllocMachine_ne hu_lt hget'
                intro mp' hv'
                have hmls_i' : callerMf.locals[i]? = some { value := .live (.indirect mp'), layout := mls_i.layout } := by
                  cases mls_i with
                  | mk val lay => dsimp only at hv' ⊢; rw [hv'] at hmls_i; exact hmls_i
                have hne_prov := hd_callerMf i destIdx mp' mp_d mls_i.layout c_d (Ne.symm hi_d) hmls_i' hmls_d
                rw [hprov] at hne_prov
                exact hne_prov⟩
          have hlinks_mach₁ :
              CallerStackLinksRel rootBody mach₁ cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc)) }
                restStack callerProts (callerMf' :: restMfs) := by
            cases hlinks_caller with
            | root _ _ _ hrc_r hrp_r _ =>
              exact .root _ callerMf' callerProts hrc_r hrp_r hfr_caller_mach₁
            | cons _ _ cf_next cs_next curP_next callerP_next _ callerMf_next restMfs_next
                hrc_n hdest_n _ hretWf_n hcp_n hpdisj_n hrest_n =>
              have hdisj_rest : ∀ mf ∈ callerMf_next :: restMfs_next,
                  ∀ (i : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
                    (lay : Option Miri.Interpreter.LocalLayout),
                    mf.locals[i]? = some { value := .live (.indirect mp), layout := lay } →
                    mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some allocId := by
                intro mf hmf i mp lay hi
                have hmem_rev : mf ∈ (callerMf_next :: restMfs_next).reverse := List.mem_reverse.mpr hmf
                obtain ⟨f₁, hf₁_lt, rfl⟩ := List.getElem_of_mem hmem_rev
                let f₂ := (callerMf_next :: restMfs_next).reverse.length
                have hne_f : f₁ ≠ f₂ := Nat.ne_of_lt hf₁_lt
                have hf₁_get :
                    (⟨(callerMf_next :: restMfs_next).reverse ++ [callerMf]⟩ : Array _)[f₁]? =
                      some ((callerMf_next :: restMfs_next).reverse[f₁]'hf₁_lt) := by
                  rw [array_getElem?_append_singleton_of_lt _ _ hf₁_lt]
                  exact Array.getElem?_eq_getElem hf₁_lt
                have hf₂_get :
                    (⟨(callerMf_next :: restMfs_next).reverse ++ [callerMf]⟩ : Array _)[f₂]? =
                      some callerMf :=
                  array_getElem?_append_singleton_last (callerMf_next :: restMfs_next).reverse callerMf
                have hne_prov := hdisj_pop.inter_frame f₁ f₂ i destIdx _ callerMf mp mp_d lay c_d
                  hne_f hf₁_get hf₂_get hi hmls_d
                rw [hprov] at hne_prov
                exact hne_prov
              have hdest_n' := hdest_n.of_updateAllocMachine_ne (kind := localAlloc.kind) (alloc' := alloc') hu_lt hget'
                (hdisj_rest callerMf_next List.mem_cons_self)
              have hrest_n' := hrest_n.of_updateAllocMachine_ne (kind := localAlloc.kind) (alloc' := alloc') hu_lt hget' hdisj_rest
              have hretWf_n' :
                  CalleeIndirectRetWf mach₁ cf.callerBody
                    { cf.frame with
                      blockIdx := cf.returnTarget
                      stmtIdx := 0
                      locals := cf.frame.locals.set destIdx (.init (.scalar sc)) }
                    cf_next callerMf' := by
                intro mp_z lay_z decl_z destDecl_z destIdx_z hz hdecl_z hcf_z hdecl_dz
                dsimp only [callerMf'] at hz
                obtain ⟨hnodup_z, hprim_z, hlay_z, hinit_z, huninit_z⟩ :=
                  hretWf_n mp_z lay_z decl_z destDecl_z destIdx_z hz hdecl_z hcf_z hdecl_dz
                have hnodup_z' : (mach₁.memory.live.toList.map Prod.fst).Nodup := by
                  dsimp [mach₁]
                  rw [updateAllocMachine_live_map_fst_eq hu_lt hget']
                  exact hnodup_z
                refine ⟨hnodup_z', hprim_z, hlay_z, ?_, ?_⟩
                · intro retVal_z hval_z
                  dsimp only at hval_z
                  rw [get?_eq_getElem?, List.getElem?_set] at hval_z
                  by_cases hz_d : destIdx = 0
                  · subst hz_d
                    simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hval_z
                    injection hval_z with hv_eq
                    exact ⟨sc, hv_eq.symm⟩
                  · simp only [hz_d, ↓reduceIte, ← get?_eq_getElem?] at hval_z
                    exact hinit_z retVal_z hval_z
                · intro hun_z allocId_z tag_z localAlloc_z baseAddr_z off_z hprov_z hlive_z hbase_z hptr_z
                  dsimp only at hun_z
                  rw [get?_eq_getElem?, List.getElem?_set] at hun_z
                  by_cases hz_d : destIdx = 0
                  · subst hz_d
                    simp only [↓reduceIte, hlt_af_d] at hun_z
                    cases hun_z
                  · simp only [hz_d, ↓reduceIte, ← get?_eq_getElem?] at hun_z
                    have hne_prov := hd_callerMf 0 destIdx mp_z mp_d lay_z c_d (Ne.symm hz_d) hz hmls_d
                    have hne_id : allocId ≠ allocId_z := by
                      intro heq
                      apply hne_prov
                      rw [hprov_z, hprov, heq]
                      rfl
                    exact huninit_z hun_z allocId_z tag_z localAlloc_z baseAddr_z off_z hprov_z
                      (mem_live_inv_of_updateAllocMachine hne_id hlive_z) hbase_z hptr_z
              exact .cons cf.callerBody _ cf_next cs_next curP_next callerP_next callerMf'
                callerMf_next restMfs_next hrc_n hdest_n' hfr_caller_mach₁
                hretWf_n' hcp_n hpdisj_n hrest_n'
          have hlinks_post :
              CallerStackLinksRel rootBody mach' cf.callerBody
                { cf.frame with
                  blockIdx := cf.returnTarget
                  stmtIdx := 0
                  locals := cf.frame.locals.set destIdx (.init (.scalar sc)) }
                restStack callerProts (callerMf' :: restMfs) := by
            apply hlinks_mach₁.of_deallocFrameLocals
            intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
            rcases List.mem_cons.mp hmf with rfl | hmem_rest
            · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
            · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest)
                i j mp₁ mp₂ lay₁ lay₂ hi hj
          have hd_callerMf' : MemoryAllocDisjoint callerMf' := hd_callerMf
          have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
            hdisj_pop.replace_top hd_callerMf' (fun _ _ lay hi => ⟨lay, hi⟩)
          refine .mk callerMf'
            (array_back?_append_singleton restMfs.reverse callerMf')
            hcal_root_post (fun _ => rfl)
            (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, hcp] using hlinks_post.toForall2)
            (by
              have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
              cases hcp_rev
              unfold activeMirBody
              have hrev_post :
                (⟨restMfs.reverse ++ [callerMf']⟩ : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).toList.reverse =
                  callerMf' :: restMfs :=
                array_toList_reverse_append_singleton restMfs callerMf'
              rw [hrev_post]
              exact hlinks_post)
            hdisj_post htb_post
            hvalid_post' hcid_pos hcid_act_post' hcid_bor hbt_post
        | immediate destIdx destDecl slot_d imm_d cachedLayout_d hcf hdecl_d hslot_d hne_dead hmls_d =>
            have hforall_caller := hlinks_caller.toForall2
            have hfr_caller := list_forall2_head hforall_caller
            obtain ⟨_, mls_d', hlt_af_d, hlt_mf_d, _, hmls_d', hmls_eq_d, hloc_d⟩ :=
              hfr_caller.lookup_local hdecl_d
            have hmls_eq2 : mls_d' = ⟨.live (.immediate imm_d), cachedLayout_d⟩ := by
              rw [hmls_d] at hmls_d'; exact Option.some.inj hmls_d'.symm
            subst hmls_eq2
            have hcache_d : ∀ l ∈ cachedLayout_d, l = translateTy destDecl.ty cf.callerBody.layouts :=
              hloc_d.cachedLayout_eq
            have hwrite_af :
                writePlaceValue cf.frame.locals s.memory.borrows cf.destination retVal =
                  .ok (cf.frame.locals.set destIdx (.init retVal)) := by
              unfold writePlaceValue
              rw [hcf]
              dsimp only
              rw [hslot_d]
              cases slot_d with
              | dead => exact False.elim (hne_dead rfl)
              | uninit =>
                dsimp only
                rw [set?_eq_some_set hlt_af_d (.init retVal)]
              | init _ =>
                dsimp only
                rw [set?_eq_some_set hlt_af_d (.init retVal)]
            let callerMf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
              { callerMf with
                locals := callerMf.locals.set destIdx
                  { callerMf.locals[destIdx]'hlt_mf_d with value := .live (.immediate imm0) } hlt_mf_d }
            have hcopy :
                (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).copyReturn ()
                  (.immediate imm0)
                  calleeMf.returnPlace
                  { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ } =
                ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ }, .ok ()) := by
              rw [hrp_callee]
              have hget_d := frame_getLocal_of_getElem? callerMf destIdx
                ⟨.live (.immediate imm_d), cachedLayout_d⟩ hmls_d
              have hrep_d := frame_replaceLocalValue_of_lt callerMf destIdx hlt_mf_d
                (.live (.immediate imm0))
              unfold annealControlHooksLM4_1 annealCopyReturnLM4_1
                Miri.Interpreter.Stack.currentFrame?
              dsimp only [Miri.Interpreter.runRvalue, bind, pure, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.run, EStateM.pure]
              simp +zetaHave only [array_back?_append_singleton,
                hget_d, hrep_d]
              have hne_false :
                  (restMfs.length !=
                    (⟨restMfs.reverse ++ [callerMf]⟩ :
                      Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1) =
                  false := by
                simp
              have hidx_lt :
                  (⟨restMfs.reverse ++ [callerMf]⟩ :
                    Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 <
                    (⟨restMfs.reverse ++ [callerMf]⟩ :
                      Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size := by
                simp
              simp +zetaHave only [hne_false, Bool.false_eq_true, ↓reduceIte, hidx_lt, ↓reduceDIte]
              congr 3
              apply Array.ext'
              simp
              rfl
            have hclean :
                (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
                  false calleeMf { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ } =
                ({ stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩
                   machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
                 .ok .normal) := by
              unfold annealControlHooksLM4_1
              dsimp only
              rw [cleanupStackFrame_callee_goto
                (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
                ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ m₀.machine.memory calleeMf
                hretCont (hva calleeMf hback)
                hfr_callee.allSlotsAllocLive hd_callee.slotsAllocDisjoint]
            by_cases hdiv_true : cf.isDiverging = true
            · simp only [hdiv_true, ↓reduceIte] at hretCont ⊢
              rw [returnFromCurrentFrame_lm4_1_callee_div_ub hback hfr_callee.body_eq hfr_callee.location_eq
                hbb hcleanup hretCont hop0 hpop hcopy hclean]
              dsimp only [Except.map]
              exact StepRelMultiFrame.ub _ _
            have hdiv_false : cf.isDiverging = false := Bool.eq_false_iff.mpr hdiv_true
            simp only [hdiv_false, Bool.false_eq_true, ↓reduceIte] at hretCont ⊢
            rw [hwrite_af]
            dsimp only [restoreCallerProtectors]
            rw [returnFromCurrentFrame_lm4_1_callee_ok hback hfr_callee.body_eq hfr_callee.location_eq
              hbb hcleanup hretCont hop0 hpop hcopy hclean]
            dsimp only [Except.map]
            apply StepRelMultiFrame.step
            let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
              { callerMf₁ with location := .mir ⟨cf.returnTarget, 0⟩ }
            let mach' : AnnealMachine :=
              { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf }
            have himmRel_d : ImmediateRel destDecl.ty cf.callerBody.layouts retVal imm0 :=
              hty_compat destIdx destDecl hcf hdecl_d retVal imm0 himmRel0
            have hnew_loc_d :
                LocalRel m₀.machine destDecl cf.callerBody.layouts (.init retVal)
                  { callerMf.locals[destIdx]'hlt_mf_d with value := .live (.immediate imm0) } := by
              rw [hmls_eq_d]
              exact .immediate (.init retVal) imm0 cachedLayout_d hcache_d
                (Or.inr ⟨retVal, rfl, himmRel_d⟩)
            have hfr_caller₁ :=
              hfr_caller.update_local hdecl_d (.init retVal) (.live (.immediate imm0)) hnew_loc_d
            have hfr_caller_loc :
                FrameRel cf.callerBody m₀.machine
                  { cf.frame with
                    blockIdx := cf.returnTarget
                    stmtIdx := 0
                    locals := cf.frame.locals.set destIdx (.init retVal) }
                  callerMf' :=
              ⟨hfr_caller₁.body_eq, rfl, hfr_caller₁.af_locals_len,
               hfr_caller₁.mf_locals_size, hfr_caller₁.locals_rel⟩
            have hlinks_updated :
                CallerStackLinksRel rootBody m₀.machine cf.callerBody
                  { cf.frame with
                    blockIdx := cf.returnTarget
                    stmtIdx := 0
                    locals := cf.frame.locals.set destIdx (.init retVal) }
                  restStack callerProts (callerMf' :: restMfs) := by
              refine hlinks_caller.update_top_frame rfl rfl rfl hfr_caller_loc ?_
              intro mp_z lay_z hz
              dsimp only [callerMf', callerMf₁] at hz
              by_cases hz_d : destIdx = 0
              · subst hz_d
                rw [Array.getElem?_set_self] at hz
                cases hz
              · rw [Array.getElem?_set_ne _ hz_d] at hz
                refine ⟨⟨lay_z, hz⟩, Or.inl ?_⟩
                dsimp only
                rw [get?_eq_getElem?, get?_eq_getElem?, List.getElem?_set_ne hz_d]
            have hlinks_post :
                CallerStackLinksRel rootBody mach' cf.callerBody
                  { cf.frame with
                    blockIdx := cf.returnTarget
                    stmtIdx := 0
                    locals := cf.frame.locals.set destIdx (.init retVal) }
                  restStack callerProts (callerMf' :: restMfs) := by
              apply hlinks_updated.of_deallocFrameLocals
              intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
              rcases List.mem_cons.mp hmf with rfl | hmem_rest
              · dsimp only [callerMf', callerMf₁] at hi
                by_cases hi_d : destIdx = i
                · subst hi_d
                  rw [Array.getElem?_set_self] at hi
                  cases hi
                · rw [Array.getElem?_set_ne _ hi_d] at hi
                  exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
              · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest)
                  i j mp₁ mp₂ lay₁ lay₂ hi hj
            have hd_callerMf' : MemoryAllocDisjoint callerMf' := by
              have hd_callerMf : MemoryAllocDisjoint callerMf := by
                apply hdisj_pop.intra_frame callerMf
                simp
              apply MemoryAllocDisjoint.mono_immediate hd_callerMf
              intro k
              by_cases hk : destIdx = k
              · subst hk
                right
                exact ⟨imm0, (callerMf.locals[destIdx]'hlt_mf_d).layout, by
                  dsimp only [callerMf', callerMf₁]; rw [Array.getElem?_set_self]⟩
              · left
                dsimp only [callerMf', callerMf₁]
                rw [Array.getElem?_set_ne _ hk]
            have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ := by
              apply hdisj_pop.replace_top hd_callerMf'
              intro i mp lay hi
              dsimp only [callerMf', callerMf₁] at hi
              by_cases hi_d : destIdx = i
              · subst hi_d
                rw [Array.getElem?_set_self] at hi
                cases hi
              · rw [Array.getElem?_set_ne _ hi_d] at hi
                exact ⟨lay, hi⟩
            refine .mk callerMf'
              (array_back?_append_singleton restMfs.reverse callerMf')
              hcal_root_post (fun _ => rfl)
              (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, hcp] using hlinks_post.toForall2)
              (by
                have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
                cases hcp_rev
                unfold activeMirBody
                have hrev_post :
                  (⟨restMfs.reverse ++ [callerMf']⟩ : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).toList.reverse =
                    callerMf' :: restMfs :=
                  array_toList_reverse_append_singleton restMfs callerMf'
                rw [hrev_post]
                exact hlinks_post)
              hdisj_post htb_post
              hvalid_post' hcid_pos hcid_act_post' hcid_bor hbt_post

abbrev step_terminator_return_callee_immediate_simulation :=
  @step_terminator_return_callee_simulation

/-- **Theorem 4b (`step_terminator_unwindResume_callee_simulation`)**:
At arbitrary stack depth (`s.memory.callStack = cf :: restStack`) under
`MultiFrameStateRel rootBody s m`, executing `TerminatorKind.unwindResume` at a
cleanup basic block (`bb.isCleanup = true`) of the active callee frame:
* `_0` is required to be live (`hlive0`): Stage-1 never inspects `_0` while
  unwinding, whereas `lean-miri`'s `returnOperand` (canonical `localToOp 0`)
  faults on a `.dead` `_0`; with `_0` live, `returnOperand` succeeds even if `_0`
  is `.uninit` on a non-ZST return type;
* when `cf.returnUnwind = .unreachable`, both Stage-1 `Trusted`
  (`unwindFromCallStack` at `Terminators.lean:642`, `.faulted .ub`) and
  `lean-miri` (`ControlFlow.unwindToBlock` at `ControlFlow.lean:46-47`,
  `.undefinedBehavior "unwinding past a frame that does not allow unwinding"`)
  fault with undefined behavior (`StepRelMultiFrame.ub`);
* when `cf.returnUnwind = .cleanup cleanupBb`, both Stage-1 `Trusted`
  (`unwindFromCallStack` at `Terminators.lean:645-653`) and `lean-miri`
  (`ControlFlow.returnFromCurrentFrame ... true` + `unwindToBlock` at
  `ControlFlow.lean:45`) pop the callee frame, deallocate its `.indirect` stack
  locals (`deallocFrameLocals`), release its active `CallId` protectors
  (`restoreCallerProtectors cf` = `releaseCallProtectors 1 (cf :: restStack) s.memory.activeProtectors`
  and `popFrameBorrowTracker`), leave `cf.destination` untouched, and step to
  `MultiFrameStateRel`-related states at `(cleanupBb, 0)` in `cf.callerBody`.

Not covered here: `cf.returnUnwind = .continue_` (Stage-1 pops through several
frames in a single step, see `unwindFromCallStack_running_releaseCallProtectors`,
whereas `lean-miri` unwinds one frame per step) and `.terminate` (Stage-1
`.halted .abort` vs. the hooks' unsupported `unwindTerminate`); unwinding out of
the root frame is a certified divergence
(`step_terminator_unwindResume_root_panic_vs_ub_divergence`). -/
theorem step_terminator_unwindResume_callee_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {cf : SavedCallerFrame} {restStack : List SavedCallerFrame}
    (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = cf :: restStack)
    (hva : ∀ tf, m.stack.frames.back? = some tf → tf.vaList = #[])
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = true)
    (hterm : bb.terminator.kind = .unwindResume)
    (hdecl0 : get? (activeMirBody rootBody s).localDecls 0 = some decl0)
    (hlive0 : get? s.frame.locals 0 ≠ some .dead)
    (hunwind :
      cf.returnUnwind = .unreachable ∨
        ∃ cleanupBb, cf.returnUnwind = .cleanup cleanupBb)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  rcases hstate with
    ⟨_, _, _, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  generalize hprots : s.memory.activeProtectors = prots at hlinks hvalid hcid_act hbt
  generalize hcur : activeMirBody rootBody s = curBody at hlinks
  rw [hstack] at hlinks hbt
  cases hlinks with
  | cons _ _ _ _ curFrameProts callerProts calleeMf callerMf restMfs
      hretCont _ hfr_callee _ hcp _ hlinks_caller =>
    subst hcur
    have harr := array_eq_of_toList_reverse_cons hmfs
    have hback : m.stack.frames.back? = some calleeMf := by rw [harr]; simp
    have harr_two :
        m.stack.frames = ⟨( restMfs.reverse ++ [callerMf] ) ++ [calleeMf]⟩ := by
      rw [harr]
      apply Array.ext'
      simp [List.reverse_cons]
    let poppedFrame := annealPoppedFrameState s
    have hpopped_eq :
        poppedFrame =
          poppedCalleeFrameState s.memory.borrows (curFrameProts ++ callerProts)
            (callerRestoredProtectors [cf]) := by
      dsimp only [poppedFrame, annealPoppedFrameState]
      rw [hstack, hprots]
    let bt' := popFrameBorrowTracker poppedFrame m.machine.borrowTracker
    let m₀ : AnnealStepState :=
      { stack := m.stack, machine := { m.machine with borrowTracker := bt' } }
    have hbt_post :
        BorrowTrackerStackRel s.memory.borrows
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors)
          restStack bt' := by
      dsimp only [bt']
      rw [hpopped_eq]
      exact hbt.of_popFrame
    have hfr_callee := hfr_callee.of_borrowTracker (bt' := bt')
    have hlinks_caller := hlinks_caller.of_borrowTracker (bt' := bt')
    obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hfr_callee.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? calleeMf 0 mls0 hmls0
    have hop0 :
        ∃ op0,
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).returnOperand () m =
            (m, .ok op0) := by
      cases hloc0 with
      | dead _ _ => exact False.elim (hlive0 hslot0)
      | immediate _ imm0 _ _ _ =>
        exact ⟨.immediate imm0,
          annealControlHooks_returnOperand_cleanup_live_back hback hfr_callee.body_eq
            hfr_callee.location_eq hbb hcleanup hget0 hdecl0⟩
      | indirect _ mp0 _ _ _ _ =>
        exact ⟨.indirect mp0,
          annealControlHooks_returnOperand_cleanup_live_back hback hfr_callee.body_eq
            hfr_callee.location_eq hbb hcleanup hget0 hdecl0⟩
    obtain ⟨op0, hop0⟩ := hop0
    have hpop :
        (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).popFrame () m =
          ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }, .ok calleeMf) :=
      annealPopFrameLM4_1_callee_append_singleton harr_two
    have hd_callee : MemoryAllocDisjoint calleeMf := by
      apply hdisj.intra_frame calleeMf
      rw [harr]; simp
    have hdisj_orig :
        MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ := by
      rw [← harr]; exact hdisj
    have hdisj_pop : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ :=
      hdisj_orig.pop_top
    have hclean :
        (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
          true calleeMf { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ } =
        ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
           machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
         .ok .normal) := by
      unfold annealControlHooksLM4_1
      dsimp only
      rw [cleanupStackFrame_callee_goto_any_unwinding
        (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
        ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ m₀.machine.memory true calleeMf
        hretCont (hva calleeMf hback)
        hfr_callee.allSlotsAllocLive hd_callee.slotsAllocDisjoint]
    rw [stepMirFn_activeMirBody_eq rootBody s hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
    rw [miri_step_at_terminator_multiFrame hback hfr_callee.body_eq hfr_callee.location_eq hbb hstmt_none]
    unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, hstack]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure, unwindFromCallStack, restoreCallerProtectors]
    rcases hunwind with hunreach | ⟨cleanupBb, hclean_bb⟩
    · rw [hunreach] at hretCont ⊢
      dsimp only [translateUnwindAction] at hretCont
      rw [returnFromCurrentFrame_lm4_1_unwind_unreachable_ub harr hfr_callee.body_eq
        hfr_callee.location_eq hbb hcleanup hretCont hop0 hpop hclean]
      dsimp only [Except.map]
      exact StepRelMultiFrame.ub _ _
    · rw [hclean_bb] at hretCont ⊢
      dsimp only [translateUnwindAction] at hretCont
      rw [returnFromCurrentFrame_lm4_1_unwind_cleanup_ok harr hfr_callee.body_eq
        hfr_callee.location_eq hbb hcleanup hretCont hop0 hpop hclean]
      dsimp only [Except.map]
      apply StepRelMultiFrame.step
      let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { callerMf with location := .mir ⟨cleanupBb, 0⟩ }
      have hfr_caller : FrameRel cf.callerBody m₀.machine cf.frame callerMf := by
        have hforall_c := hlinks_caller.toForall2
        cases hforall_c with
        | cons hfr _ => exact hfr
      have hfr_caller' :
          FrameRel cf.callerBody m₀.machine
            { cf.frame with blockIdx := cleanupBb, stmtIdx := 0 }
            callerMf' :=
        ⟨hfr_caller.body_eq, rfl, hfr_caller.af_locals_len, hfr_caller.mf_locals_size, hfr_caller.locals_rel⟩
      have hlinks_updated :
          CallerStackLinksRel rootBody m₀.machine cf.callerBody
            { cf.frame with blockIdx := cleanupBb, stmtIdx := 0 }
            restStack callerProts (callerMf' :: restMfs) :=
        hlinks_caller.update_top_frame rfl rfl rfl hfr_caller'
          (fun mp0 lay0 h0 => ⟨⟨lay0, h0⟩, Or.inl rfl⟩)
      have hlinks_post :
          CallerStackLinksRel rootBody
            { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf }
            cf.callerBody
            { cf.frame with blockIdx := cleanupBb, stmtIdx := 0 }
            restStack callerProts (callerMf' :: restMfs) := by
        apply hlinks_updated.of_deallocFrameLocals
        intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
        rcases List.mem_cons.mp hmf with rfl | hmem_rest
        · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
        · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest)
            i j mp₁ mp₂ lay₁ lay₂ hi hj
      have hd_callerMf' : MemoryAllocDisjoint callerMf' := by
        have hd_callerMf : MemoryAllocDisjoint callerMf := by
          apply hdisj_pop.intra_frame callerMf
          simp
        exact hd_callerMf
      have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ := by
        apply hdisj_pop.replace_top hd_callerMf'
        intro i mp lay hi
        exact ⟨lay, hi⟩
      have hvalid_post : ActiveProtectorsValid s.memory.borrows callerProts := by
        apply hvalid.mono_protectors
        intro cid hcid
        exact natListContainsBool_append_right curFrameProts callerProts cid hcid
      have hcid_act_post : ∀ cid ∈ callerProts, cid < s.memory.nextProtector := by
        intro cid hcid
        exact hcid_act cid (List.mem_append_right curFrameProts hcid)
      have hcal_root_post :
          restStack = [] →
            some cf.callerBody = none ∨ some cf.callerBody = some rootBody := by
        intro hnil
        subst hnil
        cases hlinks_caller with
        | root _ _ _ _ _ _ => exact Or.inr rfl
      have hvalid_post' :
          ActiveProtectorsValid s.memory.borrows
            (match cf.callerProtector with
             | some protId => protId :: cf.calleeProtectors
             | none => cf.calleeProtectors) := by
        have hcp_rev : callerProts =
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors) := hcp.symm
        rw [← hcp_rev]; exact hvalid_post
      have hcid_act_post' :
          ∀ cid ∈ (match cf.callerProtector with
                   | some protId => protId :: cf.calleeProtectors
                   | none => cf.calleeProtectors),
            cid < s.memory.nextProtector := by
        have hcp_rev : callerProts =
          (match cf.callerProtector with
           | some protId => protId :: cf.calleeProtectors
           | none => cf.calleeProtectors) := hcp.symm
        rw [← hcp_rev]; exact hcid_act_post
      have htb_post :
          TreeBorrowsRel s.memory.borrows
            (match cf.callerProtector with
             | some protId => protId :: cf.calleeProtectors
             | none => cf.calleeProtectors)
            (basedNormalTree s.memory.borrows
              (match cf.callerProtector with
               | some protId => protId :: cf.calleeProtectors
               | none => cf.calleeProtectors)) :=
        htb.change_protectors _
      refine .mk callerMf'
        (array_back?_append_singleton restMfs.reverse callerMf')
        hcal_root_post (fun _ => rfl)
        (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, hcp] using hlinks_post.toForall2)
        (by
          have hcp_rev : callerProts = (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) := hcp.symm
          cases hcp_rev
          unfold activeMirBody
          have hrev_post :
            (⟨restMfs.reverse ++ [callerMf']⟩ : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).toList.reverse =
              callerMf' :: restMfs :=
            array_toList_reverse_append_singleton restMfs callerMf'
          rw [hrev_post]
          exact hlinks_post)
        hdisj_post htb_post
        hvalid_post' hcid_pos hcid_act_post' hcid_bor hbt_post


/-- On a single-frame `lean-miri` stack (`m.stack.frames = #[rootMf]`) whose top
frame sits in a cleanup block, `ControlFlow.returnFromCurrentFrame hooks () true m`
(the `UnwindResume` transition) faults with
`.undefinedBehavior "unwinding past the topmost stack frame"` for any control hooks. -/
theorem returnFromCurrentFrame_unwind_root_ub
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m : AnnealStepState}
    {rootMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    (hframes : m.stack.frames = #[rootMf])
    (hbody : rootMf.body = translateBody body)
    (hloc : rootMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () true m =
      (m, .error (.undefinedBehavior "unwinding past the topmost stack frame")) := by
  have hback : m.stack.frames.back? = some rootMf := by rw [hframes]; rfl
  have hsize : (m.stack.frames.size == 1) = true := by rw [hframes]; rfl
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, hcleanup, hsize]

/-- **Divergence (`step_terminator_unwindResume_root_panic_vs_ub_divergence`)**:
executing `TerminatorKind.unwindResume` in a cleanup block of the *root* frame
(`s.memory.callStack = []`) under `MultiFrameStateRel rootBody s m`:
1. Stage-1 `Trusted` halts with a panic outcome
   (`unwindFromCallStack [] _ = .halted .panic`, `Terminators.lean:633`, so
   `stepMirFn rootBody s = MirStepNode.retOutcome .panic`);
2. `lean-miri` faults with undefined behavior, because
   `ControlFlow.returnFromCurrentFrame` refuses to unwind a single-frame stack
   (`.undefinedBehavior "unwinding past the topmost stack frame"`).
This complements `step_terminator_unwindResume_callee_simulation`, which covers
non-root callee frames whose saved caller catches (`.cleanup`) or forbids
(`.unreachable`) the unwind. -/
theorem step_terminator_unwindResume_root_panic_vs_ub_divergence
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = .nil)
    (hphase : ∀ p, rootBody.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? rootBody.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = true)
    (hterm : bb.terminator.kind = .unwindResume)
    (fnPtrs : List FnPtrEntry := .nil) :
    stepMirFn rootBody s = MirStepNode.retOutcome .panic ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
        fnPtrs)
      () m).2 =
      .error (.undefinedBehavior "unwinding past the topmost stack frame") := by
  rcases hstate with ⟨topFrame, hback, hcal_root, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hact_body : activeMirBody rootBody s = rootBody := by
    unfold activeMirBody
    rcases hcal_root hstack with hnone | hsome
    · simp [hnone]
    · simp [hsome]
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  rw [hstack, hact_body] at hlinks
  cases hlinks with
  | root _ rootMf _ _ _ hframe =>
    have hframes : m.stack.frames = #[rootMf] := by
      have h := array_eq_of_toList_reverse_cons hmfs
      simpa using h
    have hback_root : m.stack.frames.back? = some rootMf := by rw [hframes]; rfl
    have htf_eq : rootMf = topFrame := Option.some.inj (hback_root.symm.trans hback)
    subst htf_eq
    have hphase' : ∀ p, (activeMirBody rootBody s).phase ≠ .other p := by
      rw [hact_body]; exact hphase
    have hbb' : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb := by
      rw [hact_body]; exact hbb
    refine ⟨?_, ?_⟩
    · rw [stepMirFn_activeMirBody_eq rootBody s hphase']
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb', hstmt_none, hbeq_len, ↓reduceIte]
      unfold evalTerminator
      rw [hterm, hstack]
      rfl
    · rw [miri_step_at_terminator_multiFrame hback (by rw [hact_body]; exact hframe.body_eq)
        hframe.location_eq hbb' hstmt_none]
      unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
      rw [hterm]
      dsimp only [translateTerminatorKind, Id.run, Pure.pure]
      rw [returnFromCurrentFrame_unwind_root_ub _ hframes hframe.body_eq hframe.location_eq hbb
        hcleanup]
      rfl

/-! ## 5. `Terminator.Call` Simulation at Arbitrary Stack Depth (`step_terminator_call_simulation`) -/

@[simp]
theorem lookupCallee_nil_eq_of_findCallee_some
    (callees : List CapturedMir) (callerLayouts : LayoutTable)
    (defPath : DefPath) (extraTraitImpls : List TraitImplEntry)
    {calleeBody : CapturedMir}
    (hfind : findCallee? callees defPath = some calleeBody)
    (htparam : calleeBody.typeParamCount = 0) :
    lookupCallee callees callerLayouts defPath [] extraTraitImpls = some calleeBody := by
  unfold lookupCallee resolveCalleeBodyAndArgs?
  simp [hfind, htparam]

@[simp]
theorem lookupCallee_nil_eq_none_of_findCallee_none
    (callees : List CapturedMir) (callerLayouts : LayoutTable)
    (defPath : DefPath) (extraTraitImpls : List TraitImplEntry)
    (hfind : findCallee? callees defPath = none) :
    lookupCallee callees callerLayouts defPath [] extraTraitImpls = none := by
  unfold lookupCallee resolveCalleeBodyAndArgs?
  simp [hfind]

/-- Diverging `Terminator.Call` (`target = none`) to an unlinked unreachable call
target (`isUnreachableCallTarget defPath = true`: `"core::hint::unreachable_unchecked"`,
`"std::hint::unreachable_unchecked"`, or `"core::intrinsics::unreachable"`; neither
Stage-1 `lookupCallee` nor `findCallee?` resolves a body for it) at arbitrary stack
depth faults with undefined behavior in both Anneal (`Terminators.lean:3227-3228`)
and `lean-miri`. (A diverging call to a *linked* callee instead pushes a diverging
frame in both machines: `step_terminator_call_diverging_simulation`.) -/
theorem step_terminator_call_unreachable_unchecked_ub_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {func : MirAst.Operand} {argOps : List MirAst.Operand}
    {destination : Place} {unwind : MirAst.UnwindAction}
    {defPath : DefPath}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call func argOps destination .none unwind)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hunreach : isUnreachableCallTarget defPath = true := by rfl)
    (hargs : argOps = .nil := by rfl)
    (hcallee_none :
      lookupCallee s.memory.callees (activeMirBody rootBody s).layouts
        defPath (extractCalleeTypeArgs func) s.memory.traitImpls = none := by rfl)
    (hfind_none : findCallee? s.memory.callees defPath = none := by rfl)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  subst hargs
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (translateOperand func)
              ((List.nil : List MirAst.Operand).map fun a => ⟨defaultSpanRef, translateOperand a⟩).toArray
              (translatePlace destination) none (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator
        rw [hterm]
        rfl
      have hcall :
          annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
            (translateTerminator bb.terminator) m fnPtrs =
          (m, .error (.undefinedBehavior "entering unreachable_unchecked")) := by
        unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
        rw [hback]
        dsimp only []
        rw [hframe.location_eq]
        dsimp only []
        rw [hbb]
        dsimp only []
        rw [hterm, htk]
        dsimp only []
        rw [hfunc]
        dsimp only [List.map, annealEvalCallArgsLM4_1, Miri.Interpreter.runRvalue, pure,
          EStateM.pure]
        rw [hfind_none]
        dsimp only []
        rw [hunreach]
        rfl
      unfold evalTerminator resolveCallTarget Miri.Interpreter.ControlFlow.evalTerminator
        annealTerminatorHooksLM4_1
      rw [hterm, htk]
      dsimp only [Id.run]
      rw [hcall, hfunc]
      dsimp only [evalOperands]
      rw [hcallee_none, hunreach]
      exact StepRelMultiFrame.ub _ _

theorem initLocalsAux_nil (idx : Nat) (decls : List LocalDecl) (hpos : 0 < idx) :
    initLocalsAux idx decls [] = List.replicate decls.length .dead := by
  induction decls generalizing idx with
  | nil => rfl
  | cons _ ds ih =>
    cases idx with
    | zero => omega
    | succ n =>
      simp [initLocalsAux, List.replicate_succ, ih (n + 1) (by omega)]

theorem IsLiveFrameLocal.set_immediate
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx j : Nat} (h : IsLiveFrameLocal mf idx)
    (hlt : j < mf.locals.size) (imm : Miri.Interpreter.Immediate AnnealProv) :
    IsLiveFrameLocal
      { mf with locals := mf.locals.set j { mf.locals[j]'hlt with value := .live (.immediate imm) } hlt }
      idx := by
  intro mls hmls hdead
  rw [Array.getElem?_set] at hmls
  by_cases hj : j = idx
  · simp only [hj, ↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hdead
    cases hdead
  · simp only [hj, ↓reduceIte] at hmls
    exact h mls hmls hdead

theorem IsLiveFrameLocal.cache_layout
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx j : Nat} (h : IsLiveFrameLocal mf idx)
    (hlt : j < mf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    IsLiveFrameLocal (cacheFrameLocalLayout mf j hlt lay) idx := by
  intro mls hmls hdead
  unfold cacheFrameLocalLayout at hmls
  rw [Array.getElem?_set] at hmls
  by_cases hj : j = idx
  · subst hj
    simp only [↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hdead
    exact h (mf.locals[j]'hlt) (Array.getElem?_eq_getElem hlt) hdead
  · simp only [hj, ↓reduceIte] at hmls
    exact h mls hmls hdead

theorem stack_currentFrame?_append_singleton
    (stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hframes : stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩) :
    stack.currentFrame? = some topFrame := by
  unfold Miri.Interpreter.Stack.currentFrame?
  rw [hframes]
  exact array_back?_append_singleton restMfs.reverse topFrame

theorem stepState_with_same_append_singleton
    (m : AnnealStepState)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩) :
    { m with stack := ⟨⟨restMfs.reverse ++ [topFrame]⟩⟩ } = m := by
  rcases m with ⟨⟨frames⟩, machine⟩
  dsimp only at hframes
  subst hframes
  rfl

@[simp]
theorem array_size_append_singleton {α : Type _} (xs : List α) (tf : α) :
    (⟨xs ++ [tf]⟩ : Array α).size = xs.length + 1 := by
  simp

theorem annealResolveAndCacheLocalLayout_multiFrame_eq
    {body : CapturedMir} {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts) :
    annealResolveAndCacheLocalLayout body.localDecls body.layouts idx known m =
      .ok (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts),
            translateTy decl.ty body.layouts)
        { m with
          stack := ⟨⟨restMfs.reverse ++
            [cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)]⟩⟩ } := by
  have hget : topFrame.getLocal idx = .ok (topFrame.locals[idx]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  have hgor := frame_getOrCacheLocalLayout_eq topFrame hlt hcache
  with_unfolding_all
    unfold annealResolveAndCacheLocalLayout
    simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes,
      hget, cachedLayout_orElse_lookupLocalDeclLayout_orElse hdecl hcache,
      hgor, hframes, array_size_append_singleton,
      Nat.add_sub_cancel, Nat.lt_succ_self, ↓reduceDIte,
      array_set_last_append_singleton]
    rfl

theorem annealEvalOperand_copy_dead_multiFrame
    {body : CapturedMir} {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with
          stack := ⟨⟨restMfs.reverse ++
            [cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)]⟩⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_multiFrame_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem annealEvalOperand_copy_live_multiFrame
    {body : CapturedMir} {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨⟨restMfs.reverse ++
            [cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)]⟩⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_multiFrame_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem annealEvalOperand_move_dead_multiFrame
    {body : CapturedMir} {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with
          stack := ⟨⟨restMfs.reverse ++
            [cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)]⟩⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_multiFrame_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem annealEvalOperand_move_live_multiFrame
    {body : CapturedMir} {m : AnnealStepState}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨⟨restMfs.reverse ++
            [deinitFrameLocal
              (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)) idx
              (by rw [cacheFrameLocalLayout_size]; exact hlt)]⟩⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_multiFrame_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  have hlt' : idx < (cacheFrameLocalLayout topFrame idx hlt
      (translateTy decl.ty body.layouts)).locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt
  have hrep := frame_replaceLocalValue_of_lt
    (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)) idx hlt'
    (.live (.immediate .uninit))
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes,
      Option.isNone_some, hres, hgop, hrep,
      array_size_append_singleton,
      Nat.add_sub_cancel, Nat.lt_succ_self, ↓reduceDIte,
      array_set_last_append_singleton]
    rfl

/-- Well-typed call argument operand in `callerBody` relative to `topFrame` and
the corresponding parameter declaration `argDecl` in `calleeBody`, covering
constants/copies (`WellTypedScalarOperand`) and destructive moves (`Operand.move`). -/
inductive WellTypedCallArgOperand
    (callerBody calleeBody : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Operand → LocalDecl → Prop where
  | scalarOp (op : MirAst.Operand) (srcTy : Ty) (argDecl : LocalDecl) :
      WellTypedScalarOperand callerBody topFrame op srcTy →
      translateTy srcTy callerBody.layouts = translateTy argDecl.ty calleeBody.layouts →
      (∀ v imm, ImmediateRel srcTy callerBody.layouts v imm →
        ImmediateRel argDecl.ty calleeBody.layouts v imm) →
      WellTypedCallArgOperand callerBody calleeBody topFrame op argDecl
  | moveLocal (idx : Local) (srcDecl argDecl : LocalDecl) :
      get? callerBody.localDecls idx = some srcDecl →
      (translateTy srcDecl.ty callerBody.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      IsImmediateFrameLocal topFrame idx →
      translateTy srcDecl.ty callerBody.layouts = translateTy argDecl.ty calleeBody.layouts →
      (∀ v imm, ImmediateRel srcDecl.ty callerBody.layouts v imm →
        ImmediateRel argDecl.ty calleeBody.layouts v imm) →
      WellTypedCallArgOperand callerBody calleeBody topFrame (.move ⟨idx, .nil⟩) argDecl

theorem WellTypedCallArgOperand.mono_immediate
    {callerBody calleeBody : CapturedMir}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {argDecl : LocalDecl}
    (h : WellTypedCallArgOperand callerBody calleeBody tf op argDecl)
    (hmono : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :
    WellTypedCallArgOperand callerBody calleeBody tf' op argDecl := by
  cases h with
  | scalarOp op srcTy argDecl hop hlay himm =>
    exact .scalarOp op srcTy argDecl (hop.mono_immediate hmono) hlay himm
  | moveLocal idx srcDecl argDecl hdecl hsz himm_loc hlay himm =>
    exact .moveLocal idx srcDecl argDecl hdecl hsz (hmono idx himm_loc) hlay himm

/-- Well-typed list of call argument operands `argOps` matching the callee's
post-`_0` parameter/local declarations (`argDecls ++ tempDecls`). -/
inductive WellTypedCallArgs
    (callerBody calleeBody : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    List MirAst.Operand → List LocalDecl → Prop where
  | nil (tempDecls : List LocalDecl) :
      WellTypedCallArgs callerBody calleeBody topFrame [] tempDecls
  | cons (op : MirAst.Operand) (restOps : List MirAst.Operand)
      (argDecl : LocalDecl) (restDecls : List LocalDecl) :
      WellTypedCallArgOperand callerBody calleeBody topFrame op argDecl →
      WellTypedCallArgs callerBody calleeBody topFrame restOps restDecls →
      WellTypedCallArgs callerBody calleeBody topFrame (op :: restOps) (argDecl :: restDecls)

theorem WellTypedCallArgs.mono_immediate
    {callerBody calleeBody : CapturedMir}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ops : List MirAst.Operand} {decls : List LocalDecl}
    (h : WellTypedCallArgs callerBody calleeBody tf ops decls)
    (hmono : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :
    WellTypedCallArgs callerBody calleeBody tf' ops decls := by
  induction h with
  | nil tempDecls => exact .nil tempDecls
  | cons op restOps argDecl restDecls hop _ ih =>
    exact .cons op restOps argDecl restDecls (hop.mono_immediate hmono) ih

/-- Pointwise relation between evaluated Anneal argument values `argVals`,
`lean-miri` argument immediates `argImms`, and the callee's post-`_0`
`LocalDecl`s (`argDecls ++ tempDecls`). -/
inductive CalleeArgsRel (layouts : LayoutTable) :
    List LocalDecl → List Value → List (Miri.Interpreter.RvalueImmTy AnnealProv) → Prop where
  | nil (tempDecls : List LocalDecl) :
      CalleeArgsRel layouts tempDecls [] []
  | cons (decl : LocalDecl) (decls : List LocalDecl)
      (v : Value) (vs : List Value)
      (rv : Miri.Interpreter.RvalueImmTy AnnealProv)
      (rvs : List (Miri.Interpreter.RvalueImmTy AnnealProv)) :
      rv.layout = translateTy decl.ty layouts →
      ImmediateRel decl.ty layouts v rv.imm →
      CalleeArgsRel layouts decls vs rvs →
      CalleeArgsRel layouts (decl :: decls) (v :: vs) (rv :: rvs)

/-- Joint outcome relation for a single call argument operand evaluation
(`evalOperand` in Anneal vs `annealEvalOperand >>= annealReadImmediate` in `lean-miri`). -/
inductive CallArgOperandEvalSimRel
    (callerBody calleeBody : CapturedMir)
    (m : AnnealStepState)
    (callerAf : StackFrame)
    (callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (argDecl : LocalDecl) :
    PlaceReadResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) → Prop where
  | ub (m' : AnnealStepState) (msg : String) :
      CallArgOperandEvalSimRel callerBody calleeBody m callerAf callerMf restMfs argDecl
        .ub (.error (.undefinedBehavior msg) m')
  | ok (v : Value) (locals' : List LocalSlot)
      (callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (rv : Miri.Interpreter.RvalueImmTy AnnealProv) :
      callerMf'.localsIdentity = callerMf.localsIdentity →
      callerMf'.returnContinuation = callerMf.returnContinuation →
      callerMf'.returnPlace = callerMf.returnPlace →
      (∀ (i : Nat) mp lay,
        callerMf'.locals[i]? =
          some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
        (∃ lay₀,
          callerMf.locals[i]? =
            some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀)) ∧
        get? locals' i = get? callerAf.locals i) →
      (∀ j, IsImmediateFrameLocal callerMf j → IsImmediateFrameLocal callerMf' j) →
      (∀ j, IsLiveFrameLocal callerMf j → IsLiveFrameLocal callerMf' j) →
      (MemoryAllocDisjoint callerMf → MemoryAllocDisjoint callerMf') →
      FrameRel callerBody m.machine { callerAf with locals := locals' } callerMf' →
      rv.layout = translateTy argDecl.ty calleeBody.layouts →
      ImmediateRel argDecl.ty calleeBody.layouts v rv.imm →
      CallArgOperandEvalSimRel callerBody calleeBody m callerAf callerMf restMfs argDecl
        (.ok v locals')
        (.ok rv { m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ })

theorem evalCallArgOperand_simulation
    {callerBody calleeBody : CapturedMir}
    {m : AnnealStepState}
    {callerAf : StackFrame}
    {callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {op : MirAst.Operand} {argDecl : LocalDecl}
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [callerMf]⟩)
    (hframe : FrameRel callerBody m.machine callerAf callerMf)
    (hop : WellTypedCallArgOperand callerBody calleeBody callerMf op argDecl)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    CallArgOperandEvalSimRel callerBody calleeBody m callerAf callerMf restMfs argDecl
      (evalOperand callerAf.locals op borrows globals callerBody.layouts callerLocals)
      ((annealEvalOperand callerBody.localDecls callerBody.layouts (translateOperand op) none >>=
        annealReadImmediate) m) := by
  have hsame := stepState_with_same_append_singleton m restMfs callerMf hframes
  cases hop with
  | scalarOp op srcTy argDecl hwt hlay_eq himm_tr =>
    cases hwt with
    | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
      obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
      have heval_a : evalOperand callerAf.locals (.constant c) borrows globals
          callerBody.layouts callerLocals = .ok (.scalar sc) callerAf.locals := by
        unfold evalOperand
        dsimp only
        rw [hval]; rfl
      have heval_m : annealEvalOperand callerBody.localDecls callerBody.layouts
          (translateOperand (.constant c)) none m =
          .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty callerBody.layouts⟩ m := by
        with_unfolding_all
          unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
          dsimp only
          rw [hval]
          simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
            EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            stack_currentFrame?_append_singleton m.stack restMfs callerMf hframes,
            Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
      rw [heval_a, EStateM.bind_eq_ok heval_m]
      change CallArgOperandEvalSimRel callerBody calleeBody m callerAf callerMf restMfs argDecl
        (.ok (.scalar sc) callerAf.locals)
        (.ok ⟨.scalar (.fromScalarInt msc), translateTy c.ty callerBody.layouts⟩ m)
      rw [← hsame]
      exact .ok (.scalar sc) callerAf.locals callerMf
        ⟨.scalar (.fromScalarInt msc), translateTy c.ty callerBody.layouts⟩
        rfl rfl rfl
        (fun _ _ lay h => ⟨⟨lay, h⟩, rfl⟩)
        (fun _ h => h)
        (fun _ h => h)
        id
        hframe
        hlay_eq
        (himm_tr _ _ (.scalar sc msc hrel hlaysz hbool hchar))
    | copyLocal idx decl hdecl hsz_nz himm =>
      obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hcache := hloc.layout_eq
      have himm' := himm mls hmls
      have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
      rw [htr]
      cases hloc with
      | dead cachedLayout _ =>
        have ha : evalOperand callerAf.locals (.copy ⟨idx, .nil⟩) borrows globals
            callerBody.layouts callerLocals = .ub := by
          simp [evalOperand, hslot]
        rw [ha, EStateM.bind_eq_error
          (annealEvalOperand_copy_dead_multiFrame hframes hlt_mf hdecl hmls_eq hcache)]
        exact .ub _ _
      | indirect _ mp _ _ _ _ =>
        exact False.elim (himm' mp rfl)
      | immediate _ imm cachedLayout _ hval =>
        let callerMf' := cacheFrameLocalLayout callerMf idx hlt_mf (translateTy decl.ty callerBody.layouts)
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · have ha : evalOperand callerAf.locals (.copy ⟨idx, .nil⟩) borrows globals
              callerBody.layouts callerLocals = .ub := by
            simp [evalOperand, hslot]
          rw [ha, EStateM.bind_eq_ok
            (annealEvalOperand_copy_live_multiFrame hframes hlt_mf hdecl hmls_eq hcache)]
          exact .ub _ _
        · have ha : evalOperand callerAf.locals (.copy ⟨idx, .nil⟩) borrows globals
              callerBody.layouts callerLocals = .ok v callerAf.locals := by
            simp [evalOperand, readProjectedValue, hslot]
          obtain ⟨hread, _⟩ :=
            annealReadImmediate_of_immediateRel himmRel hsz_nz (translateTy decl.ty callerBody.layouts)
              { m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ }
          rw [ha, EStateM.bind_eq_ok
            (annealEvalOperand_copy_live_multiFrame hframes hlt_mf hdecl hmls_eq hcache), hread]
          refine .ok v callerAf.locals callerMf'
            ⟨imm, translateTy decl.ty callerBody.layouts⟩
            rfl rfl rfl
            (fun i mp lay hi => ?_)
            (fun _ hj => hj.cache_layout hlt_mf _)
            (fun _ hj => hj.cache_layout hlt_mf _)
            (fun hdisj => ?_)
            (hframe.cache_local_layout hdecl hlt_mf)
            hlay_eq
            (himm_tr v imm himmRel)
          · refine ⟨?_, rfl⟩
            dsimp [callerMf', cacheFrameLocalLayout] at hi
            rw [Array.getElem?_set] at hi
            by_cases hk : idx = i
            · subst hk
              simp only [↓reduceIte, Option.some.injEq] at hi
              have hval_eq : (callerMf.locals[idx]'hlt_mf).value = .live (.indirect mp) :=
                congrArg Miri.Interpreter.LocalState.value hi
              rw [hmls_eq] at hval_eq
              cases hval_eq
            · simp only [hk, ↓reduceIte] at hi
              exact ⟨lay, hi⟩
          · apply MemoryAllocDisjoint.mono_layout hdisj
            intro k
            by_cases hk : k = idx
            · subst hk
              exists (translateTy decl.ty callerBody.layouts)
              dsimp [callerMf', cacheFrameLocalLayout]
              rw [Array.getElem?_set]
              simp only [↓reduceIte]
              simp [hmls, hmls_eq]
            · exists (callerMf.locals[k]?).bind (fun x => x.layout)
              dsimp [callerMf', cacheFrameLocalLayout]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)]
              cases callerMf.locals[k]? <;> rfl
  | moveLocal idx srcDecl argDecl hdecl hsz_nz himm hlay_eq himm_tr =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hcache := hloc.layout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.move ⟨idx, .nil⟩) = .Move ⟨idx, #[]⟩ := rfl
    rw [htr]
    cases hloc with
    | dead cachedLayout _ =>
      have ha : evalOperand callerAf.locals (.move ⟨idx, .nil⟩) borrows globals
          callerBody.layouts callerLocals = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_error
        (annealEvalOperand_move_dead_multiFrame hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      let callerMf₀ := cacheFrameLocalLayout callerMf idx hlt_mf (translateTy srcDecl.ty callerBody.layouts)
      have hlt_mf' : idx < callerMf₀.locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_mf
      let callerMf' := deinitFrameLocal callerMf₀ idx hlt_mf'
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · have ha : evalOperand callerAf.locals (.move ⟨idx, .nil⟩) borrows globals
            callerBody.layouts callerLocals = .ub := by
          simp [evalOperand, hslot]
        rw [ha, EStateM.bind_eq_ok
          (annealEvalOperand_move_live_multiFrame hframes hlt_mf hdecl hmls_eq hcache)]
        exact .ub _ _
      · have ha : evalOperand callerAf.locals (.move ⟨idx, .nil⟩) borrows globals
            callerBody.layouts callerLocals = .ok v (callerAf.locals.set idx .uninit) := by
          simp [evalOperand, hslot, set?_eq_some_set hlt_af]
        obtain ⟨hread, _⟩ :=
          annealReadImmediate_of_immediateRel himmRel hsz_nz (translateTy srcDecl.ty callerBody.layouts)
            { m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ }
        rw [ha, EStateM.bind_eq_ok
          (annealEvalOperand_move_live_multiFrame hframes hlt_mf hdecl hmls_eq hcache), hread]
        have hnew : LocalRel m.machine srcDecl callerBody.layouts .uninit
            { callerMf₀.locals[idx]'hlt_mf' with value := .live (.immediate .uninit) } := by
          have hlay : (callerMf₀.locals[idx]'hlt_mf').layout =
              some (translateTy srcDecl.ty callerBody.layouts) := by
            simp [callerMf₀, cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        refine .ok v (callerAf.locals.set idx .uninit) callerMf'
          ⟨imm, translateTy srcDecl.ty callerBody.layouts⟩
          rfl rfl rfl
          (fun i mp lay hi => ?_)
          (fun _ hj => (hj.cache_layout hlt_mf _).set_immediate hlt_mf' .uninit)
          (fun _ hj => (hj.cache_layout hlt_mf _).set_immediate hlt_mf' .uninit)
          (fun hdisj => ?_)
          ((hframe.cache_local_layout hdecl hlt_mf).update_local hdecl .uninit
            (.live (.immediate .uninit)) hnew)
          hlay_eq
          (himm_tr v imm himmRel)
        · dsimp [callerMf', deinitFrameLocal] at hi
          rw [Array.getElem?_set] at hi
          by_cases hk : idx = i
          · subst hk
            simp only [↓reduceIte, Option.some.injEq] at hi
            have hval_eq : (Miri.Interpreter.LocalValue.live (.immediate .uninit) :
                Miri.Interpreter.LocalValue AnnealProv) = .live (.indirect mp) :=
              congrArg Miri.Interpreter.LocalState.value hi
            cases hval_eq
          · simp only [hk, ↓reduceIte] at hi
            dsimp [callerMf₀, cacheFrameLocalLayout] at hi
            rw [Array.getElem?_set_ne _ hk] at hi
            refine ⟨⟨lay, hi⟩, ?_⟩
            rw [get?_eq_getElem?, get?_eq_getElem?, List.getElem?_set_ne hk]
        · have hdisj₀ : MemoryAllocDisjoint callerMf₀ := by
            apply MemoryAllocDisjoint.mono_layout hdisj
            intro k
            by_cases hk : k = idx
            · subst hk
              exists (translateTy srcDecl.ty callerBody.layouts)
              dsimp [callerMf₀, cacheFrameLocalLayout]
              rw [Array.getElem?_set]
              simp only [↓reduceIte]
              simp [hmls, hmls_eq]
            · exists (callerMf.locals[k]?).bind (fun x => x.layout)
              dsimp [callerMf₀, cacheFrameLocalLayout]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)]
              cases callerMf.locals[k]? <;> rfl
          apply MemoryAllocDisjoint.mono_immediate (tf := callerMf₀) hdisj₀
          intro k
          by_cases hk : k = idx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy srcDecl.ty callerBody.layouts), by
              simp [callerMf', deinitFrameLocal, callerMf₀, cacheFrameLocalLayout]⟩
          · left
            simp [callerMf', deinitFrameLocal, callerMf₀, cacheFrameLocalLayout,
              Array.getElem?_set_ne _ (Ne.symm hk)]

theorem runRvalue_eq_of_eq_any {S α : Type} {f g : Miri.Interpreter.RvalueM S α} {s₁ s₂ : S}
    (h : f s₁ = g s₂) : Miri.Interpreter.runRvalue f s₁ = Miri.Interpreter.runRvalue g s₂ := by
  unfold Miri.Interpreter.runRvalue
  rw [h]

theorem runRvalue_eq_error_iff {S α : Type} {f : Miri.Interpreter.RvalueM S α} {s s' : S}
    {e : Miri.Interpreter.StepError} :
    Miri.Interpreter.runRvalue f s = (s', .error e) ↔ f s = .error e s' := by
  unfold Miri.Interpreter.runRvalue
  cases f s <;> simp [and_comm]

theorem runRvalue_eq_ok_iff {S α : Type} {f : Miri.Interpreter.RvalueM S α} {s s' : S} {a : α} :
    Miri.Interpreter.runRvalue f s = (s', .ok a) ↔ f s = .ok a s' := by
  unfold Miri.Interpreter.runRvalue
  cases f s <;> simp [and_comm]

/-- Joint simulation relation for evaluating `Terminator.Call` argument operands
(`evalOperands` in Anneal vs `annealEvalCallArgsLM4_1` in `lean-miri`). -/
inductive EvalCallArgsSimRel
    (callerBody calleeBody : CapturedMir)
    (m : AnnealStepState)
    (callerAf : StackFrame)
    (callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (restDecls : List LocalDecl) :
    OperandsEvalResult →
    Miri.Interpreter.StepResult AnnealStepState (List (Miri.Interpreter.RvalueImmTy AnnealProv)) → Prop where
  | ub (m' : AnnealStepState) (msg : String) :
      EvalCallArgsSimRel callerBody calleeBody m callerAf callerMf restMfs restDecls
        .ub (m', .error (.undefinedBehavior msg))
  | ok (argVals : List Value) (locals' : List LocalSlot)
       (callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
       (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv)) :
      callerMf'.localsIdentity = callerMf.localsIdentity →
      callerMf'.returnContinuation = callerMf.returnContinuation →
      callerMf'.returnPlace = callerMf.returnPlace →
      (∀ (i : Nat) mp lay,
        callerMf'.locals[i]? =
          some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
        (∃ lay₀,
          callerMf.locals[i]? =
            some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀)) ∧
        get? locals' i = get? callerAf.locals i) →
      (∀ j, IsImmediateFrameLocal callerMf j → IsImmediateFrameLocal callerMf' j) →
      (∀ j, IsLiveFrameLocal callerMf j → IsLiveFrameLocal callerMf' j) →
      (MemoryAllocDisjoint callerMf → MemoryAllocDisjoint callerMf') →
      FrameRel callerBody m.machine { callerAf with locals := locals' } callerMf' →
      CalleeArgsRel calleeBody.layouts restDecls argVals argImms →
      EvalCallArgsSimRel callerBody calleeBody m callerAf callerMf restMfs restDecls
        (.ok argVals locals')
        ({ m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ }, .ok argImms)

theorem evalCallArgs_simulation
    {callerBody calleeBody : CapturedMir}
    {m : AnnealStepState}
    {callerAf : StackFrame}
    {callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {argOps : List MirAst.Operand} {restDecls : List LocalDecl}
    (hwt : WellTypedCallArgs callerBody calleeBody callerMf argOps restDecls)
    (hframes : m.stack.frames = ⟨restMfs.reverse ++ [callerMf]⟩)
    (hframe : FrameRel callerBody m.machine callerAf callerMf)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    EvalCallArgsSimRel callerBody calleeBody m callerAf callerMf restMfs restDecls
      (evalOperands callerAf.locals argOps borrows globals callerBody.layouts callerLocals)
      (Miri.Interpreter.runRvalue
        (annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
          (argOps.map translateOperand)) m) := by
  induction argOps generalizing callerMf restDecls m callerAf with
  | nil =>
    cases hwt with
    | nil =>
      have hsame := stepState_with_same_append_singleton m restMfs callerMf hframes
      unfold evalOperands annealEvalCallArgsLM4_1 Miri.Interpreter.runRvalue
      dsimp only [List.map, pure, Pure.pure, EStateM.pure]
      rw [← hsame]
      exact .ok [] callerAf.locals callerMf []
        rfl rfl rfl
        (fun _ _ lay h => ⟨⟨lay, h⟩, rfl⟩)
        (fun _ h => h)
        (fun _ h => h)
        id
        hframe
        (.nil restDecls)
  | cons op restOps ih =>
    cases hwt with
    | cons _ _ argDecl restDecls' hop hwt_rest =>
      have hm_cons :
          Miri.Interpreter.runRvalue
            (annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
              ((op :: restOps).map translateOperand)) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand callerBody.localDecls callerBody.layouts (translateOperand op) none >>=
                annealReadImmediate) >>=
              fun imm => do
                let restImms ←
                  annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
                    (restOps.map translateOperand)
                return (imm :: restImms)) m := by
        dsimp only [List.map, annealEvalCallArgsLM4_1]
        apply runRvalue_eq_of_eq_any
        exact EStateM.bind_assoc_apply _ _ _ m
      rw [hm_cons]
      have hop_sim :=
        evalCallArgOperand_simulation hframes hframe hop borrows globals callerLocals
      generalize ha_op :
        evalOperand callerAf.locals op borrows globals callerBody.layouts callerLocals = aOp at hop_sim
      generalize hm_op :
        (annealEvalOperand callerBody.localDecls callerBody.layouts (translateOperand op) none >>=
          annealReadImmediate) m = mOp at hop_sim
      cases hop_sim with
      | ub m' msg =>
        unfold evalOperands Miri.Interpreter.runRvalue
        rw [ha_op, EStateM.bind_eq_error hm_op]
        exact .ub _ _
      | ok v locals₁ callerMf₁ rv hid₁ hrc₁ hrp₁ hloc₁ himm_mono₁ hlive_mono₁ hdisj₁ hframe₁ hlay₁ himmRel₁ =>
        let m₁ : AnnealStepState := { m with stack := ⟨⟨restMfs.reverse ++ [callerMf₁]⟩⟩ }
        have hih := ih (m := m₁) (callerAf := { callerAf with locals := locals₁ })
          (hwt_rest.mono_immediate himm_mono₁) rfl hframe₁
        have hm_after_op :
            Miri.Interpreter.runRvalue
              ((annealEvalOperand callerBody.localDecls callerBody.layouts (translateOperand op) none >>=
                  annealReadImmediate) >>=
                fun imm => do
                  let restImms ←
                    annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
                      (restOps.map translateOperand)
                  return (imm :: restImms)) m =
            Miri.Interpreter.runRvalue
              (do
                let restImms ←
                  annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
                    (restOps.map translateOperand)
                return (rv :: restImms)) m₁ := by
          apply runRvalue_eq_of_eq_any
          exact EStateM.bind_eq_ok hm_op
        rw [hm_after_op]
        generalize ha_rest :
          evalOperands locals₁ restOps borrows globals callerBody.layouts callerLocals = aRest at hih
        generalize hm_rest :
          Miri.Interpreter.runRvalue
            (annealEvalCallArgsLM4_1 callerBody.localDecls callerBody.layouts
              (restOps.map translateOperand)) m₁ = mRest at hih
        cases hih with
        | ub m' msg =>
          have hm_err := runRvalue_eq_error_iff.mp hm_rest
          unfold evalOperands Miri.Interpreter.runRvalue
          rw [ha_op]
          dsimp only
          rw [ha_rest, EStateM.bind_eq_error hm_err]
          exact .ub _ _
        | ok vs locals₂ callerMf₂ rvs hid₂ hrc₂ hrp₂ hloc₂ himm_mono₂ hlive_mono₂ hdisj₂ hframe₂ hargsRel₂ =>
          have hm_ok := runRvalue_eq_ok_iff.mp hm_rest
          unfold evalOperands Miri.Interpreter.runRvalue
          rw [ha_op]
          dsimp only
          rw [ha_rest, EStateM.bind_eq_ok hm_ok]
          dsimp only [pure, Pure.pure, EStateM.pure]
          refine .ok (v :: vs) locals₂ callerMf₂ (rv :: rvs)
            (hid₂.trans hid₁) (hrc₂.trans hrc₁) (hrp₂.trans hrp₁)
            (fun i mp lay hi => ?_)
            (fun j hj => himm_mono₂ j (himm_mono₁ j hj))
            (fun j hj => hlive_mono₂ j (hlive_mono₁ j hj))
            (fun hdisj => hdisj₂ (hdisj₁ hdisj))
            hframe₂
            (.cons argDecl restDecls' v vs rv rvs hlay₁ himmRel₁ hargsRel₂)
          obtain ⟨⟨lay₁, hi₁⟩, heq₁⟩ := hloc₂ i mp lay hi
          obtain ⟨⟨lay₀, hi₀⟩, heq₀⟩ := hloc₁ i mp lay₁ hi₁
          exact ⟨⟨lay₀, hi₀⟩, heq₁.trans heq₀⟩

def calleeArgLocalStates :
    List LocalDecl → List (Miri.Interpreter.RvalueImmTy AnnealProv) →
    List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
  | [], _ => []
  | _ :: decls, rv :: rest =>
    { value := .live (.immediate rv.imm), layout := some rv.layout } ::
      calleeArgLocalStates decls rest
  | _ :: decls, [] =>
    { value := .dead, layout := none } :: calleeArgLocalStates decls []

theorem calleeArgLocalStates_nil (decls : List LocalDecl) :
    calleeArgLocalStates decls [] =
      List.replicate decls.length { value := .dead, layout := none } := by
  induction decls with
  | nil => rfl
  | cons _ ds ih => simp [calleeArgLocalStates, List.replicate_succ, ih]

theorem calleeArgLocalStates_length
    (decls : List LocalDecl) (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv)) :
    (calleeArgLocalStates decls argImms).length = decls.length := by
  induction decls generalizing argImms with
  | nil => rfl
  | cons _ ds ih =>
    cases argImms with
    | nil => simp [calleeArgLocalStates, ih]
    | cons _ rs => simp [calleeArgLocalStates, ih]

theorem initLocalsAux_length
    (idx : Nat) (decls : List LocalDecl) (argVals : List Value) :
    (initLocalsAux idx decls argVals).length = decls.length := by
  induction decls generalizing idx argVals with
  | nil => rfl
  | cons _ ds ih =>
    cases idx with
    | zero => simp [initLocalsAux, ih]
    | succ n =>
      cases argVals with
      | nil => simp [initLocalsAux, ih]
      | cons _ vs => simp [initLocalsAux, ih]

theorem calleeArgLocalStates_no_indirect
    (decls : List LocalDecl) (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv))
    (k : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Option Miri.Interpreter.LocalLayout) :
    (calleeArgLocalStates decls argImms)[k]? ≠
      some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) := by
  induction decls generalizing argImms k with
  | nil => simp [calleeArgLocalStates]
  | cons _ ds ih =>
    cases argImms with
    | nil =>
      cases k with
      | zero => simp [calleeArgLocalStates]
      | succ k' => simpa [calleeArgLocalStates] using ih [] k'
    | cons _ rvs =>
      cases k with
      | zero => simp [calleeArgLocalStates]
      | succ k' => simpa [calleeArgLocalStates] using ih rvs k'

theorem CalleeArgsRel.locals_rel
    {layouts : LayoutTable} {decls : List LocalDecl}
    {argVals : List Value} {argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv)}
    (hargs : CalleeArgsRel layouts decls argVals argImms)
    (mach : AnnealMachine) :
    ∀ (idx : Nat), 0 < idx →
      ∀ (k : Nat) (decl : LocalDecl) (slot : LocalSlot)
        (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
        get? decls k = some decl →
        get? (initLocalsAux idx decls argVals) k = some slot →
        (calleeArgLocalStates decls argImms)[k]? = some mls →
        LocalRel mach decl layouts slot mls := by
  induction hargs with
  | nil tempDecls =>
    intro idx hpos k decl slot mls _ hslot hmls
    rw [initLocalsAux_nil idx tempDecls hpos, get?_eq_getElem?] at hslot
    rw [calleeArgLocalStates_nil tempDecls] at hmls
    obtain ⟨_, hslot_eq⟩ := List.getElem?_eq_some_iff.mp hslot
    rw [List.getElem_replicate] at hslot_eq
    obtain ⟨_, hmls_eq⟩ := List.getElem?_eq_some_iff.mp hmls
    rw [List.getElem_replicate] at hmls_eq
    subst hslot_eq hmls_eq
    exact .dead none (fun _ h => nomatch h)
  | cons decl restDecls v vs rv rvs hlay himm _ ih =>
    intro idx hpos k decl_k slot_k mls_k hdecl hslot hmls
    cases idx with
    | zero => omega
    | succ n =>
      cases k with
      | zero =>
        simp only [get?, initLocalsAux, calleeArgLocalStates, List.getElem?_cons_zero,
          Option.some.injEq] at hdecl hslot hmls
        subst hdecl hslot hmls
        refine .immediate (.init v) rv.imm (some rv.layout) ?_ (Or.inr ⟨v, rfl, himm⟩)
        intro l hl
        injection hl with hl'
        exact hl'.symm.trans hlay
      | succ k' =>
        simp only [get?, initLocalsAux, calleeArgLocalStates, List.getElem?_cons_succ] at hdecl hslot hmls
        exact ih (n + 1) (by omega) k' decl_k slot_k mls_k hdecl hslot hmls

theorem CalleeArgsRel.initCalleeArgLocals_eq
    {layouts : LayoutTable} {decls : List LocalDecl}
    {argVals : List Value} {argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv)}
    (hargs : CalleeArgsRel layouts decls argVals argImms) :
    ∀ (pref : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      frame.locals =
        ⟨pref ++ List.replicate decls.length { value := .dead, layout := none }⟩ →
      initCalleeArgLocals pref.length argImms frame =
        { frame with locals := ⟨pref ++ calleeArgLocalStates decls argImms⟩ } := by
  induction hargs with
  | nil tempDecls =>
    intro pref frame hloc
    unfold initCalleeArgLocals
    rw [calleeArgLocalStates_nil, ← hloc]
  | cons decl restDecls v vs rv rvs _ _ _ ih =>
    intro pref frame hloc
    unfold initCalleeArgLocals
    have hlt : pref.length < frame.locals.size := by
      rw [hloc]
      simp [List.replicate_succ]
    simp only [hlt, ↓reduceDIte]
    let newSlot : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate rv.imm), layout := some rv.layout }
    have hset :
        frame.locals.set pref.length newSlot hlt =
        ⟨(pref ++ [newSlot]) ++
          List.replicate restDecls.length { value := .dead, layout := none }⟩ := by
      apply Array.ext'
      rw [Array.toList_set, hloc]
      simp [newSlot, List.replicate_succ, List.set_append_right]
    have hlen' : pref.length + 1 = (pref ++ [newSlot]).length := by
      simp
    rw [hlen']
    have hih := ih (pref ++ [newSlot])
      { frame with locals := frame.locals.set pref.length newSlot hlt }
      hset
    rw [hih]
    simp [newSlot, calleeArgLocalStates, List.append_assoc]

/-- Well-formedness of a caller destination local `destIdx` in `topFrame`:
either `destIdx` is an immediate local (`IsImmediateFrameLocal topFrame destIdx`),
or `destIdx` is an `.indirect` primitive scalar local backed by a well-formed stack
allocation in `mach`. -/
def CallerDestSlotWf
    (mach : AnnealMachine)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (destIdx : Local) (destDecl : LocalDecl) : Prop :=
  IsImmediateFrameLocal topFrame destIdx ∨
  (IsPrimScalarTy destDecl.ty ∧
   (mach.memory.live.toList.map Prod.fst).Nodup ∧
   ∀ (mp : Miri.Interpreter.MemPlace AnnealProv)
     (lay : Option Miri.Interpreter.LocalLayout)
     (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
     (localAlloc : AnnealLocalAlloc),
     topFrame.locals[destIdx]? = some { value := .live (.indirect mp), layout := lay } →
     mp.ptr.provenance = some (.concrete allocId tag) →
     (allocId, localAlloc) ∈ mach.memory.live.toList →
     localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat ∧
     localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
     ∃ words,
       InitMaskWordRel localAlloc.allocation.initializationMask
         localAlloc.allocation.byteSize words)

theorem CallerDestSlotWf.of_immediate
    {mach : AnnealMachine}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destIdx : Local} {destDecl : LocalDecl}
    (himm : IsImmediateFrameLocal topFrame destIdx) :
    CallerDestSlotWf mach topFrame destIdx destDecl :=
  Or.inl himm

theorem CallerDestSlotWf.mono_evalArgs
    {mach : AnnealMachine}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destIdx : Local} {destDecl : LocalDecl}
    (h : CallerDestSlotWf mach tf destIdx destDecl)
    (himm_mono : IsImmediateFrameLocal tf destIdx → IsImmediateFrameLocal tf' destIdx)
    (hind_sub :
      ∀ mp lay,
        tf'.locals[destIdx]? = some { value := .live (.indirect mp), layout := lay } →
        ∃ lay₀, tf.locals[destIdx]? = some { value := .live (.indirect mp), layout := lay₀ }) :
    CallerDestSlotWf mach tf' destIdx destDecl := by
  rcases h with himm | ⟨hprim, hnodup, halloc⟩
  · exact Or.inl (himm_mono himm)
  · refine Or.inr ⟨hprim, hnodup, ?_⟩
    intro mp lay allocId tag localAlloc hdest' hprov hlive
    obtain ⟨lay₀, hdest₀⟩ := hind_sub mp lay hdest'
    exact halloc mp lay₀ allocId tag localAlloc hdest₀ hprov hlive

/-- When the callee can unwind (or the call already forbids unwinding), the
nounwind rewriting of canonical `Call.initStackFrame` leaves the call's unwind
action unchanged. -/
theorem nounwind_cont_eq {canUnwind : Bool} {unwind : MirAst.UnwindAction}
    (h : canUnwind = true ∨ unwind = .unreachable) :
    (if canUnwind then translateUnwindAction unwind else Miri.MIR.UnwindAction.Unreachable) =
      translateUnwindAction unwind := by
  rcases h with h | h
  · simp [h]
  · subst h; cases canUnwind <;> rfl

inductive CallArgsAndPushSimRel
    (callerBody calleeBody : CapturedMir)
    (callerAf : StackFrame)
    (callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (destIdx : Local) (destDecl : LocalDecl)
    (targetOpt : Option BasicBlockIdx) (unwind : MirAst.UnwindAction)
    (m : AnnealStepState) :
    OperandsEvalResult →
    Miri.Interpreter.StepResult AnnealStepState (List (Miri.Interpreter.RvalueImmTy AnnealProv)) →
    Prop where
  | ub (m' : AnnealStepState) (msg : String) :
      CallArgsAndPushSimRel callerBody calleeBody callerAf callerMf restMfs
        destIdx destDecl targetOpt unwind m
        .ub
        (m', .error (.undefinedBehavior msg))
  | ok (argVals : List Value) (locals' : List LocalSlot)
      (callerMf' calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv)) :
      callerMf'.localsIdentity = callerMf.localsIdentity →
      callerMf'.returnContinuation = callerMf.returnContinuation →
      callerMf'.returnPlace = callerMf.returnPlace →
      (∀ (i : Nat) mp lay,
        callerMf'.locals[i]? =
          some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
        (∃ lay₀,
          callerMf.locals[i]? =
            some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀)) ∧
        get? locals' i = get? callerAf.locals i) →
      (MemoryAllocDisjoint callerMf → MemoryAllocDisjoint callerMf') →
      FrameRel callerBody m.machine { callerAf with locals := locals' } callerMf' →
      resolveCallerDestinationPlace callerBody restMfs.length callerMf'
        (translatePlace ⟨destIdx, .nil⟩) =
        .ok calleeMf.returnPlace →
      (∀ cf : SavedCallerFrame,
        cf.callerBody = callerBody →
        cf.frame = { callerAf with locals := locals' } →
        cf.destination = ⟨destIdx, .nil⟩ →
        CallerDestinationRel m.machine restMfs.length cf callerMf' calleeMf.returnPlace) →
      calleeMf.returnContinuation =
        .goto targetOpt
          (if calleeBody.fnAbi.canUnwind then translateUnwindAction unwind else .Unreachable) →
      (∀ (i : Nat) mp lay,
        calleeMf.locals[i]? ≠
          some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay)) →
      FrameRel calleeBody m.machine
        { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
        calleeMf →
      calleeMf.vaList = #[] →
      (let hooks := annealStackLifecycleHooksLM4_1 calleeBody.localDecls calleeBody.layouts
       let loadedCallee : Miri.Interpreter.LoadedBody :=
         ⟨.ofCanonicalIndex 0, translateBody calleeBody⟩
       let fnInst : Miri.Interpreter.CallInstance := ⟨.Item 0, #[]⟩
       let cont : Miri.Interpreter.ReturnContinuation :=
         .goto targetOpt
           (if calleeBody.fnAbi.canUnwind then translateUnwindAction unwind else .Unreachable)
       let rawRes :=
         (⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit).pushStackFrameRaw
           m.machine.memory hooks loadedCallee fnInst cont calleeMf.returnPlace defaultSpanRef
       rawRes.outcome = .ok () ∧
       rawRes.state = m.machine.memory ∧
       ∃ rawCalleeFrame,
         rawRes.stack.currentFrame? = some rawCalleeFrame ∧
         let calleeWithArgs := initCalleeArgLocals 1 argImms rawCalleeFrame
         let stackWithArgs : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit :=
           ⟨rawRes.stack.frames.pop.push calleeWithArgs⟩
         stackWithArgs.pushStackFrameDone m.machine.memory hooks =
           ⟨⟨⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩⟩, m.machine.memory, .ok ()⟩) →
      CallArgsAndPushSimRel callerBody calleeBody callerAf callerMf restMfs
        destIdx destDecl targetOpt unwind m
        (.ok argVals locals')
        ({ m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ }, .ok argImms)

theorem step_terminator_call_args_simulation_ok
    {callerBody calleeBody : CapturedMir}
    {callerAf : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {destIdx : Local} {destDecl : LocalDecl}
    {targetOpt : Option BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {m : AnnealStepState}
    {retDecl : LocalDecl} {restDecls : List LocalDecl}
    {calleeBb0 : BasicBlockData}
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hdest_decl : get? callerBody.localDecls destIdx = some destDecl)
    (argVals : List Value) (locals' : List LocalSlot)
    (callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv))
    (h_id : callerMf'.localsIdentity = topFrame.localsIdentity)
    (h_cont : callerMf'.returnContinuation = topFrame.returnContinuation)
    (h_rp : callerMf'.returnPlace = topFrame.returnPlace)
    (h_loc : ∀ (i : Nat) mp lay,
      callerMf'.locals[i]? = some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
      (∃ lay₀, topFrame.locals[i]? = some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀)) ∧
      get? locals' i = get? callerAf.locals i)
    (hdest_wf : CallerDestSlotWf m.machine callerMf' destIdx destDecl)
    (hdest_live : IsLiveFrameLocal callerMf' destIdx)
    (h_disj : MemoryAllocDisjoint topFrame → MemoryAllocDisjoint callerMf')
    (h_frame : FrameRel callerBody m.machine { callerAf with locals := locals' } callerMf')
    (hargs_rel : CalleeArgsRel calleeBody.layouts restDecls argVals argImms) :
    CallArgsAndPushSimRel callerBody calleeBody callerAf topFrame restMfs
      destIdx destDecl targetOpt unwind m
      (.ok argVals locals')
      ({ m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ }, .ok argImms) := by
  obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    h_frame.lookup_local hdest_decl
  have hlive_d := hdest_live mls_d hmls_d
  have hdest_resolved :
      ∃ returnPlace,
        resolveCallerDestinationPlace callerBody restMfs.length callerMf'
          (translatePlace ⟨destIdx, .nil⟩) = .ok returnPlace ∧
        ∀ cf : SavedCallerFrame,
          cf.callerBody = callerBody →
          cf.frame = { callerAf with locals := locals' } →
          cf.destination = ⟨destIdx, .nil⟩ →
          CallerDestinationRel m.machine restMfs.length cf callerMf' returnPlace := by
    cases hloc_d with
    | dead _ _ =>
      exact False.elim (hlive_d rfl)
    | immediate _ imm_d cachedLayout_d _ hval_d =>
      have hne_dead : slot_d ≠ .dead := by
        rcases hval_d with ⟨rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> nofun
      let returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv :=
        .frameLocal restMfs.length destIdx none
          (translateTy destDecl.ty callerBody.layouts)
          callerMf'.localsIdentity
      have hget_d : callerMf'.getLocal destIdx =
          .ok ⟨.live (.immediate imm_d), cachedLayout_d⟩ := by
        unfold Miri.Interpreter.Frame.getLocal
        simp [hlt_d, hmls_d_eq, pure, Except.pure]
      have hres_dest :
          resolveCallerDestinationPlace callerBody restMfs.length callerMf'
            (translatePlace ⟨destIdx, .nil⟩) = .ok returnPlace := by
        unfold resolveCallerDestinationPlace lookupLocalDeclLayout translatePlace
        dsimp only [List.map, List.toArray, Array.isEmpty_empty, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        rw [hdest_decl]
        dsimp only []
        rw [hget_d]
        rfl
      refine ⟨returnPlace, hres_dest, ?_⟩
      intro cf hcb hcf_fr hcf_dest
      have hdecl_cf : get? cf.callerBody.localDecls destIdx = some destDecl := by
        rw [hcb]; exact hdest_decl
      have hslot_cf : get? cf.frame.locals destIdx = some slot_d := by
        rw [hcf_fr]; exact hslot_d
      have hrp_cf :
          returnPlace =
            .frameLocal restMfs.length destIdx none
              (translateTy destDecl.ty cf.callerBody.layouts)
              callerMf'.localsIdentity := by
        dsimp only [returnPlace]
        rw [hcb]
      rw [hrp_cf]
      exact .immediate destIdx destDecl slot_d imm_d cachedLayout_d
        hcf_dest hdecl_cf hslot_cf hne_dead hmls_d
    | indirect _ mp_d cachedLayout_d _ hne_dead hmp_d =>
      rcases hdest_wf with himm_d | ⟨hprim_d, hnodup_d, halloc_d⟩
      · exact False.elim (himm_d _ hmls_d mp_d rfl)
      · let returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv :=
          .memory ⟨mp_d, translateTy destDecl.ty callerBody.layouts⟩
        have hget_d : callerMf'.getLocal destIdx =
            .ok ⟨.live (.indirect mp_d), cachedLayout_d⟩ := by
          unfold Miri.Interpreter.Frame.getLocal
          simp [hlt_d, hmls_d_eq, pure, Except.pure]
        have hres_dest :
            resolveCallerDestinationPlace callerBody restMfs.length callerMf'
              (translatePlace ⟨destIdx, .nil⟩) = .ok returnPlace := by
          unfold resolveCallerDestinationPlace lookupLocalDeclLayout translatePlace
          dsimp only [List.map, List.toArray, Array.isEmpty_empty, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          rw [hdest_decl]
          dsimp only []
          rw [hget_d]
          rfl
        have hmp_save := hmp_d
        rcases hmp_d with
          ⟨allocId, tag, baseAddr, relOffset, localAlloc,
            hprov, hmis, hmeta, hlive, hbase, hovf, hptr,
            hmut, halign, hbnd, _, _, _, _⟩
        obtain ⟨hlen, hpmap, words, hmask⟩ :=
          halloc_d mp_d cachedLayout_d allocId tag localAlloc hmls_d hprov hlive
        refine ⟨returnPlace, hres_dest, ?_⟩
        intro cf hcb hcf_fr hcf_dest
        have hdecl_cf : get? cf.callerBody.localDecls destIdx = some destDecl := by
          rw [hcb]; exact hdest_decl
        have hslot_cf : get? cf.frame.locals destIdx = some slot_d := by
          rw [hcf_fr]; exact hslot_d
        have hrp_cf :
            returnPlace = .memory ⟨mp_d, translateTy destDecl.ty cf.callerBody.layouts⟩ := by
          dsimp only [returnPlace]
          rw [hcb]
        have halign_cf :
            mp_d.ptr.offset.isAligned
              (translateTy destDecl.ty cf.callerBody.layouts).layout.align.abi = .ok true := by
          rw [hcb]; exact halign
        have hbnd_cf :
            relOffset.bytes.toNat +
              (translateTy destDecl.ty cf.callerBody.layouts).layout.size.bytes.toNat ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
          rw [hcb]; exact hbnd
        have hmp_cf :
            MemPlaceRel m.machine destDecl.ty cf.callerBody.layouts (slotOptVal slot_d) mp_d := by
          rw [hcb]; exact hmp_save
        exact .indirect destIdx destDecl slot_d mp_d cachedLayout_d returnPlace
          allocId tag baseAddr relOffset localAlloc words
          hcf_dest hdecl_cf hprim_d hslot_cf hne_dead hmls_d (Or.inl hrp_cf)
          hprov hmis hmeta hlive hnodup_d hbase hovf hptr hmut hlen hpmap hmask
          halign_cf hbnd_cf hmp_cf
  obtain ⟨returnPlace, hres_dest, hdest_rel_fn⟩ := hdest_resolved
  let hooks := annealStackLifecycleHooksLM4_1 calleeBody.localDecls calleeBody.layouts
  let loadedCallee : Miri.Interpreter.LoadedBody :=
    ⟨.ofCanonicalIndex 0, translateBody calleeBody⟩
  let fnInst : Miri.Interpreter.CallInstance := ⟨.Item 0, #[]⟩
  let cont : Miri.Interpreter.ReturnContinuation :=
    .goto targetOpt
      (if calleeBody.fnAbi.canUnwind then translateUnwindAction unwind else .Unreachable)
  let rawCalleeFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    Miri.Interpreter.Frame.create loadedCallee fnInst () cont returnPlace
      defaultSpanRef (.ofAllocationToken 0)
  let calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { rawCalleeFrame with
      locals := ⟨{ value := .live (.immediate .uninit), layout := none } ::
        calleeArgLocalStates restDecls argImms⟩
      location := .mir ⟨0, 0⟩ }
  have hcallee_no_ind :
      ∀ (i : Nat) mp lay,
        calleeMf.locals[i]? ≠
          some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) := by
    intro i mp lay
    dsimp only [calleeMf]
    cases i with
    | zero => simp
    | succ k =>
      simpa using calleeArgLocalStates_no_indirect restDecls argImms k mp lay
  have hfr_callee :
      FrameRel calleeBody m.machine
        { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
        calleeMf := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · unfold initLocals
      rw [hcallee_decls]
      simp [initLocalsAux, initLocalsAux_length]
    · dsimp only [calleeMf]
      rw [hcallee_decls]
      simp [calleeArgLocalStates_length]
    · intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
      unfold initLocals at hslot_i
      rw [hcallee_decls] at hdecl_i hslot_i
      dsimp only [calleeMf] at hmls_i
      cases i with
      | zero =>
        simp only [get?, initLocalsAux, List.getElem?_cons_zero, Option.some.injEq] at hdecl_i hslot_i
        have hmls0 : mls_i = { value := .live (.immediate .uninit), layout := none } := by
          simpa using hmls_i.symm
        subst hdecl_i hslot_i hmls0
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      | succ k =>
        simp only [get?, initLocalsAux, List.getElem?_cons_succ] at hdecl_i hslot_i
        have hmls_k : (calleeArgLocalStates restDecls argImms)[k]? = some mls_i := by
          simpa using hmls_i
        exact hargs_rel.locals_rel m.machine 1 (by omega) k decl_i slot_i mls_i
          hdecl_i hslot_i hmls_k
  refine .ok argVals locals' callerMf' calleeMf argImms
    h_id h_cont h_rp h_loc h_disj h_frame
    hres_dest hdest_rel_fn rfl hcallee_no_ind hfr_callee rfl ?_
  dsimp only []
  have hemp_false :
      (⟨restMfs.reverse ++ [callerMf']⟩ :
        Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).isEmpty =
        false := by
    unfold Array.isEmpty
    simp
  have hraw_eq :
      (⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ :
        Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit).pushStackFrameRaw
        m.machine.memory hooks loadedCallee fnInst cont calleeMf.returnPlace defaultSpanRef =
      ⟨⟨⟨(callerMf' :: restMfs).reverse ++ [rawCalleeFrame]⟩⟩, m.machine.memory, .ok ()⟩ := by
    have hrp_eq : calleeMf.returnPlace = returnPlace := rfl
    rw [hrp_eq]
    dsimp only [hooks, cont]
    unfold Miri.Interpreter.Stack.pushStackFrameRaw annealStackLifecycleHooksLM4_1
    simp only [Id.run, hemp_false, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      pure, Pure.pure]
    change ({ stack := ⟨(⟨restMfs.reverse ++ [callerMf']⟩ : Array _).push rawCalleeFrame⟩
              state := m.machine.memory
              outcome := .ok () } : Miri.Interpreter.StackRunResult _ _ _ _ _) = _
    rw [array_push_append_singleton restMfs callerMf' rawCalleeFrame]
  rw [hraw_eq]
  refine ⟨rfl, rfl, rawCalleeFrame,
    array_back?_append_singleton (callerMf' :: restMfs).reverse rawCalleeFrame, ?_⟩
  dsimp only []
  have hpop_eq :
      (⟨(callerMf' :: restMfs).reverse ++ [rawCalleeFrame]⟩ : Array _).pop =
        ⟨(callerMf' :: restMfs).reverse⟩ :=
    array_pop_append_singleton (callerMf' :: restMfs).reverse rawCalleeFrame
  rw [hpop_eq]
  have hraw_locals :
      rawCalleeFrame.locals =
        ⟨[{ value := .dead, layout := none }] ++
          List.replicate restDecls.length { value := .dead, layout := none }⟩ := by
    apply Array.ext'
    simp [rawCalleeFrame, Miri.Interpreter.Frame.create, loadedCallee, translateBody,
      hcallee_decls, List.replicate_succ]
  let calleeWithArgs : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { rawCalleeFrame with
      locals := ⟨{ value := .dead, layout := none } ::
        calleeArgLocalStates restDecls argImms⟩ }
  have hinit_args :
      initCalleeArgLocals 1 argImms rawCalleeFrame = calleeWithArgs :=
    hargs_rel.initCalleeArgLocals_eq [{ value := .dead, layout := none }]
      rawCalleeFrame hraw_locals
  rw [hinit_args]
  have hpush_args :
      (⟨(callerMf' :: restMfs).reverse⟩ : Array _).push calleeWithArgs =
        ⟨(callerMf' :: restMfs).reverse ++ [calleeWithArgs]⟩ := by
    apply Array.ext'
    simp
  rw [hpush_args]
  have hlt0 : 0 < calleeWithArgs.locals.size := by
    dsimp [calleeWithArgs]
    simp
  have hget0 : calleeWithArgs.getLocal 0 = .ok { value := .dead, layout := none } := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [calleeWithArgs, pure, Except.pure]
  have hbody_loc0 : calleeWithArgs.body.locals[0]? = some (encodeTyId retDecl.ty) := by
    dsimp only [calleeWithArgs, rawCalleeFrame, Miri.Interpreter.Frame.create,
      loadedCallee, translateBody]
    rw [hcallee_decls]
    rfl
  let calleeLive0 : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { rawCalleeFrame with
      locals := ⟨{ value := .live (.immediate .uninit), layout := none } ::
        calleeArgLocalStates restDecls argImms⟩ }
  have hrep0 :
      calleeWithArgs.replaceLocalValue 0 (.live (.immediate .uninit)) = .ok calleeLive0 := by
    rw [frame_replaceLocalValue_of_lt calleeWithArgs 0 hlt0]
    congr 1
  have hstorage0 :
      calleeWithArgs.storageLive m.machine.memory
        (annealLocalStorageHooks calleeBody.localDecls calleeBody.layouts) 0 =
        ⟨calleeLive0, m.machine.memory, .ok ()⟩ := by
    simp only [Miri.Interpreter.Frame.storageLive, Miri.Interpreter.Frame.storageLiveDyn,
      hget0, hbody_loc0,
      annealLocalStorageHooks_veryTriviallySized, annealLocalStorageHooks_afterLocalWrite,
      Miri.Interpreter.MemPlaceMeta.hasMeta, hrep0, Miri.Interpreter.Frame.deallocateLocal,
      Id.run, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hlt_bb0 : 0 < calleeLive0.body.basicBlocks.size := by
    dsimp only [calleeLive0, rawCalleeFrame, Miri.Interpreter.Frame.create,
      loadedCallee, translateBody]
    rw [get?_eq_getElem?] at hcallee_bb0
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hcallee_bb0
    simpa using hlt
  have hset_loc0 :
      calleeLive0.setLocation (.mir .start) = .ok calleeMf := by
    unfold Miri.Interpreter.Frame.setLocation Miri.MIR.Location.start
    simp only [hlt_bb0, ↓reduceDIte, Nat.zero_le, ↓reduceIte, pure, Except.pure]
    rfl
  unfold Miri.Interpreter.Stack.pushStackFrameDone
  dsimp only [hooks, annealStackLifecycleHooksLM4_1]
  simp only [Id.run, Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton (callerMf' :: restMfs).reverse calleeWithArgs,
    pure_bind, hstorage0,
    array_pop_append_singleton (callerMf' :: restMfs).reverse calleeWithArgs]
  have hpush_live0 :
      (⟨(callerMf' :: restMfs).reverse⟩ : Array _).push calleeLive0 =
        ⟨(callerMf' :: restMfs).reverse ++ [calleeLive0]⟩ := by
    apply Array.ext'
    simp
  rw [hpush_live0]
  have hforIn_empty :
      ∀ (b : Option (Miri.Interpreter.StackRunResult AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory Unit) ×
          (Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit × AnnealMemory))
        (f : Miri.MIR.LocalId → _ → Id (ForInStep _)),
        forIn (#[] : Array Miri.MIR.LocalId) b f = pure b :=
    fun _ _ => rfl
  rw [hforIn_empty]
  dsimp only [pure, Pure.pure, bind, Bind.bind, Miri.Interpreter.Stack.updateCurrentLocation]
  rw [array_back?_append_singleton (callerMf' :: restMfs).reverse calleeLive0]
  dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [hset_loc0]
  simp only [array_size_append_singleton, Nat.add_sub_cancel, Nat.lt_succ_self,
    ↓reduceDIte, array_set_last_append_singleton]

theorem step_terminator_call_args_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    {destIdx : Local} {destDecl : LocalDecl}
    {targetOpt : Option BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl}
    {calleeBb0 : BasicBlockData}
    {argOps : List MirAst.Operand}
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (hmfs : m.stack.frames.toList.reverse = topFrame :: restMfs)
    (hdest_wf : CallerDestSlotWf m.machine topFrame destIdx destDecl)
    (hdest_live : IsLiveFrameLocal topFrame destIdx)
    (hwt_args : WellTypedCallArgs (activeMirBody rootBody s) calleeBody topFrame argOps restDecls) :
    CallArgsAndPushSimRel (activeMirBody rootBody s) calleeBody s.frame topFrame restMfs
      destIdx destDecl targetOpt unwind m
      (evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
        (activeMirBody rootBody s).layouts s.memory.callerLocals)
      (Miri.Interpreter.runRvalue
        (annealEvalCallArgsLM4_1 (activeMirBody rootBody s).localDecls
          (activeMirBody rootBody s).layouts (argOps.map translateOperand)) m) := by
  rcases hstate with ⟨_, _, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rw [hmfs] at hforall
  cases hforall with
  | cons hframe _ =>
    dsimp only at hframe
    have harr := array_eq_of_toList_reverse_cons hmfs
    have heval := evalCallArgs_simulation hwt_args harr hframe
      s.memory.borrows s.memory.globals s.memory.callerLocals
    generalize ha_ops :
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
        (activeMirBody rootBody s).layouts s.memory.callerLocals = aOps at heval ⊢
    generalize hm_ops :
      Miri.Interpreter.runRvalue
        (annealEvalCallArgsLM4_1 (activeMirBody rootBody s).localDecls
          (activeMirBody rootBody s).layouts (argOps.map translateOperand)) m = mOps at heval ⊢
    cases heval with
    | ub m' msg => exact .ub m' msg
    | ok argVals locals' callerMf' argImms h_id h_cont h_rp h_loc himm_mono hlive_mono h_disj h_frame hargs_rel =>
      exact step_terminator_call_args_simulation_ok
        hcallee_decls hcallee_bb0 hdest_decl
        argVals locals' callerMf' argImms
        h_id h_cont h_rp h_loc
        (hdest_wf.mono_evalArgs (himm_mono destIdx) (fun mp lay hi => (h_loc destIdx mp lay hi).1))
        (hlive_mono destIdx hdest_live)
        h_disj h_frame hargs_rel

/-- **Theorem 5 (`step_terminator_call_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.call func argOps ⟨destIdx, .nil⟩ (some targetBb) unwind` where
`extractCalleeDefPath? func = some defPath` and `findCallee? s.memory.callees defPath = some calleeBody`:
* faults with undefined behavior in both machines if evaluating `argOps` hits a
  `.dead` or `.uninit` argument local;
* when argument evaluation succeeds, resolves `⟨destIdx, .nil⟩` to either a
  `.frameLocal` (when `destIdx` is `.immediate`) or `.memory ⟨mp, destLay⟩` (when
  `destIdx` is `.indirect`), pushes `SavedCallerFrame` onto `s.memory.callStack`,
  sets `s.memory.activeCallee = some calleeBody`, initializes the callee frame
  at `(0, 0)` via `Stack.pushStackFrameRaw` + `initCalleeArgLocals` +
  `Stack.pushStackFrameDone`, and preserves `MultiFrameStateRel` at depth `d + 1`.

`hcallee_unwind` (`calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable`)
excludes calls to nounwind callees with an unwinding `unwind` action, for which
canonical `lean-miri` (`Call.initStackFrame`) rewrites the callee continuation to
`.Unreachable` while Stage-1 keeps `returnUnwind := unwind`
(`WitnessLM4_1.wit_lm4_1_nounwind_callee_unwind_divergence`). The statement is
generic in the registered function pointers `fnPtrs`, so it composes with
`annealStepHooksForState rootBody s` (`fnPtrs := s.memory.fnPtrs`). -/
theorem step_terminator_call_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {func : MirAst.Operand} {argOps : List MirAst.Operand}
    {destIdx : Local} {destDecl : LocalDecl}
    {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {defPath : DefPath} {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl}
    {calleeBb0 : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call func argOps ⟨destIdx, .nil⟩ (some targetBb) unwind)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hcallee : findCallee? s.memory.callees defPath = some calleeBody)
    (htypeArgs : extractCalleeTypeArgs func = .nil := by rfl)
    (htparam : calleeBody.typeParamCount = 0 := by rfl)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hdest_wf : ∀ tf, m.stack.frames.back? = some tf →
      CallerDestSlotWf m.machine tf destIdx destDecl)
    (hdest_live : ∀ tf, m.stack.frames.back? = some tf → IsLiveFrameLocal tf destIdx)
    (hwt_args : ∀ tf, m.stack.frames.back? = some tf →
      WellTypedCallArgs (activeMirBody rootBody s) calleeBody tf argOps restDecls)
    (hcallee_unwind : calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable :=
      by first | exact Or.inl rfl | exact Or.inr rfl)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  have hstate_copy := hstate
  rcases hstate with
    ⟨topFrame, hback, _, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨callerMf, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some callerMf := by rw [harr]; simp
      have htf_eq : topFrame = callerMf := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      have hargs_sim :=
        step_terminator_call_args_simulation (targetOpt := some targetBb) (unwind := unwind)
          hstate_copy hcallee_decls hcallee_bb0 hdest_decl
          callerMf restMfs hmfs
          (hdest_wf callerMf hback)
          (hdest_live callerMf hback)
          (hwt_args callerMf hback)
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (translateOperand func)
              (argOps.map fun a => ⟨defaultSpanRef, translateOperand a⟩).toArray
              (translatePlace ⟨destIdx, .nil⟩) (some targetBb) (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator
        rw [hterm]
        rfl
      generalize ha_ops :
        evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
          (activeMirBody rootBody s).layouts s.memory.callerLocals = aOps at hargs_sim ⊢
      generalize hm_ops :
        Miri.Interpreter.runRvalue
          (annealEvalCallArgsLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts (argOps.map translateOperand)) m = mOps at hargs_sim
      cases hargs_sim with
      | ub m' msg =>
        have hcall :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m fnPtrs =
            (m', .error (.undefinedBehavior msg)) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]
          dsimp only []
          rw [hframe.location_eq]
          dsimp only []
          rw [hbb]
          dsimp only []
          rw [hterm, htk]
          dsimp only []
          rw [hfunc]
          dsimp only []
          rw [hm_ops]
        unfold evalTerminator resolveCallTarget Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        dsimp only [Id.run]
        rw [hfunc]
        dsimp only []
        rw [ha_ops, hcall]
        exact StepRelMultiFrame.ub _ _
      | ok argVals locals' callerMf' calleeMf argImms
          hid_eq hrc_eq hrp_eq hloc_sub hd_fn hfr_caller'
          hres_dest hdest_rel_fn hrc_callee hcallee_no_ind hfr_callee _ hpush_spec =>
        have hind_sub :
            ∀ (i : Nat) mp lay,
              callerMf'.locals[i]? =
                some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
              ∃ lay₀,
                callerMf.locals[i]? =
                  some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀) :=
          fun i mp lay hi => (hloc_sub i mp lay hi).1
        obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
        have hcall :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m fnPtrs =
            ({ stack := ⟨⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩⟩
               machine := m.machine }, .ok ()) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]
          dsimp only []
          rw [hframe.location_eq]
          dsimp only []
          rw [hbb]
          dsimp only []
          rw [hterm, htk]
          dsimp only []
          rw [hfunc]
          dsimp only []
          rw [hm_ops]
          dsimp only []
          rw [hcallee]
          dsimp only []
          unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
          dsimp only []
          have hback_after :
              (⟨restMfs.reverse ++ [callerMf']⟩ : Array _).back? = some callerMf' :=
            array_back?_append_singleton restMfs.reverse callerMf'
          have hsize_after :
              (⟨restMfs.reverse ++ [callerMf']⟩ :
                Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
                restMfs.length := by
            simp
          rw [hback_after]
          dsimp only []
          rw [hsize_after, hres_dest]
          dsimp only []
          rw [hraw_ok]
          dsimp only []
          unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
          rw [hraw_curr]
          dsimp only []
          rw [hraw_state, hdone_eq]
        unfold evalTerminator resolveCallTarget Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        dsimp only [Id.run]
        rw [hfunc]
        dsimp only []
        rw [ha_ops]
        dsimp only []
        rw [htypeArgs,
          lookupCallee_nil_eq_of_findCallee_some _ _ _ _ hcallee htparam,
          hcall]
        dsimp only [checkCalleeTargetCompatible, pushCalleeFrame]
        have hsize_ne :
            ((⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).size == m.stack.frames.size) =
              false := by
          rw [harr]
          simp
        simp only [hsize_ne, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Except.map, pure, Pure.pure]
        apply StepRelMultiFrame.step
        let savedCaller : SavedCallerFrame :=
          { callerBody := activeMirBody rootBody s
            frame := { s.frame with locals := locals' }
            destination := ⟨destIdx, .nil⟩
            returnTarget := targetBb
            calleeProtectors := s.memory.activeProtectors
            returnUnwind := unwind
            isDiverging := false }
        have hlinks_caller' :
            CallerStackLinksRel rootBody m.machine savedCaller.callerBody savedCaller.frame
              s.memory.callStack s.memory.activeProtectors (callerMf' :: restMfs) :=
          hlinks.update_top_frame hrc_eq hrp_eq hid_eq hfr_caller'
            (fun mp0 lay0 h0 => ⟨(hloc_sub 0 mp0 lay0 h0).1, Or.inl (hloc_sub 0 mp0 lay0 h0).2⟩)
        have hdest_rel :
            CallerDestinationRel m.machine restMfs.length savedCaller callerMf' calleeMf.returnPlace :=
          hdest_rel_fn savedCaller rfl rfl rfl
        have hlinks_post :
            CallerStackLinksRel rootBody m.machine calleeBody
              { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
              (savedCaller :: s.memory.callStack)
              ([] ++ s.memory.activeProtectors)
              (calleeMf :: callerMf' :: restMfs) :=
          .cons calleeBody
            { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
            savedCaller s.memory.callStack [] s.memory.activeProtectors
            calleeMf callerMf' restMfs
            (by rw [hrc_callee, nounwind_cont_eq hcallee_unwind] <;> rfl) hdest_rel hfr_callee
            (fun mp0 lay0 _ _ _ h0 _ _ _ => False.elim (hcallee_no_ind 0 mp0 lay0 h0))
            rfl (by intro _ h; cases h) hlinks_caller'
        have hdisj_orig : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ := by
          rw [← harr]; exact hdisj
        have hd_callerMf : MemoryAllocDisjoint callerMf := by
          apply hdisj_orig.intra_frame callerMf
          simp
        have hdisj_caller' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
          hdisj_orig.replace_top (hd_fn hd_callerMf) hind_sub
        have hd_calleeMf : MemoryAllocDisjoint calleeMf := by
          intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
          exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
        have hdisj_post :
            MultiFrameAllocDisjoint ⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ := by
          have harr_eq :
              (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _) =
                ⟨(restMfs.reverse ++ [callerMf']) ++ [calleeMf]⟩ := by
            apply Array.ext'
            simp [List.reverse_cons]
          rw [harr_eq]
          refine ⟨?_, ?_⟩
          · intro mf hmf
            rcases List.mem_append.mp hmf with hmem_old | hsingle
            · exact hdisj_caller'.intra_frame mf hmem_old
            · rcases List.mem_singleton.mp hsingle with rfl
              exact hd_calleeMf
          · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
            have hlen_old : (restMfs.reverse ++ [callerMf']).length = restMfs.length + 1 := by
              simp
            by_cases hf₁_top : f₁ = restMfs.length + 1
            · subst hf₁_top
              rw [← hlen_old, array_getElem?_append_singleton_last] at hf₁
              injection hf₁ with hmf₁_eq
              subst hmf₁_eq
              exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
            · by_cases hf₂_top : f₂ = restMfs.length + 1
              · subst hf₂_top
                rw [← hlen_old, array_getElem?_append_singleton_last] at hf₂
                injection hf₂ with hmf₂_eq
                subst hmf₂_eq
                exact False.elim (hcallee_no_ind j mp₂ lay₂ hj)
              · have hlt₁ : f₁ < (restMfs.reverse ++ [callerMf']).length := by
                  have := Array.getElem?_eq_some_iff.mp hf₁ |>.1
                  simp at this
                  omega
                have hlt₂ : f₂ < (restMfs.reverse ++ [callerMf']).length := by
                  have := Array.getElem?_eq_some_iff.mp hf₂ |>.1
                  simp at this
                  omega
                rw [array_getElem?_append_singleton_of_lt _ _ hlt₁] at hf₁
                rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
                exact hdisj_caller'.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
        have hrev_post :
            (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).toList.reverse =
              calleeMf :: callerMf' :: restMfs :=
          array_toList_reverse_append_singleton (callerMf' :: restMfs) calleeMf
        refine .mk calleeMf
          (array_back?_append_singleton (callerMf' :: restMfs).reverse calleeMf)
          (fun hnil => nomatch hnil)
          (fun _ => rfl)
          (by
            unfold FrameStackRel annealFrameStackTopDown activeMirBody
            rw [hrev_post]
            exact hlinks_post.toForall2)
          (by
            unfold activeMirBody
            rw [hrev_post]
            exact hlinks_post)
          hdisj_post htb hvalid hcid_pos hcid_act hcid_bor
          (hbt.of_pushFrame rfl)

/-- **Theorem 5b (`step_terminator_call_diverging_simulation`)**: Stage-1
`Trusted` executes a *diverging* `TerminatorKind.call func argOps ⟨destIdx, .nil⟩
none unwind` (`target = none`, return type `!`) to a linked callee natively
(`Terminators.lean:3172-3217`): it evaluates the arguments, resolves
`calleeBody` via `lookupCallee`, and pushes a diverging
`SavedCallerFrame` (`pushDivergingCalleeFrame`: `isDiverging := true`,
`returnTarget := 0`, `returnUnwind := unwind`). At arbitrary stack depth under
`MultiFrameStateRel rootBody s m`:
* both machines fault with undefined behavior if evaluating `argOps` hits a
  `.dead` or `.uninit` argument local;
* otherwise `lean-miri` (`annealEvalCallLM4_1` / `annealPushCalleeFrameLM4_1`)
  pushes the callee frame with return continuation `.goto none unwind` (Miri's
  `ReturnContinuation::Goto { ret: None, unwind }`), and both machines step to
  `MultiFrameStateRel`-related states at depth `d + 1`.

Composed with the `cf.isDiverging = true` branch of
`step_terminator_return_callee_simulation`, a later normal `return` from the
callee faults with UB in both machines (Stage-1 `Terminators.lean:3011-3012`
vs. `ControlFlow.returnToBlock none`), so that branch is reached from genuine
call steps rather than only from hand-built states
(`WitnessLM4_1.wit_lm4_1_diverging_call_then_return_ub`). -/
theorem step_terminator_call_diverging_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {func : MirAst.Operand} {argOps : List MirAst.Operand}
    {destIdx : Local} {destDecl : LocalDecl}
    {unwind : MirAst.UnwindAction}
    {defPath : DefPath} {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl}
    {calleeBb0 : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call func argOps ⟨destIdx, .nil⟩ none unwind)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hcallee : findCallee? s.memory.callees defPath = some calleeBody)
    (htypeArgs : extractCalleeTypeArgs func = .nil := by rfl)
    (htparam : calleeBody.typeParamCount = 0 := by rfl)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hdest_wf : ∀ tf, m.stack.frames.back? = some tf →
      CallerDestSlotWf m.machine tf destIdx destDecl)
    (hdest_live : ∀ tf, m.stack.frames.back? = some tf → IsLiveFrameLocal tf destIdx)
    (hwt_args : ∀ tf, m.stack.frames.back? = some tf →
      WellTypedCallArgs (activeMirBody rootBody s) calleeBody tf argOps restDecls)
    (hcallee_unwind : calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable :=
      by first | exact Or.inl rfl | exact Or.inr rfl)
    (fnPtrs : List FnPtrEntry := .nil) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)
          fnPtrs) () m) := by
  have hstate_copy := hstate
  rcases hstate with
    ⟨topFrame, hback, _, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨callerMf, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some callerMf := by rw [harr]; simp
      have htf_eq : topFrame = callerMf := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      have hargs_sim :=
        step_terminator_call_args_simulation (targetOpt := none) (unwind := unwind)
          hstate_copy hcallee_decls hcallee_bb0 hdest_decl
          callerMf restMfs hmfs
          (hdest_wf callerMf hback)
          (hdest_live callerMf hback)
          (hwt_args callerMf hback)
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (translateOperand func)
              (argOps.map fun a => ⟨defaultSpanRef, translateOperand a⟩).toArray
              (translatePlace ⟨destIdx, .nil⟩) none (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator
        rw [hterm]
        rfl
      generalize ha_ops :
        evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
          (activeMirBody rootBody s).layouts s.memory.callerLocals = aOps at hargs_sim ⊢
      generalize hm_ops :
        Miri.Interpreter.runRvalue
          (annealEvalCallArgsLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts (argOps.map translateOperand)) m = mOps at hargs_sim
      cases hargs_sim with
      | ub m' msg =>
        have hcall :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m fnPtrs =
            (m', .error (.undefinedBehavior msg)) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]
          dsimp only []
          rw [hframe.location_eq]
          dsimp only []
          rw [hbb]
          dsimp only []
          rw [hterm, htk]
          dsimp only []
          rw [hfunc]
          dsimp only []
          rw [hm_ops]
        unfold evalTerminator resolveCallTarget Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        dsimp only [Id.run]
        rw [hfunc]
        dsimp only []
        rw [ha_ops, hcall]
        exact StepRelMultiFrame.ub _ _
      | ok argVals locals' callerMf' calleeMf argImms
          hid_eq hrc_eq hrp_eq hloc_sub hd_fn hfr_caller'
          hres_dest hdest_rel_fn hrc_callee hcallee_no_ind hfr_callee _ hpush_spec =>
        have hind_sub :
            ∀ (i : Nat) mp lay,
              callerMf'.locals[i]? =
                some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
              ∃ lay₀,
                callerMf.locals[i]? =
                  some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀) :=
          fun i mp lay hi => (hloc_sub i mp lay hi).1
        obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
        have hcall :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m fnPtrs =
            ({ stack := ⟨⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩⟩
               machine := m.machine }, .ok ()) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]
          dsimp only []
          rw [hframe.location_eq]
          dsimp only []
          rw [hbb]
          dsimp only []
          rw [hterm, htk]
          dsimp only []
          rw [hfunc]
          dsimp only []
          rw [hm_ops]
          dsimp only []
          rw [hcallee]
          dsimp only []
          unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
          dsimp only []
          have hback_after :
              (⟨restMfs.reverse ++ [callerMf']⟩ : Array _).back? = some callerMf' :=
            array_back?_append_singleton restMfs.reverse callerMf'
          have hsize_after :
              (⟨restMfs.reverse ++ [callerMf']⟩ :
                Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
                restMfs.length := by
            simp
          rw [hback_after]
          dsimp only []
          rw [hsize_after, hres_dest]
          dsimp only []
          rw [hraw_ok]
          dsimp only []
          unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
          rw [hraw_curr]
          dsimp only []
          rw [hraw_state, hdone_eq]
        unfold evalTerminator resolveCallTarget Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        dsimp only [Id.run]
        rw [hfunc]
        dsimp only []
        rw [ha_ops]
        dsimp only []
        rw [htypeArgs,
          lookupCallee_nil_eq_of_findCallee_some _ _ _ _ hcallee htparam,
          hcall]
        dsimp only [checkCalleeTargetCompatible, pushDivergingCalleeFrame]
        have hsize_ne :
            ((⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).size == m.stack.frames.size) =
              false := by
          rw [harr]
          simp
        simp only [hsize_ne, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Except.map, pure, Pure.pure]
        apply StepRelMultiFrame.step
        let savedCaller : SavedCallerFrame :=
          { callerBody := activeMirBody rootBody s
            frame := { s.frame with locals := locals' }
            destination := ⟨destIdx, .nil⟩
            returnTarget := 0
            calleeProtectors := s.memory.activeProtectors
            returnUnwind := unwind
            isDiverging := true }
        have hlinks_caller' :
            CallerStackLinksRel rootBody m.machine savedCaller.callerBody savedCaller.frame
              s.memory.callStack s.memory.activeProtectors (callerMf' :: restMfs) :=
          hlinks.update_top_frame hrc_eq hrp_eq hid_eq hfr_caller'
            (fun mp0 lay0 h0 => ⟨(hloc_sub 0 mp0 lay0 h0).1, Or.inl (hloc_sub 0 mp0 lay0 h0).2⟩)
        have hdest_rel :
            CallerDestinationRel m.machine restMfs.length savedCaller callerMf' calleeMf.returnPlace :=
          hdest_rel_fn savedCaller rfl rfl rfl
        have hlinks_post :
            CallerStackLinksRel rootBody m.machine calleeBody
              { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
              (savedCaller :: s.memory.callStack)
              ([] ++ s.memory.activeProtectors)
              (calleeMf :: callerMf' :: restMfs) :=
          .cons calleeBody
            { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
            savedCaller s.memory.callStack [] s.memory.activeProtectors
            calleeMf callerMf' restMfs
            (by rw [hrc_callee, nounwind_cont_eq hcallee_unwind] <;> rfl) hdest_rel hfr_callee
            (fun mp0 lay0 _ _ _ h0 _ _ _ => False.elim (hcallee_no_ind 0 mp0 lay0 h0))
            rfl (by intro _ h; cases h) hlinks_caller'
        have hdisj_orig : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ := by
          rw [← harr]; exact hdisj
        have hd_callerMf : MemoryAllocDisjoint callerMf := by
          apply hdisj_orig.intra_frame callerMf
          simp
        have hdisj_caller' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
          hdisj_orig.replace_top (hd_fn hd_callerMf) hind_sub
        have hd_calleeMf : MemoryAllocDisjoint calleeMf := by
          intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
          exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
        have hdisj_post :
            MultiFrameAllocDisjoint ⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ := by
          have harr_eq :
              (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _) =
                ⟨(restMfs.reverse ++ [callerMf']) ++ [calleeMf]⟩ := by
            apply Array.ext'
            simp [List.reverse_cons]
          rw [harr_eq]
          refine ⟨?_, ?_⟩
          · intro mf hmf
            rcases List.mem_append.mp hmf with hmem_old | hsingle
            · exact hdisj_caller'.intra_frame mf hmem_old
            · rcases List.mem_singleton.mp hsingle with rfl
              exact hd_calleeMf
          · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
            have hlen_old : (restMfs.reverse ++ [callerMf']).length = restMfs.length + 1 := by
              simp
            by_cases hf₁_top : f₁ = restMfs.length + 1
            · subst hf₁_top
              rw [← hlen_old, array_getElem?_append_singleton_last] at hf₁
              injection hf₁ with hmf₁_eq
              subst hmf₁_eq
              exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
            · by_cases hf₂_top : f₂ = restMfs.length + 1
              · subst hf₂_top
                rw [← hlen_old, array_getElem?_append_singleton_last] at hf₂
                injection hf₂ with hmf₂_eq
                subst hmf₂_eq
                exact False.elim (hcallee_no_ind j mp₂ lay₂ hj)
              · have hlt₁ : f₁ < (restMfs.reverse ++ [callerMf']).length := by
                  have := Array.getElem?_eq_some_iff.mp hf₁ |>.1
                  simp at this
                  omega
                have hlt₂ : f₂ < (restMfs.reverse ++ [callerMf']).length := by
                  have := Array.getElem?_eq_some_iff.mp hf₂ |>.1
                  simp at this
                  omega
                rw [array_getElem?_append_singleton_of_lt _ _ hlt₁] at hf₁
                rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
                exact hdisj_caller'.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
        have hrev_post :
            (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).toList.reverse =
              calleeMf :: callerMf' :: restMfs :=
          array_toList_reverse_append_singleton (callerMf' :: restMfs) calleeMf
        refine .mk calleeMf
          (array_back?_append_singleton (callerMf' :: restMfs).reverse calleeMf)
          (fun hnil => nomatch hnil)
          (fun _ => rfl)
          (by
            unfold FrameStackRel annealFrameStackTopDown activeMirBody
            rw [hrev_post]
            exact hlinks_post.toForall2)
          (by
            unfold activeMirBody
            rw [hrev_post]
            exact hlinks_post)
          hdisj_post htb hvalid hcid_pos hcid_act hcid_bor
          (hbt.of_pushFrame rfl)

/-! ## 6. Arbitrary-Depth Multi-Frame `.continue_` & `.terminate` Unwinding Simulation -/

private abbrev miriFinishStep {S : Type}
    (result : Miri.Interpreter.StepResult S Unit) :
    Miri.Interpreter.StepResult S Bool :=
  (result.1, result.2.map fun _ => true)

/-- `annealControlHooksLM4_1.returnOperand` succeeds on a live `_0` whenever the
active frame sits at `location = .unwinding span` (`CallLM4_1.lean:2165`). -/
theorem annealControlHooks_returnOperand_unwinding_live_back
    {body : CapturedMir}
    {poppedFrame : Miri.TreeBorrows.FrameState}
    {decl0 : LocalDecl}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {span : Miri.MIR.SpanRef}
    (hback : m.stack.frames.back? = some topFrame)
    (hloc : topFrame.location = .unwinding span)
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live op, lay⟩)
    (hdecl0 : get? body.localDecls 0 = some decl0) :
    (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m =
      (m, .ok op) := by
  unfold annealControlHooksLM4_1 annealReturnOperandLM4_1
    lookupLocalDeclLayout Miri.Interpreter.Stack.currentFrame?
  dsimp only
  rw [hback]
  dsimp only
  rw [hget0]
  dsimp only
  rcases op with imm | mp
  · cases imm with
    | scalar _ => rfl
    | scalarPair _ _ => rfl
    | uninit =>
      dsimp only
      rw [hdecl0, hloc]
      dsimp only
      split <;> rfl
  · rfl

theorem returnFromCurrentFrame_lm4_1_unwind_continue_ok
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {retOpt : Option Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hretCont : calleeMf.returnContinuation = .goto retOpt .Continue)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
         machine := mach₂ },
       .ok ()) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  have hbodySpan :
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).bodySpan callerMf =
        .ok defaultSpanRef := rfl
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hcleanup, hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton, hbodySpan]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_lm4_1_unwind_terminate_err
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {retOpt : Option Miri.MIR.BasicBlockId} {reason : Miri.MIR.UnwindTerminateReason}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hbody : calleeMf.body = translateBody body)
    (hloc : calleeMf.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = true)
    (hretCont : calleeMf.returnContinuation = .goto retOpt (.Terminate reason))
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
         machine := mach₂ },
       .error (.unsupported "unwindTerminate")) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  have hbodySpan :
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).bodySpan callerMf =
        .ok defaultSpanRef := rfl
  have htermHook :
      ∀ st,
        (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).unwindTerminate () reason st =
          (st, .error (.unsupported "unwindTerminate")) := fun _ => rfl
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hcleanup, hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton, hbodySpan, htermHook]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_unwinding_loc_root_ub
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {m : AnnealStepState}
    {rootMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {span : Miri.MIR.SpanRef}
    (hframes : m.stack.frames = #[rootMf])
    (hloc : rootMf.location = .unwinding span) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () true m =
      (m, .error (.undefinedBehavior "unwinding past the topmost stack frame")) := by
  have hback : m.stack.frames.back? = some rootMf := by rw [hframes]; rfl
  have hsize : (m.stack.frames.size == 1) = true := by rw [hframes]; rfl
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, hsize]

theorem returnFromCurrentFrame_lm4_1_unwinding_loc_cleanup_ok
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {span : Miri.MIR.SpanRef}
    {retOpt : Option Miri.MIR.BasicBlockId} {cleanupBb : Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hloc : calleeMf.location = .unwinding span)
    (hretCont : calleeMf.returnContinuation = .goto retOpt (.Cleanup cleanupBb))
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .mir ⟨cleanupBb, 0⟩ }]⟩⟩
         machine := mach₂ },
       .ok ()) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.goToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_lm4_1_unwinding_loc_unreachable_ub
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {span : Miri.MIR.SpanRef}
    {retOpt : Option Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hloc : calleeMf.location = .unwinding span)
    (hretCont : calleeMf.returnContinuation = .goto retOpt .Unreachable)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ },
       .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock]

theorem returnFromCurrentFrame_lm4_1_unwinding_loc_continue_ok
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {span : Miri.MIR.SpanRef}
    {retOpt : Option Miri.MIR.BasicBlockId}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hloc : calleeMf.location = .unwinding span)
    (hretCont : calleeMf.returnContinuation = .goto retOpt .Continue)
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
         machine := mach₂ },
       .ok ()) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc]
  have hbodySpan :
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).bodySpan callerMf =
        .ok defaultSpanRef := rfl
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton, hbodySpan]
  congr 3
  apply Array.ext'
  simp

theorem returnFromCurrentFrame_lm4_1_unwinding_loc_terminate_err
    {body : CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {m m₁ : AnnealStepState}
    {mach₂ : AnnealMachine}
    {xs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {span : Miri.MIR.SpanRef}
    {retOpt : Option Miri.MIR.BasicBlockId} {reason : Miri.MIR.UnwindTerminateReason}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = ⟨(callerMf :: xs).reverse ++ [calleeMf]⟩)
    (hloc : calleeMf.location = .unwinding span)
    (hretCont : calleeMf.returnContinuation = .goto retOpt (.Terminate reason))
    (hop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).returnOperand () m = (m, .ok op))
    (hpop : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).popFrame () m = (m₁, .ok calleeMf))
    (hclean : (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).cleanupFrame () true calleeMf m₁ =
      ({ stack := ⟨⟨xs.reverse ++ [callerMf]⟩⟩, machine := mach₂ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame) () true m =
      ({ stack := ⟨⟨xs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
         machine := mach₂ },
       .error (.unsupported "unwindTerminate")) := by
  have hback : m.stack.frames.back? = some calleeMf := by rw [hframes]; simp
  have hsize_ne : (m.stack.frames.size == 1) = false := by
    rw [hframes]; simp [List.reverse_cons]
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?
  rw [hback]
  dsimp only
  rw [hloc]
  have hbodySpan :
      (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).bodySpan callerMf =
        .ok defaultSpanRef := rfl
  have htermHook :
      ∀ st,
        (annealControlHooksLM4_1 body.localDecls body.layouts poppedFrame).unwindTerminate () reason st =
          (st, .error (.unsupported "unwindTerminate")) := fun _ => rfl
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    hsize_ne, hop, hpop, hclean, hretCont,
    Miri.Interpreter.ControlFlow.unwindToBlock,
    Miri.Interpreter.ControlFlow.setLocation,
    Miri.Interpreter.Stack.currentFrame?,
    array_back?_append_singleton, array_pop_append_singleton, hbodySpan, htermHook]
  congr 3
  apply Array.ext'
  simp

/-- Frame-level side conditions needed for `lean-miri`'s `returnFromCurrentFrame`
along an arbitrary multi-frame unwind chain (`vaList = #[]` across the Miri stack,
and `_0` declared and live in every saved caller frame that may be popped). -/
structure UnwindChainWf (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState) : Prop where
  vaList_empty : ∀ mf ∈ m.stack.frames.toList, mf.vaList = #[]
  cur_decl0 : s.memory.callStack ≠ [] → ∃ decl0, get? (activeMirBody rootBody s).localDecls 0 = some decl0
  cur_live0 : s.memory.callStack ≠ [] → get? s.frame.locals 0 ≠ some .dead
  stack_decl0 : ∀ cf ∈ s.memory.callStack, ∃ decl0, get? cf.callerBody.localDecls 0 = some decl0
  stack_live0 : ∀ cf ∈ s.memory.callStack, get? cf.frame.locals 0 ≠ some .dead

/-- One `lean-miri` step (`Step.lean:90`) from an `UnwindingStateRel rootBody s m`
state (`topFrame.location = .unwinding span`) across all cases of `s.memory.callStack`
and `cf.returnUnwind`. -/
theorem step_unwinding_state_single_frame
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hunw : UnwindingStateRel rootBody s m)
    (hwf : UnwindChainWf rootBody s m) :
    (s.memory.callStack = [] →
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
        (m, .error (.undefinedBehavior "unwinding past the topmost stack frame"))) ∧
    (∀ cf restStack, s.memory.callStack = cf :: restStack →
      let s₁ : MachineState :=
        { frame := cf.frame
          memory :=
            { s.memory with
              callStack := restStack
              activeCallee := some cf.callerBody
              activeProtectors := restoreCallerProtectors cf } }
      (∀ cleanupBb, cf.returnUnwind = .cleanup cleanupBb →
        ∃ m',
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            (m', .ok true) ∧
          MultiFrameStateRel rootBody
            { s₁ with frame := { cf.frame with blockIdx := cleanupBb, stmtIdx := 0 } }
            m') ∧
      (cf.returnUnwind = .unreachable →
        ∃ m',
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            (m', .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) ∧
      (cf.returnUnwind = .terminate →
        ∃ m',
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            (m', .error (.unsupported "unwindTerminate"))) ∧
      (cf.returnUnwind = .continue_ →
        ∃ m₁,
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            (m₁, .ok true) ∧
          UnwindingStateRel rootBody s₁ m₁ ∧
          UnwindChainWf rootBody s₁ m₁)) := by
  rcases hunw with ⟨m_mir, topFrame₀, span, hback_mir, hm_eq, hstate_mir⟩
  rcases hstate_mir with
    ⟨topFrame₁, hback₁, hcal_root, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have htf_eq0 : topFrame₁ = topFrame₀ := Option.some.inj (hback₁.symm.trans hback_mir)
  subst htf_eq0
  refine ⟨?_, ?_⟩
  · intro hnil
    have hact_body : activeMirBody rootBody s = rootBody := by
      unfold activeMirBody
      rcases hcal_root hnil with hnone | hsome <;> simp [*]
    generalize hmfs : m_mir.stack.frames.toList.reverse = mfs at hlinks
    rw [hnil, hact_body] at hlinks
    cases hlinks with
    | root _ rootMf _ _ _ _ =>
      have hframes_mir : m_mir.stack.frames = #[rootMf] := by
        simpa using array_eq_of_toList_reverse_cons hmfs
      have hback_r : m_mir.stack.frames.back? = some rootMf := by rw [hframes_mir]; rfl
      have h_eq : rootMf = topFrame₁ := Option.some.inj (hback_r.symm.trans hback₁)
      subst h_eq
      have hframes_m : m.stack.frames = #[{ rootMf with location := .unwinding span }] := by
        rw [hm_eq, hframes_mir]; rfl
      have hcurr : m.stack.currentFrame? = some { rootMf with location := .unwinding span } := by
        rw [Miri.Interpreter.Stack.currentFrame?, hframes_m]; rfl
      unfold Miri.Interpreter.Step.step annealStepHooksForState annealStepHooksLM4_1
      rw [hcurr]
      change miriFinishStep
        (Miri.Interpreter.ControlFlow.returnFromCurrentFrame
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts (annealPoppedFrameState s)) () true m) = _
      rw [returnFromCurrentFrame_unwinding_loc_root_ub _ hframes_m rfl]
      rfl
  · intro cf restStack hstack
    dsimp only []
    have hne_cs : s.memory.callStack ≠ [] := by rw [hstack]; exact List.cons_ne_nil _ _
    obtain ⟨decl0, hdecl0⟩ := hwf.cur_decl0 hne_cs
    have hlive0 := hwf.cur_live0 hne_cs
    generalize hmfs : m_mir.stack.frames.toList.reverse = mfs at hlinks
    generalize hprots : s.memory.activeProtectors = prots at hlinks hvalid hcid_act hbt
    generalize hcur : activeMirBody rootBody s = curBody at hlinks
    rw [hstack] at hlinks hbt
    cases hlinks with
    | cons _ _ _ _ curFrameProts callerProts calleeMf callerMf restMfs
        hretCont _ hfr_callee _ hcp _ hlinks_caller =>
      subst hcur
      have harr_mir := array_eq_of_toList_reverse_cons hmfs
      have hback_cal : m_mir.stack.frames.back? = some calleeMf := by rw [harr_mir]; simp
      have hcal_eq : calleeMf = topFrame₁ := Option.some.inj (hback_cal.symm.trans hback₁)
      subst hcal_eq
      let calleeUnw : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { calleeMf with location := .unwinding span }
      have harr_m : m.stack.frames = ⟨(callerMf :: restMfs).reverse ++ [calleeUnw]⟩ := by
        rw [hm_eq, harr_mir]
        apply Array.ext'
        simp [List.reverse_cons, calleeUnw]
      have harr_two_m :
          m.stack.frames = ⟨(restMfs.reverse ++ [callerMf]) ++ [calleeUnw]⟩ := by
        rw [harr_m]
        apply Array.ext'
        simp [List.reverse_cons]
      have hback_m : m.stack.frames.back? = some calleeUnw := by
        rw [harr_m]; simp
      have hcurr_m : m.stack.currentFrame? = some calleeUnw := hback_m
      have hmach_eq : m.machine = m_mir.machine := by rw [hm_eq]
      let poppedFrame := annealPoppedFrameState s
      have hpopped_eq :
          poppedFrame =
            poppedCalleeFrameState s.memory.borrows (curFrameProts ++ callerProts)
              (callerRestoredProtectors [cf]) := by
        dsimp only [poppedFrame, annealPoppedFrameState]
        rw [hstack, hprots]
      let bt' := popFrameBorrowTracker poppedFrame m.machine.borrowTracker
      let m₀ : AnnealStepState :=
        { stack := m.stack, machine := { m.machine with borrowTracker := bt' } }
      have hbt_post :
          BorrowTrackerStackRel s.memory.borrows
            (restoreCallerProtectors cf) restStack bt' := by
        dsimp only [bt', restoreCallerProtectors]
        rw [hmach_eq, hpopped_eq]
        exact hbt.of_popFrame
      have hfr_callee_bt : FrameRel (activeMirBody rootBody s) m₀.machine s.frame calleeMf := by
        simpa [m₀, hmach_eq] using hfr_callee.of_borrowTracker (bt' := bt')
      have hlinks_caller_bt :
          CallerStackLinksRel rootBody m₀.machine cf.callerBody cf.frame restStack callerProts
            (callerMf :: restMfs) := by
        simpa [m₀, hmach_eq] using hlinks_caller.of_borrowTracker (bt' := bt')
      obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hfr_callee_bt.lookup_local hdecl0
      have hmls0_unw : calleeUnw.locals[0]? = some mls0 := hmls0
      have hget0 := frame_getLocal_of_getElem? calleeUnw 0 mls0 hmls0_unw
      have hop0 :
          ∃ op0,
            (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts poppedFrame).returnOperand () m =
              (m, .ok op0) := by
        cases hloc0 with
        | dead _ _ => exact False.elim (hlive0 hslot0)
        | immediate _ imm0 _ _ _ =>
          exact ⟨.immediate imm0,
            annealControlHooks_returnOperand_unwinding_live_back hback_m rfl hget0 hdecl0⟩
        | indirect _ mp0 _ _ _ _ =>
          exact ⟨.indirect mp0,
            annealControlHooks_returnOperand_unwinding_live_back hback_m rfl hget0 hdecl0⟩
      obtain ⟨op0, hop0⟩ := hop0
      have hpop :
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts poppedFrame).popFrame () m =
            ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }, .ok calleeUnw) :=
        annealPopFrameLM4_1_callee_append_singleton harr_two_m
      have hd_callee : MemoryAllocDisjoint calleeMf := by
        apply hdisj.intra_frame calleeMf
        rw [harr_mir]; simp
      have hd_calleeUnw : MemoryAllocDisjoint calleeUnw := hd_callee
      have hdisj_orig :
          MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ := by
        rw [← harr_mir]; exact hdisj
      have hdisj_pop : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ :=
        hdisj_orig.pop_top
      have hva_unw : calleeUnw.vaList = #[] := by
        apply hwf.vaList_empty calleeUnw
        rw [harr_m]; simp
      have hlive_unw : AllSlotsAllocLive m₀.machine.memory calleeUnw.locals.toList :=
        hfr_callee_bt.allSlotsAllocLive
      have hclean :
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
            true calleeUnw { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ } =
          ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
             machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } },
           .ok .normal) := by
        unfold annealControlHooksLM4_1
        dsimp only
        rw [cleanupStackFrame_callee_goto_any_unwinding
          (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
          ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ m₀.machine.memory true calleeUnw
          hretCont hva_unw hlive_unw hd_calleeUnw.slotsAllocDisjoint]
      have hdealloc_eq :
          deallocFrameLocals m₀.machine.memory calleeUnw =
            deallocFrameLocals m₀.machine.memory calleeMf := rfl
      have hstep_eq :
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            miriFinishStep
              (Miri.Interpreter.ControlFlow.returnFromCurrentFrame
                (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
                  (activeMirBody rootBody s).layouts poppedFrame) () true m) := by
        unfold Miri.Interpreter.Step.step annealStepHooksForState annealStepHooksLM4_1
        rw [hcurr_m]
        rfl
      have hfr_caller : FrameRel cf.callerBody m₀.machine cf.frame callerMf := by
        cases hlinks_caller_bt.toForall2 with
        | cons hfr _ => exact hfr
      have hcp_eq : restoreCallerProtectors cf = callerProts := by
        unfold restoreCallerProtectors
        cases hopt : cf.callerProtector <;> (rw [hopt] at hcp; exact hcp)
      have hvalid_post : ActiveProtectorsValid s.memory.borrows (restoreCallerProtectors cf) := by
        rw [hcp_eq]
        apply hvalid.mono_protectors
        intro cid hcid
        exact natListContainsBool_append_right curFrameProts callerProts cid hcid
      have hcid_act_post : ∀ cid ∈ restoreCallerProtectors cf, cid < s.memory.nextProtector := by
        intro cid hcid
        rw [hcp_eq] at hcid
        exact hcid_act cid (List.mem_append_right curFrameProts hcid)
      have hcal_root_post :
          restStack = [] →
            some cf.callerBody = none ∨ some cf.callerBody = some rootBody := by
        intro hnil
        subst hnil
        cases hlinks_caller_bt with
        | root _ _ _ _ _ _ => exact Or.inr rfl
      have htb_post :
          TreeBorrowsRel s.memory.borrows (restoreCallerProtectors cf)
            (basedNormalTree s.memory.borrows (restoreCallerProtectors cf)) :=
        htb.change_protectors _
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cleanupBb hclean_bb
        have hretCont' : calleeUnw.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) (.Cleanup cleanupBb) := by
          dsimp only [calleeUnw]
          rw [hretCont, hclean_bb]
          rfl
        refine ⟨{ stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .mir ⟨cleanupBb, 0⟩ }]⟩⟩
                  machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } },
                ?_, ?_⟩
        · rw [hstep_eq,
            returnFromCurrentFrame_lm4_1_unwinding_loc_cleanup_ok harr_m rfl hretCont' hop0 hpop hclean]
          rfl
        · let callerMf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
            { callerMf with location := .mir ⟨cleanupBb, 0⟩ }
          let callerAf' : StackFrame := { cf.frame with blockIdx := cleanupBb, stmtIdx := 0 }
          have hfr_caller' : FrameRel cf.callerBody m₀.machine callerAf' callerMf' :=
            ⟨hfr_caller.body_eq, rfl, hfr_caller.af_locals_len, hfr_caller.mf_locals_size, hfr_caller.locals_rel⟩
          have hlinks_upd :
              CallerStackLinksRel rootBody m₀.machine cf.callerBody callerAf'
                restStack callerProts (callerMf' :: restMfs) :=
            hlinks_caller_bt.update_top_frame (curAf' := callerAf') rfl rfl rfl hfr_caller'
              (fun mp0 lay0 h0 => ⟨⟨lay0, h0⟩, Or.inl rfl⟩)
          have hlinks_post :
              CallerStackLinksRel rootBody
                { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw }
                cf.callerBody callerAf'
                restStack callerProts (callerMf' :: restMfs) := by
            rw [hdealloc_eq]
            apply hlinks_upd.of_deallocFrameLocals
            intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
            rcases List.mem_cons.mp hmf with rfl | hmem_rest
            · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
            · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest) i j mp₁ mp₂ lay₁ lay₂ hi hj
          have hd_callerMf' : MemoryAllocDisjoint callerMf' :=
            hdisj_pop.intra_frame callerMf (by simp)
          have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
            hdisj_pop.replace_top hd_callerMf' (fun _ _ lay hi => ⟨lay, hi⟩)
          refine .mk callerMf'
            (array_back?_append_singleton restMfs.reverse callerMf')
            hcal_root_post (fun _ => rfl)
            (by
              unfold FrameStackRel annealFrameStackTopDown activeMirBody
              dsimp only [callerAf']
              rw [array_toList_reverse_append_singleton restMfs callerMf']
              exact hlinks_post.toForall2)
            (by
              unfold activeMirBody
              dsimp only [callerAf']
              rw [hcp_eq, array_toList_reverse_append_singleton restMfs callerMf']
              exact hlinks_post)
            hdisj_post htb_post hvalid_post hcid_pos hcid_act_post hcid_bor hbt_post
      · intro hunreach
        have hretCont' : calleeUnw.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) .Unreachable := by
          dsimp only [calleeUnw]; rw [hretCont, hunreach]; rfl
        refine ⟨{ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
                  machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } },
                ?_⟩
        rw [hstep_eq,
          returnFromCurrentFrame_lm4_1_unwinding_loc_unreachable_ub harr_m rfl hretCont' hop0 hpop hclean]
        rfl
      · intro hterm_act
        have hretCont' : calleeUnw.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) (.Terminate .Abi) := by
          dsimp only [calleeUnw]; rw [hretCont, hterm_act]; rfl
        refine ⟨{ stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
                  machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } },
                ?_⟩
        rw [hstep_eq,
          returnFromCurrentFrame_lm4_1_unwinding_loc_terminate_err harr_m rfl hretCont' hop0 hpop hclean]
        rfl
      · intro hcont_act
        have hretCont' : calleeUnw.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) .Continue := by
          dsimp only [calleeUnw]; rw [hretCont, hcont_act]; rfl
        let m₁_mir : AnnealStepState :=
          { stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
            machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } }
        let m₁ : AnnealStepState :=
          { stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
            machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw } }
        refine ⟨m₁, ?_, ?_, ?_⟩
        · rw [hstep_eq,
            returnFromCurrentFrame_lm4_1_unwinding_loc_continue_ok harr_m rfl hretCont' hop0 hpop hclean]
          rfl
        · refine ⟨m₁_mir, callerMf, defaultSpanRef,
            array_back?_append_singleton restMfs.reverse callerMf, ?_, ?_⟩
          · dsimp only [m₁, m₁_mir]
            congr 2
            apply Array.ext'
            simp
          · have hlinks_post :
                CallerStackLinksRel rootBody
                  { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeUnw }
                  cf.callerBody cf.frame restStack callerProts (callerMf :: restMfs) := by
              rw [hdealloc_eq]
              apply hlinks_caller_bt.of_deallocFrameLocals
              intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
              rcases List.mem_cons.mp hmf with rfl | hmem_rest
              · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
              · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest) i j mp₁ mp₂ lay₁ lay₂ hi hj
            refine .mk callerMf
              (array_back?_append_singleton restMfs.reverse callerMf)
              hcal_root_post (fun _ => rfl)
              (by
                unfold FrameStackRel annealFrameStackTopDown activeMirBody
                dsimp only [m₁_mir]
                rw [array_toList_reverse_append_singleton restMfs callerMf]
                exact hlinks_post.toForall2)
              (by
                unfold activeMirBody
                dsimp only [m₁_mir]
                rw [hcp_eq, array_toList_reverse_append_singleton restMfs callerMf]
                exact hlinks_post)
              hdisj_pop htb_post hvalid_post hcid_pos hcid_act_post hcid_bor hbt_post
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro mf hmf
            dsimp only [m₁] at hmf
            rcases List.mem_append.mp hmf with hmem_rest | hsingle
            · apply hwf.vaList_empty mf
              rw [harr_m]
              have hmem_c : mf ∈ (callerMf :: restMfs).reverse := by
                rw [List.reverse_cons]
                exact List.mem_append_left [callerMf] hmem_rest
              exact List.mem_append_left [calleeUnw] hmem_c
            · rcases List.mem_singleton.mp hsingle with rfl
              change callerMf.vaList = #[]
              apply hwf.vaList_empty callerMf
              rw [harr_m]
              exact List.mem_append_left [calleeUnw] (by simp [List.reverse_cons])
          · intro _
            have hmem_cf : cf ∈ s.memory.callStack := by rw [hstack]; exact List.mem_cons_self
            dsimp only [activeMirBody]
            exact hwf.stack_decl0 cf hmem_cf
          · intro _
            have hmem_cf : cf ∈ s.memory.callStack := by rw [hstack]; exact List.mem_cons_self
            exact hwf.stack_live0 cf hmem_cf
          · intro cf' hcf'
            exact hwf.stack_decl0 cf' (by rw [hstack]; exact List.mem_cons_of_mem _ hcf')
          · intro cf' hcf'
            exact hwf.stack_live0 cf' (by rw [hstack]; exact List.mem_cons_of_mem _ hcf')

/-- **Arbitrary-Depth Multi-Frame Unwinding Simulation (`unwindFromCallStack_miri_multiStep_simulation`)**:
From any `UnwindingStateRel rootBody s m` state (`topFrame.location = .unwinding span`)
satisfying `UnwindChainWf rootBody s m`, Stage-1 `unwindFromCallStack s.memory.callStack s.memory`
corresponds across arbitrary `.continue_` call depth to a multi-step
`MiriUnwindSteps rootBody` execution of `Miri.Interpreter.Step.step`:
1. `.running s'`: for some `1 ≤ k ≤ s.memory.callStack.length`,
   `s'.memory.activeProtectors = releaseCallProtectors k s.memory.callStack s.memory.activeProtectors`
   and `lean-miri` steps `k` times (`MiriUnwindSteps rootBody k s m (m', .ok true)`)
   to a state `m'` satisfying `MultiFrameStateRel rootBody s' m'`;
2. `.faulted .ub`: for some `1 ≤ k ≤ s.memory.callStack.length`, `lean-miri` steps
   `k` times to `(m', .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))`;
3. `.halted .panic`: all `s.memory.callStack.length` saved caller frames unwind
   via `.continue_` to the root frame, where step `s.memory.callStack.length + 1`
   faults with `.error (.undefinedBehavior "unwinding past the topmost stack frame")`;
4. `.halted .abort`: for some `1 ≤ k ≤ s.memory.callStack.length`, `lean-miri` steps
   `k` times to `(m', .error (.unsupported "unwindTerminate"))`. -/
theorem unwindFromCallStack_miri_multiStep_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hunw : UnwindingStateRel rootBody s m)
    (hwf : UnwindChainWf rootBody s m) :
    (∀ s', unwindFromCallStack s.memory.callStack s.memory = .running s' →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        s'.memory.activeProtectors =
          releaseCallProtectors k s.memory.callStack s.memory.activeProtectors ∧
        MiriUnwindSteps rootBody k s m (m', .ok true) ∧
        MultiFrameStateRel rootBody s' m') ∧
    (unwindFromCallStack s.memory.callStack s.memory = .faulted .ub →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        MiriUnwindSteps rootBody k s m
          (m', .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) ∧
    (unwindFromCallStack s.memory.callStack s.memory = .halted .panic →
      ∃ m',
        MiriUnwindSteps rootBody (s.memory.callStack.length + 1) s m
          (m', .error (.undefinedBehavior "unwinding past the topmost stack frame"))) ∧
    (unwindFromCallStack s.memory.callStack s.memory = .halted .abort →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        MiriUnwindSteps rootBody k s m (m', .error (.unsupported "unwindTerminate"))) := by
  generalize hcs : s.memory.callStack = cs
  induction cs generalizing s m with
  | nil =>
    have hstep := (step_unwinding_state_single_frame hunw hwf).1 hcs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _ h; simp [unwindFromCallStack] at h
    · intro h; simp [unwindFromCallStack] at h
    · intro _; exact ⟨m, .single s m m _ hstep⟩
    · intro h; simp [unwindFromCallStack] at h
  | cons cf restStack ih =>
    have hne : s.memory.callStack ≠ [] := by rw [hcs]; exact List.cons_ne_nil _ _
    have hframe_step := (step_unwinding_state_single_frame hunw hwf).2 cf restStack hcs
    cases hru : cf.returnUnwind with
    | cleanup cleanupBb =>
      obtain ⟨m', hm_step, hrel'⟩ := hframe_step.1 cleanupBb hru
      simp only [unwindFromCallStack, hru]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s' hs'
        injection hs' with hs_eq
        subst hs_eq
        exact ⟨1, m', Nat.le_refl 1, by simp only [List.length_cons]; omega, rfl,
          .single s m m' _ hm_step, hrel'⟩
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
    | unreachable =>
      obtain ⟨m', hm_step⟩ := hframe_step.2.1 hru
      simp only [unwindFromCallStack, hru]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro _
        exact ⟨1, m', Nat.le_refl 1, by simp only [List.length_cons]; omega,
          .single s m m' _ hm_step⟩
      · intro h; cases h
      · intro h; cases h
    | terminate =>
      obtain ⟨m', hm_step⟩ := hframe_step.2.2.1 hru
      simp only [unwindFromCallStack, hru]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro h; cases h
      · intro h; cases h
      · intro _
        exact ⟨1, m', Nat.le_refl 1, by simp only [List.length_cons]; omega,
          .single s m m' _ hm_step⟩
    | continue_ =>
      obtain ⟨m₁, hm_step, hunw₁, hwf₁⟩ := hframe_step.2.2.2 hru
      let s₁ : MachineState :=
        { frame := cf.frame
          memory :=
            { s.memory with
              callStack := restStack
              activeCallee := some cf.callerBody
              activeProtectors := restoreCallerProtectors cf } }
      have hih := ih hunw₁ hwf₁ (s := s₁) rfl
      simp only [unwindFromCallStack, hru]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s' hs'
        obtain ⟨k, m', hk1, hk2, hprot, hsteps, hrel'⟩ := hih.1 s' hs'
        refine ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega, ?_,
          .cons s s₁ m m₁ _ hne hm_step hunw₁ hsteps, hrel'⟩
        simpa [s₁, releaseCallProtectors] using hprot
      · intro hub
        obtain ⟨k, m', hk1, hk2, hsteps⟩ := hih.2.1 hub
        exact ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega,
          .cons s s₁ m m₁ _ hne hm_step hunw₁ hsteps⟩
      · intro hpan
        obtain ⟨m', hsteps⟩ := hih.2.2.1 hpan
        exact ⟨m', .cons s s₁ m m₁ _ hne hm_step hunw₁ hsteps⟩
      · intro habort
        obtain ⟨k, m', hk1, hk2, hsteps⟩ := hih.2.2.2 habort
        exact ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega,
          .cons s s₁ m m₁ _ hne hm_step hunw₁ hsteps⟩

/-- **Theorem 6 (`step_terminator_unwindResume_multiFrame_simulation`)**:
Full arbitrary-depth `TerminatorKind.unwindResume` simulation from any cleanup
basic block (`bb.isCleanup = true`) under `MultiFrameStateRel rootBody s m` and
`UnwindChainWf rootBody s m`, covering `UnwindAction.continue_` chains of
arbitrary length `k ≥ 1` as well as `.cleanup`, `.unreachable`, `.terminate`,
and root unwinding:
* When `stepMirFn rootBody s = .step s'`, there exist `1 ≤ k ≤ s.memory.callStack.length`
  and `m'` such that `s'.memory.activeProtectors = releaseCallProtectors k s.memory.callStack s.memory.activeProtectors`,
  `MiriUnwindSteps rootBody k s m (m', .ok true)` holds (`k` Miri steps), and
  `MultiFrameStateRel rootBody s' m'` holds;
* When `stepMirFn rootBody s = .fail .ub`, `lean-miri` faults with
  `.undefinedBehavior "unwinding past a frame that does not allow unwinding"` in
  `1 ≤ k ≤ s.memory.callStack.length` steps;
* When `stepMirFn rootBody s = .retOutcome .panic`, `lean-miri` unwinds all
  `s.memory.callStack.length` callee frames and faults on step
  `s.memory.callStack.length + 1` with `.undefinedBehavior "unwinding past the topmost stack frame"`;
* When `stepMirFn rootBody s = .retOutcome .abort`, `lean-miri` reaches
  `.error (.unsupported "unwindTerminate")` in `1 ≤ k ≤ s.memory.callStack.length` steps. -/
theorem step_terminator_unwindResume_multiFrame_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hwf : UnwindChainWf rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = true)
    (hterm : bb.terminator.kind = .unwindResume) :
    (∀ s', stepMirFn rootBody s = .step s' →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        s'.memory.activeProtectors =
          releaseCallProtectors k s.memory.callStack s.memory.activeProtectors ∧
        MiriUnwindSteps rootBody k s m (m', .ok true) ∧
        MultiFrameStateRel rootBody s' m') ∧
    (stepMirFn rootBody s = .fail .ub →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        MiriUnwindSteps rootBody k s m
          (m', .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) ∧
    (stepMirFn rootBody s = .retOutcome .panic →
      ∃ m',
        MiriUnwindSteps rootBody (s.memory.callStack.length + 1) s m
          (m', .error (.undefinedBehavior "unwinding past the topmost stack frame"))) ∧
    (stepMirFn rootBody s = .retOutcome .abort →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧
        MiriUnwindSteps rootBody k s m (m', .error (.unsupported "unwindTerminate"))) := by
  have hstate_copy := hstate
  rcases hstate with
    ⟨topFrame, hback, hcal_root, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  cases hstack : s.memory.callStack with
  | nil =>
    have hact_body : activeMirBody rootBody s = rootBody := by
      unfold activeMirBody
      rcases hcal_root hstack with hnone | hsome <;> simp [*]
    have hphase_r : ∀ p, rootBody.phase ≠ .other p := by rw [← hact_body]; exact hphase
    have hbb_r : get? rootBody.basicBlocks s.frame.blockIdx = some bb := by
      rw [← hact_body]; exact hbb
    generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
    rw [hstack, hact_body] at hlinks
    cases hlinks with
    | root _ rootMf _ _ _ hframe =>
      have hframes : m.stack.frames = #[rootMf] := by
        simpa using array_eq_of_toList_reverse_cons hmfs
      have hback_r : m.stack.frames.back? = some rootMf := by rw [hframes]; rfl
      have h_eq : rootMf = topFrame := Option.some.inj (hback_r.symm.trans hback)
      subst h_eq
      have ha_step : stepMirFn rootBody s = .retOutcome .panic := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm, hstack]
        rfl
      have hm_step :
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            (m, .error (.undefinedBehavior "unwinding past the topmost stack frame")) := by
        unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback
          (by rw [hact_body]; exact hframe.body_eq) hframe.location_eq hbb hstmt_none]
        unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
        rw [hterm]
        dsimp only [translateTerminatorKind, Id.run, Pure.pure]
        rw [returnFromCurrentFrame_unwind_root_ub _ hframes hframe.body_eq hframe.location_eq
          hbb_r hcleanup]
        rfl
      rw [ha_step]
      refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), ?_, (fun h => nomatch h)⟩
      intro _
      exact ⟨m, .single s m m _ hm_step⟩
  | cons cf restStack =>
    have hne : s.memory.callStack ≠ [] := by rw [hstack]; exact List.cons_ne_nil _ _
    obtain ⟨decl0, hdecl0⟩ := hwf.cur_decl0 hne
    have hlive0 := hwf.cur_live0 hne
    generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
    generalize hprots : s.memory.activeProtectors = prots at hlinks hvalid hcid_act hbt
    generalize hcur : activeMirBody rootBody s = curBody at hlinks
    rw [hstack] at hlinks hbt
    cases hlinks with
    | cons _ _ _ _ curFrameProts callerProts calleeMf callerMf restMfs
        hretCont _ hfr_callee _ hcp _ hlinks_caller =>
      subst hcur
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_c : m.stack.frames.back? = some calleeMf := by rw [harr]; simp
      have h_eq : calleeMf = topFrame := Option.some.inj (hback_c.symm.trans hback)
      subst h_eq
      have harr_two :
          m.stack.frames = ⟨(restMfs.reverse ++ [callerMf]) ++ [calleeMf]⟩ := by
        rw [harr]; apply Array.ext'; simp [List.reverse_cons]
      let poppedFrame := annealPoppedFrameState s
      have hpopped_eq :
          poppedFrame =
            poppedCalleeFrameState s.memory.borrows (curFrameProts ++ callerProts)
              (callerRestoredProtectors [cf]) := by
        dsimp only [poppedFrame, annealPoppedFrameState]; rw [hstack, hprots]
      let bt' := popFrameBorrowTracker poppedFrame m.machine.borrowTracker
      let m₀ : AnnealStepState :=
        { stack := m.stack, machine := { m.machine with borrowTracker := bt' } }
      have hbt_post :
          BorrowTrackerStackRel s.memory.borrows (restoreCallerProtectors cf) restStack bt' := by
        unfold restoreCallerProtectors; dsimp only [bt']; rw [hpopped_eq]; exact hbt.of_popFrame
      have hfr_callee_bt := hfr_callee.of_borrowTracker (bt' := bt')
      have hlinks_caller_bt := hlinks_caller.of_borrowTracker (bt' := bt')
      obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hfr_callee_bt.lookup_local hdecl0
      have hget0 := frame_getLocal_of_getElem? calleeMf 0 mls0 hmls0
      have hop0 :
          ∃ op0,
            (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts poppedFrame).returnOperand () m =
              (m, .ok op0) := by
        cases hloc0 with
        | dead _ _ => exact False.elim (hlive0 hslot0)
        | immediate _ imm0 _ _ _ =>
          exact ⟨.immediate imm0,
            annealControlHooks_returnOperand_cleanup_live_back hback hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hget0 hdecl0⟩
        | indirect _ mp0 _ _ _ _ =>
          exact ⟨.indirect mp0,
            annealControlHooks_returnOperand_cleanup_live_back hback hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hget0 hdecl0⟩
      obtain ⟨op0, hop0⟩ := hop0
      have hpop :
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts poppedFrame).popFrame () m =
            ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }, .ok calleeMf) :=
        annealPopFrameLM4_1_callee_append_singleton harr_two
      have hd_callee : MemoryAllocDisjoint calleeMf := by
        apply hdisj.intra_frame calleeMf; rw [harr]; simp
      have hdisj_orig :
          MultiFrameAllocDisjoint ⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ := by
        rw [← harr]; exact hdisj
      have hdisj_pop : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ :=
        hdisj_orig.pop_top
      have hva_c : calleeMf.vaList = #[] := by
        apply hwf.vaList_empty calleeMf; rw [harr]; simp
      have hclean :
          (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts poppedFrame).cleanupFrame ()
            true calleeMf { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ } =
          ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
             machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
           .ok .normal) := by
        unfold annealControlHooksLM4_1; dsimp only
        rw [cleanupStackFrame_callee_goto_any_unwinding
          (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
          ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ m₀.machine.memory true calleeMf
          hretCont hva_c hfr_callee_bt.allSlotsAllocLive hd_callee.slotsAllocDisjoint]
      have hm_term_eq :
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            miriFinishStep
              (Miri.Interpreter.ControlFlow.returnFromCurrentFrame
                (annealControlHooksLM4_1 (activeMirBody rootBody s).localDecls
                  (activeMirBody rootBody s).layouts poppedFrame) () true m) := by
        unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback hfr_callee_bt.body_eq
          hfr_callee_bt.location_eq hbb hstmt_none]
        unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm]
        rfl
      have ha_term_eq :
          stepMirFn rootBody s =
            match unwindFromCallStack (cf :: restStack) s.memory with
            | .running nextState => .step nextState
            | .halted out => .retOutcome out
            | .faulted fk => .fail fk := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm, hstack]
        rfl
      cases hru : cf.returnUnwind with
      | cleanup cleanupBb =>
        have hsim_one :=
          step_terminator_unwindResume_callee_simulation hstate_copy hstack
            (fun tf htf => hwf.vaList_empty tf (by
              have htf_eq : tf = calleeMf := Option.some.inj (htf.symm.trans hback)
              subst htf_eq; rw [harr]; simp))
            hphase hbb hstmt_none hstmt_len hcleanup hterm hdecl0 hlive0
            (Or.inr ⟨cleanupBb, hru⟩)
        have hretCont' : calleeMf.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) (.Cleanup cleanupBb) := by
          rw [hretCont, hru]; rfl
        let m' : AnnealStepState :=
          { stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .mir ⟨cleanupBb, 0⟩ }]⟩⟩
            machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } }
        have hm_ok : Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m', .ok true) := by
          rw [hm_term_eq,
            returnFromCurrentFrame_lm4_1_unwind_cleanup_ok harr hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hretCont' hop0 hpop hclean]
          rfl
        have hm_ok3 :
            Miri.Interpreter.Step.step
              (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)) () m =
              (m', .ok true) := by
          have : Miri.Interpreter.Step.step
              (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s)) () m =
            Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m := by
            unfold annealStepHooksForState
            rw [miri_step_at_terminator_multiFrame hback hfr_callee_bt.body_eq hfr_callee_bt.location_eq hbb hstmt_none,
                miri_step_at_terminator_multiFrame hback hfr_callee_bt.body_eq hfr_callee_bt.location_eq hbb hstmt_none]
            unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksLM4_1
            rw [hterm]; rfl
          rw [this, hm_ok]
        rw [ha_term_eq, hm_ok3] at hsim_one
        rw [ha_term_eq]
        simp only [unwindFromCallStack, hru] at hsim_one ⊢
        cases hsim_one with
        | step _ _ hrel' =>
          refine ⟨?_, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
          intro s' hs'
          cases hs'
          exact ⟨1, m', Nat.le_refl 1, by simp only [List.length_cons]; omega, rfl,
            .single s m m' _ hm_ok, hrel'⟩
      | unreachable =>
        have hretCont' : calleeMf.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) .Unreachable := by
          rw [hretCont, hru]; rfl
        have hm_ub :
            Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
              ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
                 machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
               .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) := by
          rw [hm_term_eq,
            returnFromCurrentFrame_lm4_1_unwind_unreachable_ub harr hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hretCont' hop0 hpop hclean]
          rfl
        rw [ha_term_eq]
        simp only [unwindFromCallStack, hru]
        refine ⟨(fun _ h => nomatch h), ?_, (fun h => nomatch h), (fun h => nomatch h)⟩
        intro _
        exact ⟨1, _, Nat.le_refl 1, by simp only [List.length_cons]; omega,
          .single s m _ _ hm_ub⟩
      | terminate =>
        have hretCont' : calleeMf.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) (.Terminate .Abi) := by
          rw [hretCont, hru]; rfl
        have hm_term :
            Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
              ({ stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
                 machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } },
               .error (.unsupported "unwindTerminate")) := by
          rw [hm_term_eq,
            returnFromCurrentFrame_lm4_1_unwind_terminate_err harr hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hretCont' hop0 hpop hclean]
          rfl
        rw [ha_term_eq]
        simp only [unwindFromCallStack, hru]
        refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), ?_⟩
        intro _
        exact ⟨1, _, Nat.le_refl 1, by simp only [List.length_cons]; omega,
          .single s m _ _ hm_term⟩
      | continue_ =>
        have hretCont' : calleeMf.returnContinuation =
            .goto (if cf.isDiverging then none else some cf.returnTarget) .Continue := by
          rw [hretCont, hru]; rfl
        let s₁ : MachineState :=
          { frame := cf.frame
            memory :=
              { s.memory with
                callStack := restStack
                activeCallee := some cf.callerBody
                activeProtectors := restoreCallerProtectors cf } }
        let m₁_mir : AnnealStepState :=
          { stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩
            machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } }
        let m₁ : AnnealStepState :=
          { stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩
            machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } }
        have hm_cont :
            Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m₁, .ok true) := by
          rw [hm_term_eq,
            returnFromCurrentFrame_lm4_1_unwind_continue_ok harr hfr_callee_bt.body_eq
              hfr_callee_bt.location_eq hbb hcleanup hretCont' hop0 hpop hclean]
          rfl
        have hunw₁ : UnwindingStateRel rootBody s₁ m₁ := by
          refine ⟨m₁_mir, callerMf, defaultSpanRef,
            array_back?_append_singleton restMfs.reverse callerMf, ?_, ?_⟩
          · dsimp only [m₁, m₁_mir]; congr 2; apply Array.ext'; simp
          · have hlinks_post :
                CallerStackLinksRel rootBody
                  { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf }
                  cf.callerBody cf.frame restStack callerProts (callerMf :: restMfs) := by
              apply hlinks_caller_bt.of_deallocFrameLocals
              intro mf hmf i j mp₁ mp₂ lay₁ lay₂ hi hj
              rcases List.mem_cons.mp hmf with rfl | hmem_rest
              · exact hdisj_orig.disjoint_with_popped_top List.mem_cons_self i j mp₁ mp₂ lay₁ lay₂ hi hj
              · exact hdisj_orig.disjoint_with_popped_top (List.mem_cons_of_mem _ hmem_rest) i j mp₁ mp₂ lay₁ lay₂ hi hj
            have hcp_eq : restoreCallerProtectors cf = callerProts := by
              unfold restoreCallerProtectors
              cases hopt : cf.callerProtector <;> (rw [hopt] at hcp; exact hcp)
            have hvalid_post : ActiveProtectorsValid s.memory.borrows (restoreCallerProtectors cf) := by
              rw [hcp_eq]
              exact hvalid.mono_protectors fun cid hcid =>
                natListContainsBool_append_right curFrameProts callerProts cid hcid
            have hcid_act_post : ∀ cid ∈ restoreCallerProtectors cf, cid < s.memory.nextProtector := by
              intro cid hcid; rw [hcp_eq] at hcid
              exact hcid_act cid (List.mem_append_right curFrameProts hcid)
            have hcal_root_post :
                restStack = [] →
                  some cf.callerBody = none ∨ some cf.callerBody = some rootBody := by
              intro hnil; subst hnil
              cases hlinks_caller_bt with | root _ _ _ _ _ _ => exact Or.inr rfl
            refine .mk callerMf
              (array_back?_append_singleton restMfs.reverse callerMf)
              hcal_root_post (fun _ => rfl)
              (by
                unfold FrameStackRel annealFrameStackTopDown activeMirBody
                dsimp only [m₁_mir, s₁, Option.getD]
                rw [array_toList_reverse_append_singleton restMfs callerMf]
                exact hlinks_post.toForall2)
              (by
                unfold activeMirBody
                dsimp only [m₁_mir, s₁, Option.getD]
                rw [hcp_eq, array_toList_reverse_append_singleton restMfs callerMf]
                exact hlinks_post)
              hdisj_pop (htb.change_protectors _) hvalid_post hcid_pos hcid_act_post hcid_bor hbt_post
        have hwf₁ : UnwindChainWf rootBody s₁ m₁ := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro mf hmf
            dsimp only [m₁] at hmf
            rcases List.mem_append.mp hmf with hmem_rest | hsingle
            · apply hwf.vaList_empty mf; rw [harr]
              exact List.mem_append_left [calleeMf] (by
                rw [List.reverse_cons]
                exact List.mem_append_left [callerMf] hmem_rest)
            · rcases List.mem_singleton.mp hsingle with rfl
              change callerMf.vaList = #[]
              apply hwf.vaList_empty callerMf; rw [harr]
              exact List.mem_append_left [calleeMf] (by simp [List.reverse_cons])
          · intro _
            unfold activeMirBody
            dsimp only [s₁, Option.getD]
            exact hwf.stack_decl0 cf (by rw [hstack]; exact List.mem_cons_self)
          · intro _
            exact hwf.stack_live0 cf (by rw [hstack]; exact List.mem_cons_self)
          · intro cf' hcf'
            exact hwf.stack_decl0 cf' (by rw [hstack]; exact List.mem_cons_of_mem _ hcf')
          · intro cf' hcf'
            exact hwf.stack_live0 cf' (by rw [hstack]; exact List.mem_cons_of_mem _ hcf')
        have htail := unwindFromCallStack_miri_multiStep_simulation hunw₁ hwf₁
        rw [ha_term_eq]
        simp only [unwindFromCallStack, hru]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro s' hs'
          cases huw : unwindFromCallStack restStack s₁.memory with
          | running nextSt =>
            rw [huw] at hs'
            cases hs'
            obtain ⟨k, m', hk1, hk2, hprot, hsteps, hrel'⟩ := htail.1 _ huw
            dsimp only [s₁] at hk2
            refine ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega, ?_,
              .cons s s₁ m m₁ _ hne hm_cont hunw₁ hsteps, hrel'⟩
            simpa [s₁, releaseCallProtectors] using hprot
          | halted _ => rw [huw] at hs'; cases hs'
          | faulted _ => rw [huw] at hs'; cases hs'
        · intro hub
          cases huw : unwindFromCallStack restStack s₁.memory with
          | running _ => rw [huw] at hub; cases hub
          | halted _ => rw [huw] at hub; cases hub
          | faulted fk =>
            rw [huw] at hub
            cases fk with
            | ub =>
              obtain ⟨k, m', hk1, hk2, hsteps⟩ := htail.2.1 huw
              dsimp only [s₁] at hk2
              exact ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega,
                .cons s s₁ m m₁ _ hne hm_cont hunw₁ hsteps⟩
            | unsupported => cases hub
            | outOfFuel => cases hub
        · intro hpan
          cases huw : unwindFromCallStack restStack s₁.memory with
          | running _ => rw [huw] at hpan; cases hpan
          | faulted _ => rw [huw] at hpan; cases hpan
          | halted out =>
            rw [huw] at hpan
            cases out with
            | panic =>
              obtain ⟨m', hsteps⟩ := htail.2.2.1 huw
              exact ⟨m', .cons s s₁ m m₁ _ hne hm_cont hunw₁ hsteps⟩
            | abort => cases hpan
            | normal _ => cases hpan
        · intro habort
          cases huw : unwindFromCallStack restStack s₁.memory with
          | running _ => rw [huw] at habort; cases habort
          | faulted _ => rw [huw] at habort; cases habort
          | halted out =>
            rw [huw] at habort
            cases out with
            | abort =>
              obtain ⟨k, m', hk1, hk2, hsteps⟩ := htail.2.2.2 huw
              dsimp only [s₁] at hk2
              exact ⟨k + 1, m', by omega, by simp only [List.length_cons]; omega,
                .cons s s₁ m m₁ _ hne hm_cont hunw₁ hsteps⟩
            | panic => cases habort
            | normal _ => cases habort

/-- **Correspondence (`step_terminator_unwindTerminate_abort_vs_unsupported`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.unwindTerminate`:
1. Stage-1 `Trusted` (`Terminators.lean:3004`) halts immediately with
   `MirStepNode.retOutcome .abort`;
2. `lean-miri` (`annealControlHooksLM4_1.unwindTerminate` at `CallLM4_1.lean:2301`)
   returns `.error (.unsupported "unwindTerminate")` (canonical `ExecutionControl.hooks.unwindTerminate`
   at `ExecutionControl.lean:28-30` resolves and calls the `panic_cannot_unwind` /
   `panic_in_cleanup` lang item, which is unlinked here). -/
theorem step_terminator_unwindTerminate_abort_vs_unsupported
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .unwindTerminate) :
    stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧
    Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
      (m, .error (.unsupported "unwindTerminate")) := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, _⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      refine ⟨?_, ?_⟩
      · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm]
      · unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
        unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1 annealControlHooksLM4_1
        rw [hterm]
        rfl

/-! ## 7. Multi-Frame `TerminatorKind.assert` & Diverging Panic Call Correspondence -/

/-- **Theorem 7 (`step_terminator_assert_local_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.assert (.copy ⟨condIdx, .nil⟩) expected target unwind` on an
immediate `bool` local `condIdx`:
1. When `condIdx` is `.dead` or `.uninit`, both Stage-1 `stepMirFn` and
   `lean-miri` (`annealStepHooksForState rootBody s`) fault with undefined
   behavior (`StepRelMultiFrame.ub`);
2. When `condIdx` holds `.init (.scalar sc)` matching `expected` (`decide (sc.bits ≠ 0) = expected`),
   both machines advance `(blockIdx, stmtIdx)` to `(target, 0)` in lockstep,
   preserving `MultiFrameStateRel` (`StepRelMultiFrame.step`);
3. When `condIdx` holds `.init (.scalar sc)` failing `expected` (`decide (sc.bits ≠ 0) ≠ expected`),
   Stage-1 dispatches `applyUnwindAction s s.frame.locals s.memory unwind`
   (`Terminators.lean:3272`), whereas `lean-miri` (`annealTerminatorHooksLM4_1.assertPanic`,
   without linked `core::panicking` lang items) returns
   `.error (.unsupported "assert panic without linked panic lang item")` (never
   fabricating `.undefinedBehavior`, matching `Panic.lean:6-7`). -/
theorem step_terminator_assert_local_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {condIdx : Local} {condDecl : LocalDecl}
    {expected : Bool} {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .assert (.copy ⟨condIdx, .nil⟩) expected target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls condIdx = some condDecl)
    (hbool_ty : condDecl.ty.kind = .bool)
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf condIdx) :
    ((get? s.frame.locals condIdx = some .dead ∨ get? s.frame.locals condIdx = some .uninit) →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) ∧
    (∀ sc, get? s.frame.locals condIdx = some (.init (.scalar sc)) →
      decide (sc.bits ≠ 0) = expected →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) ∧
    (∀ sc, get? s.frame.locals condIdx = some (.init (.scalar sc)) →
      decide (sc.bits ≠ 0) ≠ expected →
      stepMirFn rootBody s =
        (match applyUnwindAction s s.frame.locals s.memory unwind with
         | .running nextState => .step nextState
         | .halted out => .retOutcome out
         | .faulted fk => .fail fk) ∧
      (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m).2 =
        .error (.unsupported "assert panic without linked panic lang item")) := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hcache := hloc.layout_eq
      have himm' := himm topFrame hback mls hmls
      let hooks := annealTerminatorHooksLM4_1 (activeMirBody rootBody s) s.memory.callees
        (annealPoppedFrameState s) s.memory.fnPtrs
      have hm_step_eq :
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
            miriFinishStep
              (Miri.Interpreter.ControlFlow.evalTerminator hooks
                () (translateTerminator bb.terminator) m) := by
        unfold annealStepHooksForState
        exact miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none
      have ha_step_eq :
          stepMirFn rootBody s = evalTerminator s bb.terminator (some (activeMirBody rootBody s)) := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      have htk_assert :
          (translateTerminator bb.terminator).kind =
            .Assert (.Copy ⟨condIdx, #[]⟩) expected
              (.BoundsCheck (.Copy ⟨condIdx, #[]⟩) (.Copy ⟨condIdx, #[]⟩))
              target (translateUnwindAction unwind) := by
        unfold translateTerminator; rw [hterm]; rfl
      have hign :
          (hooks.ignoreOptionalOverflowChecks m &&
           Miri.Interpreter.ControlFlow.isOptionalOverflowCheck
            (.BoundsCheck (.Copy ⟨condIdx, #[]⟩) (.Copy ⟨condIdx, #[]⟩))) = false := rfl
      refine ⟨?_, ?_, ?_⟩
      · intro hdu
        cases hloc with
        | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
        | dead _ _ =>
          have heval_a :
              evalOperand s.frame.locals (.copy ⟨condIdx, .nil⟩) s.memory.borrows s.memory.globals
                (activeMirBody rootBody s).layouts s.memory.callerLocals = .ub := by
            unfold evalOperand; dsimp only []; rw [hslot]
          have hread_err :
              hooks.readAssertCondition () (.Copy ⟨condIdx, #[]⟩) m =
              ({ m with stack := ⟨⟨restMfs.reverse ++
                  [cacheFrameLocalLayout topFrame condIdx hlt_mf
                    (translateTy condDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
               .error (.undefinedBehavior "read of dead local")) := by
            dsimp only [hooks]
            unfold annealTerminatorHooksLM4_1 annealTerminatorHooks Miri.Interpreter.runRvalue
            dsimp only []
            rw [EStateM.bind_eq_error
              (annealEvalOperand_copy_dead_multiFrame harr hlt_mf hdecl hmls_eq hcache)]
          rw [ha_step_eq, hm_step_eq]
          unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
          rw [hterm, htk_assert]
          dsimp only [Id.run]
          rw [heval_a]
          simp only [hread_err, miriFinishStep, Except.map]
          exact StepRelMultiFrame.ub _ _
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨rfl, rfl⟩ | ⟨v, hv, _⟩
          · have heval_a :
                evalOperand s.frame.locals (.copy ⟨condIdx, .nil⟩) s.memory.borrows s.memory.globals
                  (activeMirBody rootBody s).layouts s.memory.callerLocals = .ub := by
              unfold evalOperand; dsimp only []; rw [hslot]
            have hread_err :
                hooks.readAssertCondition () (.Copy ⟨condIdx, #[]⟩) m =
                ({ m with stack := ⟨⟨restMfs.reverse ++
                    [cacheFrameLocalLayout topFrame condIdx hlt_mf
                      (translateTy condDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
                 .error (.undefinedBehavior "read of uninitialized local")) := by
              dsimp only [hooks]
              unfold annealTerminatorHooksLM4_1 annealTerminatorHooks Miri.Interpreter.runRvalue
              dsimp only []
              rw [EStateM.bind_eq_ok
                (annealEvalOperand_copy_live_multiFrame harr hlt_mf hdecl hmls_eq hcache)]
              rfl
            rw [ha_step_eq, hm_step_eq]
            unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
            rw [hterm, htk_assert]
            dsimp only [Id.run]
            rw [heval_a]
            simp only [hread_err, miriFinishStep, Except.map]
            exact StepRelMultiFrame.ub _ _
          · subst hv
            rcases hdu with hdead | huninit <;> (rw [hslot] at *; cases ‹_›)
      · intro sc hsc hexp
        have hslot_eq : slot = .init (.scalar sc) := Option.some.inj (hslot.symm.trans hsc)
        subst hslot_eq
        cases hloc with
        | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
          · cases h
          · injection hv with hv'; subst hv'
            obtain ⟨b, msc, hv_b, rfl, _, htoBool⟩ := bool_of_immediateRel hbool_ty himmRel
            have hsc_b : sc = boolToScalar b := by injection hv_b
            subst hsc_b
            have hdec_b : decide ((boolToScalar b).bits ≠ 0) = b := by cases b <;> rfl
            rw [hdec_b] at hexp
            subst hexp
            let tfCached := cacheFrameLocalLayout topFrame condIdx hlt_mf
              (translateTy condDecl.ty (activeMirBody rootBody s).layouts)
            have hread_ok :
                hooks.readAssertCondition () (.Copy ⟨condIdx, #[]⟩) m =
                ({ m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ }, .ok b) := by
              dsimp only [hooks]
              unfold annealTerminatorHooksLM4_1 annealTerminatorHooks Miri.Interpreter.runRvalue
              dsimp only []
              rw [EStateM.bind_eq_ok
                (annealEvalOperand_copy_live_multiFrame harr hlt_mf hdecl hmls_eq hcache)]
              dsimp only [annealReadImmediate, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
                Miri.Interpreter.Immediate.toScalar]
              rw [htoBool]
              rfl
            let tfTarget := { tfCached with location := .mir ⟨target, 0⟩ }
            have hgo :
                Miri.Interpreter.ControlFlow.goToBlock target
                  { m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ } =
                ({ m with stack := ⟨⟨restMfs.reverse ++ [tfTarget]⟩⟩ }, .ok ()) := by
              unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
                Miri.Interpreter.Stack.currentFrame?
              rw [array_back?_append_singleton restMfs.reverse tfCached]
              dsimp only []
              congr 3
              apply Array.ext'
              simp [tfTarget]
            have heval_a :
                evalOperand s.frame.locals (.copy ⟨condIdx, .nil⟩) s.memory.borrows s.memory.globals
                  (activeMirBody rootBody s).layouts s.memory.callerLocals =
                .ok (.scalar (boolToScalar b)) s.frame.locals := by
              unfold evalOperand; dsimp only []; rw [hsc]; rfl
            have ha_ok :
                evalTerminator s bb.terminator (some (activeMirBody rootBody s)) =
                  .step { frame := { s.frame with blockIdx := target, stmtIdx := 0 }
                          memory := s.memory } := by
              unfold evalTerminator
              rw [hterm]
              dsimp only []
              rw [heval_a]
              cases b <;> rfl
            rw [ha_step_eq, ha_ok, hm_step_eq]
            unfold Miri.Interpreter.ControlFlow.evalTerminator
            rw [htk_assert]
            dsimp only [Id.run]
            simp only [hign, hread_ok, Bool.false_or, beq_self_eq_true, ↓reduceIte, hgo,
              pure, Pure.pure, miriFinishStep, Except.map]
            apply StepRelMultiFrame.step
            have hfr_cached := hframe.cache_local_layout hdecl hlt_mf
            have hfr_target :
                FrameRel (activeMirBody rootBody s) m.machine
                  { s.frame with blockIdx := target, stmtIdx := 0 } tfTarget :=
              ⟨hfr_cached.body_eq, rfl, hfr_cached.af_locals_len,
               hfr_cached.mf_locals_size, hfr_cached.locals_rel⟩
            have hlinks_post :
                CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s)
                  { s.frame with blockIdx := target, stmtIdx := 0 }
                  s.memory.callStack s.memory.activeProtectors (tfTarget :: restMfs) := by
              refine hlinks.update_top_frame rfl rfl rfl hfr_target ?_
              intro mp0 lay0 h0
              dsimp only [tfTarget, tfCached, cacheFrameLocalLayout] at h0
              by_cases hc0 : condIdx = 0
              · subst hc0
                rw [Array.getElem?_set_self] at h0
                injection h0 with h_eq
                have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                rw [hmls_eq] at hv_eq; cases hv_eq
              · rw [Array.getElem?_set_ne _ hc0] at h0
                exact ⟨⟨lay0, h0⟩, Or.inl rfl⟩
            have hdisj_orig : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [topFrame]⟩ := by
              rw [← harr]; exact hdisj
            have hd_top : MemoryAllocDisjoint topFrame :=
              hdisj_orig.intra_frame topFrame (by simp)
            have hd_tfTarget : MemoryAllocDisjoint tfTarget := by
              apply MemoryAllocDisjoint.mono_layout hd_top
              intro k
              by_cases hk : k = condIdx
              · subst hk
                exists (translateTy condDecl.ty (activeMirBody rootBody s).layouts)
                dsimp only [tfTarget, tfCached, cacheFrameLocalLayout]
                rw [Array.getElem?_set_self, hmls]
                simp [hmls_eq]
              · exists (topFrame.locals[k]?).bind (·.layout)
                dsimp only [tfTarget, tfCached, cacheFrameLocalLayout]
                rw [Array.getElem?_set_ne _ (Ne.symm hk)]
                cases topFrame.locals[k]? <;> rfl
            have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [tfTarget]⟩ := by
              apply hdisj_orig.replace_top hd_tfTarget
              intro i mp lay hi
              dsimp only [tfTarget, tfCached, cacheFrameLocalLayout] at hi
              by_cases hi_c : condIdx = i
              · subst hi_c
                rw [Array.getElem?_set_self] at hi
                injection hi with h_eq
                have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                rw [hmls_eq] at hv_eq; cases hv_eq
              · rw [Array.getElem?_set_ne _ hi_c] at hi
                exact ⟨lay, hi⟩
            refine .mk tfTarget
              (array_back?_append_singleton restMfs.reverse tfTarget)
              hcal_root hcal_nonroot
              (by
                unfold FrameStackRel annealFrameStackTopDown activeMirBody
                rw [array_toList_reverse_append_singleton restMfs tfTarget]
                exact hlinks_post.toForall2)
              (by
                unfold activeMirBody
                rw [array_toList_reverse_append_singleton restMfs tfTarget]
                exact hlinks_post)
              hdisj_post htb hvalid hcid_pos hcid_act hcid_bor hbt
      · intro sc hsc hne_exp
        have hslot_eq : slot = .init (.scalar sc) := Option.some.inj (hslot.symm.trans hsc)
        subst hslot_eq
        cases hloc with
        | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
          · cases h
          · injection hv with hv'; subst hv'
            obtain ⟨b, msc, hv_b, rfl, _, htoBool⟩ := bool_of_immediateRel hbool_ty himmRel
            have hsc_b : sc = boolToScalar b := by injection hv_b
            subst hsc_b
            have hdec_b : decide ((boolToScalar b).bits ≠ 0) = b := by cases b <;> rfl
            rw [hdec_b] at hne_exp
            let tfCached := cacheFrameLocalLayout topFrame condIdx hlt_mf
              (translateTy condDecl.ty (activeMirBody rootBody s).layouts)
            have hread_ok :
                hooks.readAssertCondition () (.Copy ⟨condIdx, #[]⟩) m =
                ({ m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ }, .ok b) := by
              dsimp only [hooks]
              unfold annealTerminatorHooksLM4_1 annealTerminatorHooks Miri.Interpreter.runRvalue
              dsimp only []
              rw [EStateM.bind_eq_ok
                (annealEvalOperand_copy_live_multiFrame harr hlt_mf hdecl hmls_eq hcache)]
              dsimp only [annealReadImmediate, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
                Miri.Interpreter.Immediate.toScalar]
              rw [htoBool]
              rfl
            have hexp_beq_false : (expected == b) = false :=
              beq_eq_false_iff_ne.mpr (Ne.symm hne_exp)
            refine ⟨?_, ?_⟩
            · rw [ha_step_eq]
              unfold evalTerminator
              rw [hterm]
              have heval_a :
                  evalOperand s.frame.locals (.copy ⟨condIdx, .nil⟩) s.memory.borrows s.memory.globals
                    (activeMirBody rootBody s).layouts s.memory.callerLocals =
                  .ok (.scalar (boolToScalar b)) s.frame.locals := by
                unfold evalOperand; dsimp only []; rw [hsc]; rfl
              dsimp only []
              rw [heval_a]
              cases expected <;> cases b <;> (try exact False.elim (hne_exp rfl)) <;> rfl
            · rw [hm_step_eq]
              unfold Miri.Interpreter.ControlFlow.evalTerminator
              rw [htk_assert]
              dsimp only [Id.run]
              simp only [hign, hread_ok, Bool.false_or, hexp_beq_false, Bool.false_eq_true, ↓reduceIte]
              rfl

/-- **Correspondence (`step_terminator_call_diverging_panic_vs_unlinked`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing a
diverging `TerminatorKind.call func [] destination none unwind` to an unlinked
constant `defPath` (`findCallee? = none`, `lookupCallee = none`,
`isUnreachableCallTarget defPath = false`):
1. If `isAbortingPanicDefPath defPath = true` (`Terminators.lean:3230-3231`),
   Stage-1 `stepMirFn` halts with `MirStepNode.retOutcome .abort`;
2. If `isAbortingPanicDefPath defPath = false` and `isUnwindingPanicDefPath defPath = true`
   (`Terminators.lean:3233-3239`, e.g., `"core::panicking::panic"`), Stage-1
   `stepMirFn` dispatches `applyUnwindAction s s.frame.locals s.memory unwind`;
3. In both cases, `lean-miri` (`annealEvalCallLM4_1` without linked `core`
   panic shims) returns `.error (.unsupported "diverging call to unlinked non-unreachable callee")`. -/
theorem step_terminator_call_diverging_panic_vs_unlinked
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {func : MirAst.Operand} {destination : Place} {unwind : MirAst.UnwindAction}
    {defPath : DefPath}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call func .nil destination .none unwind)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hnot_unreach : isUnreachableCallTarget defPath = false)
    (hcallee_none :
      lookupCallee s.memory.callees (activeMirBody rootBody s).layouts
        defPath (extractCalleeTypeArgs func) s.memory.traitImpls = none)
    (hfind_none : findCallee? s.memory.callees defPath = none) :
    (isAbortingPanicDefPath defPath = true →
      stepMirFn rootBody s = MirStepNode.retOutcome .abort) ∧
    (isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = true →
      stepMirFn rootBody s =
        match applyUnwindAction s s.frame.locals s.memory unwind with
        | .running nextState => .step nextState
        | .halted out => .retOutcome out
        | .faulted fk => .fail fk) ∧
    (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m).2 =
      .error (.unsupported "diverging call to unlinked non-unreachable callee") := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, _⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      have ha_base :
          stepMirFn rootBody s =
            match isAbortingPanicDefPath defPath with
            | true => .retOutcome .abort
            | false =>
              match isUnwindingPanicDefPath defPath with
              | true =>
                match applyUnwindAction s s.frame.locals s.memory unwind with
                | .running nextState => .step nextState
                | .halted out => .retOutcome out
                | .faulted fk => .fail fk
              | false =>
                .extCall
                  { defPath := defPath, typeArgs := extractCalleeTypeArgs func,
                    args := [], memory := s.memory }
                  (resumeExternalDivergingCall s s.frame.locals unwind) := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm]
        unfold resolveCallTarget
        dsimp only []
        rw [hfunc]
        dsimp only [evalOperands]
        rw [hcallee_none, hnot_unreach]
        rfl
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (translateOperand func)
              ((List.nil : List MirAst.Operand).map fun a => ⟨defaultSpanRef, translateOperand a⟩).toArray
              (translatePlace destination) none (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator; rw [hterm]; rfl
      have hcall :
          annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
            (translateTerminator bb.terminator) m s.memory.fnPtrs =
          (m, .error (.unsupported "diverging call to unlinked non-unreachable callee")) := by
        unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
        rw [hback]; dsimp only []
        rw [hframe.location_eq]; dsimp only []
        rw [hbb]; dsimp only []
        rw [hterm, htk]; dsimp only []
        rw [hfunc]
        dsimp only [List.map, annealEvalCallArgsLM4_1, Miri.Interpreter.runRvalue, pure, EStateM.pure]
        rw [hfind_none]; dsimp only []
        rw [hnot_unreach]; rfl
      refine ⟨?_, ?_, ?_⟩
      · intro hab; rw [ha_base, hab]
      · intro hnab hunw_p; rw [ha_base, hnab, hunw_p]
      · unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
        unfold Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksLM4_1
        rw [htk]
        dsimp only [Id.run]
        rw [hcall]
        rfl

/-! ## 8. Non-Constant `FnDef` Local & Indirect `FnPtr` Call Simulations + `Safety` Divergence -/

/-- **Theorem 8a (`step_terminator_call_fnDef_local_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing a
returning `TerminatorKind.call (.copy ⟨fnIdx, .nil⟩) [] ⟨destIdx, .nil⟩ (some targetBb) unwind`
through a non-constant zero-sized function-item local `fnIdx`
(`fnDecl.ty.kind = .fnDef defPath []`) linked to `calleeBody` in `s.memory.callees`:
1. When `fnIdx` is `.dead`, both Stage-1 `stepMirFn` (`resolveCallTarget` /
   `evalOperand`) and `lean-miri` (`annealEvalNonConstCallLM4_1` /
   `annealEvalOperand`) fault with undefined behavior (`StepRelMultiFrame.ub`);
2. When `fnIdx` holds `.init .unit` (live ZST `.immediate .uninit` in `lean-miri`),
   both machines resolve `calleeBody`, push its stack frame, and step in lockstep
   to `MultiFrameStateRel`-related states at depth `d + 1` (`StepRelMultiFrame.step`). -/
theorem step_terminator_call_fnDef_local_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {fnIdx destIdx : Local} {fnDecl destDecl : LocalDecl}
    {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {defPath : DefPath} {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl}
    {calleeBb0 : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call (.copy ⟨fnIdx, .nil⟩) .nil ⟨destIdx, .nil⟩ (some targetBb) unwind)
    (hfn_decl : get? (activeMirBody rootBody s).localDecls fnIdx = some fnDecl)
    (hfn_ty : fnDecl.ty.kind = .fnDef defPath .nil)
    (hfn_imm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf fnIdx)
    (hcallee : findCallee? s.memory.callees defPath = some calleeBody)
    (htparam : calleeBody.typeParamCount = 0 := by rfl)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hdest_wf : ∀ tf, m.stack.frames.back? = some tf →
      CallerDestSlotWf m.machine tf destIdx destDecl)
    (hdest_live : ∀ tf, m.stack.frames.back? = some tf → IsLiveFrameLocal tf destIdx)
    (hfn_slot : get? s.frame.locals fnIdx = some .dead ∨
      get? s.frame.locals fnIdx = some (.init .unit))
    (hcallee_unwind : calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable :=
      by first | exact Or.inl rfl | exact Or.inr rfl) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m) := by
  rcases hstate with
    ⟨topFrame, hback, _, _, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨callerMf, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some callerMf := by rw [harr]; simp
      have htf_eq : topFrame = callerMf := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      obtain ⟨slot_f, mls_f, _, hlt_mf_f, hslot_f, hmls_f, hmls_eq_f, hloc_f⟩ :=
        hframe.lookup_local hfn_decl
      have hcache_f := hloc_f.layout_eq
      have himm_f' := hfn_imm callerMf hback mls_f hmls_f
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      unfold annealStepHooksForState
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (.Copy ⟨fnIdx, #[]⟩) #[]
              (translatePlace ⟨destIdx, .nil⟩) (some targetBb) (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator; rw [hterm]; rfl
      cases hloc_f with
      | indirect _ mp _ _ _ _ => exact False.elim (himm_f' mp rfl)
      | dead _ _ =>
        have heval_f :
            evalOperand s.frame.locals (.copy ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
              (activeMirBody rootBody s).layouts s.memory.callerLocals = .ub := by
          unfold evalOperand; dsimp only []; rw [hslot_f]
        have hcall_m :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m s.memory.fnPtrs =
            ({ m with stack := ⟨⟨restMfs.reverse ++
                [cacheFrameLocalLayout callerMf fnIdx hlt_mf_f
                  (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
             .error (.undefinedBehavior "read of dead local")) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]; dsimp only []
          rw [hframe.location_eq]; dsimp only []
          rw [hbb]; dsimp only []
          rw [hterm, htk]
          unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
          dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
          rw [EStateM.bind_eq_error
            (annealEvalOperand_copy_dead_multiFrame harr hlt_mf_f hfn_decl hmls_eq_f hcache_f)]
        unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        unfold resolveCallTarget
        dsimp only [Id.run, extractCalleeDefPath?]
        rw [heval_f, hcall_m]
        exact StepRelMultiFrame.ub _ _
      | immediate _ imm_f _ _ hval_f =>
        have hslot_init : slot_f = .init .unit := by
          rcases hfn_slot with hdead | hunit
          · rw [hslot_f] at hdead
            rcases hval_f with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> cases hdead
          · exact Option.some.inj (hslot_f.symm.trans hunit)
        subst hslot_init
        let callerMf' := cacheFrameLocalLayout callerMf fnIdx hlt_mf_f
          (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
        have hind_sub :
            ∀ (i : Nat) mp lay,
              callerMf'.locals[i]? =
                some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay) →
              (∃ lay₀,
                callerMf.locals[i]? =
                  some (Miri.Interpreter.LocalState.mk (.live (.indirect mp)) lay₀)) ∧
              get? s.frame.locals i = get? s.frame.locals i := by
          intro i mp lay hi
          refine ⟨?_, rfl⟩
          dsimp only [callerMf', cacheFrameLocalLayout] at hi
          by_cases hk : fnIdx = i
          · subst hk
            rw [Array.getElem?_set_self] at hi
            injection hi with h_eq
            have hv := congrArg Miri.Interpreter.LocalState.value h_eq
            rw [hmls_eq_f] at hv; cases hv
          · rw [Array.getElem?_set_ne _ hk] at hi
            exact ⟨lay, hi⟩
        have hdest_wf' : CallerDestSlotWf m.machine callerMf' destIdx destDecl :=
          (hdest_wf callerMf hback).mono_evalArgs
            (fun hd => hd.cache_layout hlt_mf_f _)
            (fun mp lay h => (hind_sub destIdx mp lay h).1)
        have hdest_live' : IsLiveFrameLocal callerMf' destIdx :=
          (hdest_live callerMf hback).cache_layout hlt_mf_f _
        have hd_fn : MemoryAllocDisjoint callerMf → MemoryAllocDisjoint callerMf' := by
          intro hd
          apply MemoryAllocDisjoint.mono_layout hd
          intro k
          by_cases hk : k = fnIdx
          · subst hk
            exists (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
            dsimp only [callerMf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_self, hmls_f]
            simp [hmls_eq_f]
          · exists (callerMf.locals[k]?).bind (·.layout)
            dsimp only [callerMf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
            cases callerMf.locals[k]? <;> rfl
        have hpush_sim :=
          step_terminator_call_args_simulation_ok
            (callerBody := activeMirBody rootBody s) (calleeBody := calleeBody)
            (callerAf := s.frame) (topFrame := callerMf) (restMfs := restMfs)
            (destIdx := destIdx) (destDecl := destDecl)
            (targetOpt := some targetBb) (unwind := unwind) (m := m)
            hcallee_decls hcallee_bb0 hdest_decl [] s.frame.locals callerMf' []
            rfl rfl rfl hind_sub hdest_wf' hdest_live' hd_fn
            (hframe.cache_local_layout hfn_decl hlt_mf_f)
            (.nil restDecls)
        generalize ha_ops_eq : OperandsEvalResult.ok ([] : List Value) s.frame.locals = aOps at hpush_sim
        generalize hm_ops_eq :
          ({ m with stack := ⟨⟨restMfs.reverse ++ [callerMf']⟩⟩ },
           Except.ok ([] : List (Miri.Interpreter.RvalueImmTy AnnealProv))) = mOps at hpush_sim
        cases hpush_sim with
        | ub _ _ => cases ha_ops_eq
        | ok argVals' locals'' callerMf'' calleeMf argImms' hid_eq hrc_eq hrp_eq hloc_sub _ hfr_caller'
            hres_dest hdest_rel_fn hrc_callee hcallee_no_ind hfr_callee _ hpush_spec =>
          cases ha_ops_eq
          have hm_imms : argImms' = [] := by
            injection hm_ops_eq with _ h; injection h with h2; exact h2.symm
          subst hm_imms
          have hcmf_eq : callerMf'' = callerMf' := by
            injection hm_ops_eq with hst _
            have hl := congrArg (fun st => st.stack.frames.toList) hst
            simpa using hl.symm
          subst hcmf_eq
          obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
          have hop_ty :
              operandTy (activeMirBody rootBody s).localDecls
                (activeMirBody rootBody s).layouts (.copy ⟨fnIdx, .nil⟩) =
              some fnDecl.ty := by
            simp [operandTy, placeTy, hfn_decl]
          have hcall_m :
              annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
                (translateTerminator bb.terminator) m s.memory.fnPtrs =
              ({ stack := ⟨⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩⟩
                 machine := m.machine }, .ok ()) := by
            unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
            rw [hback]; dsimp only []
            rw [hframe.location_eq]; dsimp only []
            rw [hbb]; dsimp only []
            rw [hterm, htk]
            unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
            dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
            rw [EStateM.bind_eq_ok
              (annealEvalOperand_copy_live_multiFrame harr hlt_mf_f hfn_decl hmls_eq_f hcache_f)]
            dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
            have hsome_fn :
                operandTy (activeMirBody rootBody s).localDecls
                  (activeMirBody rootBody s).layouts (.copy ⟨fnIdx, .nil⟩) =
                some { kind := .fnDef defPath .nil, layoutIdx := fnDecl.ty.layoutIdx } := by
              rw [hop_ty]
              cases hty_mk : fnDecl.ty with
              | mk k lidx => rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
            rw [hsome_fn]
            dsimp only []
            rw [hcallee]
            dsimp only []
            unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
            dsimp only []
            rw [array_back?_append_singleton restMfs.reverse callerMf']
            dsimp only []
            have hsize_after :
                (⟨restMfs.reverse ++ [callerMf']⟩ :
                  Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
                restMfs.length := by simp
            change resolveCallerDestinationPlace _ _ _ { localId := destIdx, projection := #[] } = _ at hres_dest
            rw [hsize_after, hres_dest]
            dsimp only []
            rw [hraw_ok]
            dsimp only []
            unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
            rw [hraw_curr]
            dsimp only []
            rw [hraw_state, hdone_eq]
          unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
            annealTerminatorHooksLM4_1
          rw [hterm, htk]
          unfold resolveCallTarget
          dsimp only [Id.run, extractCalleeDefPath?, bodyLocalDeclsOf]
          have heval_f :
              evalOperand s.frame.locals (.copy ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
                (activeMirBody rootBody s).layouts s.memory.callerLocals =
              .ok .unit s.frame.locals := by
            unfold evalOperand; dsimp only []; rw [hslot_f]; rfl
          rw [heval_f, hop_ty]
          have hextr : extractFnItemTarget? (some fnDecl.ty) = some (defPath, []) := by
            cases hty_mk : fnDecl.ty with
            | mk k lidx =>
              rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
          rw [hextr]
          dsimp only [evalOperands]
          rw [lookupCallee_nil_eq_of_findCallee_some _ _ _ _ hcallee htparam, hcall_m]
          dsimp only [checkCalleeTargetCompatible, pushCalleeFrame]
          have hsize_ne :
              ((⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).size == m.stack.frames.size) =
                false := by rw [harr]; simp
          simp only [Option.isSome_some, Bool.true_and, hsize_ne, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Except.map, pure, Pure.pure]
          apply StepRelMultiFrame.step
          let savedCaller : SavedCallerFrame :=
            { callerBody := activeMirBody rootBody s
              frame := { s.frame with locals := s.frame.locals }
              destination := ⟨destIdx, .nil⟩
              returnTarget := targetBb
              calleeProtectors := s.memory.activeProtectors
              returnUnwind := unwind
              isDiverging := false }
          have hlinks_caller' :
              CallerStackLinksRel rootBody m.machine savedCaller.callerBody savedCaller.frame
                s.memory.callStack s.memory.activeProtectors (callerMf' :: restMfs) :=
            hlinks.update_top_frame hrc_eq hrp_eq hid_eq hfr_caller'
              (fun mp0 lay0 h0 => ⟨(hloc_sub 0 mp0 lay0 h0).1, Or.inl (hloc_sub 0 mp0 lay0 h0).2⟩)
          have hlinks_post :
              CallerStackLinksRel rootBody m.machine calleeBody
                { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody [] }
                (savedCaller :: s.memory.callStack)
                ([] ++ s.memory.activeProtectors)
                (calleeMf :: callerMf' :: restMfs) :=
            .cons calleeBody
              { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody [] }
              savedCaller s.memory.callStack [] s.memory.activeProtectors
              calleeMf callerMf' restMfs
              (by rw [hrc_callee, nounwind_cont_eq hcallee_unwind] <;> rfl)
              (hdest_rel_fn savedCaller rfl rfl rfl) hfr_callee
              (fun mp0 lay0 _ _ _ h0 _ _ _ => False.elim (hcallee_no_ind 0 mp0 lay0 h0))
              rfl (by intro _ h; cases h) hlinks_caller'
          have hdisj_orig : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf]⟩ := by
            rw [← harr]; exact hdisj
          have hdisj_caller' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [callerMf']⟩ :=
            hdisj_orig.replace_top (hd_fn (hdisj_orig.intra_frame callerMf (by simp)))
              (fun i mp lay hi => (hloc_sub i mp lay hi).1)
          have hd_calleeMf : MemoryAllocDisjoint calleeMf :=
            fun i _ mp₁ _ lay₁ _ _ hi _ => False.elim (hcallee_no_ind i mp₁ lay₁ hi)
          have hdisj_post :
              MultiFrameAllocDisjoint ⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ := by
            have harr_eq :
                (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _) =
                  ⟨(restMfs.reverse ++ [callerMf']) ++ [calleeMf]⟩ := by
              apply Array.ext'; simp [List.reverse_cons]
            rw [harr_eq]
            refine ⟨?_, ?_⟩
            · intro mf hmf
              rcases List.mem_append.mp hmf with hmem_old | hsingle
              · exact hdisj_caller'.intra_frame mf hmem_old
              · rcases List.mem_singleton.mp hsingle with rfl; exact hd_calleeMf
            · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
              have hlen_old : (restMfs.reverse ++ [callerMf']).length = restMfs.length + 1 := by simp
              by_cases hf₁_top : f₁ = restMfs.length + 1
              · subst hf₁_top
                rw [← hlen_old, array_getElem?_append_singleton_last] at hf₁
                injection hf₁ with hmf₁_eq; subst hmf₁_eq
                exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
              · by_cases hf₂_top : f₂ = restMfs.length + 1
                · subst hf₂_top
                  rw [← hlen_old, array_getElem?_append_singleton_last] at hf₂
                  injection hf₂ with hmf₂_eq; subst hmf₂_eq
                  exact False.elim (hcallee_no_ind j mp₂ lay₂ hj)
                · have hlt₁ : f₁ < (restMfs.reverse ++ [callerMf']).length := by
                    have := Array.getElem?_eq_some_iff.mp hf₁ |>.1; simp at this; omega
                  have hlt₂ : f₂ < (restMfs.reverse ++ [callerMf']).length := by
                    have := Array.getElem?_eq_some_iff.mp hf₂ |>.1; simp at this; omega
                  rw [array_getElem?_append_singleton_of_lt _ _ hlt₁] at hf₁
                  rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
                  exact hdisj_caller'.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
          have hrev_post :
              (⟨(callerMf' :: restMfs).reverse ++ [calleeMf]⟩ : Array _).toList.reverse =
                calleeMf :: callerMf' :: restMfs :=
            array_toList_reverse_append_singleton (callerMf' :: restMfs) calleeMf
          exact .mk calleeMf
            (array_back?_append_singleton (callerMf' :: restMfs).reverse calleeMf)
            (fun hnil => nomatch hnil)
            (fun _ => rfl)
            (by
              unfold FrameStackRel annealFrameStackTopDown activeMirBody
              rw [hrev_post]; exact hlinks_post.toForall2)
            (by unfold activeMirBody; rw [hrev_post]; exact hlinks_post)
            hdisj_post htb hvalid hcid_pos hcid_act hcid_bor
            (hbt.of_pushFrame rfl)

/-- **Theorem 8b (`step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m` (where immediate
locals are in the pointer-free `ImmediateRel` fragment), calling an indirect
function-pointer local `func = .copy ⟨fnIdx, .nil⟩` (`fnDecl.ty.kind = .fnPtr ...`)
faults with undefined behavior (`StepRelMultiFrame.ub`) across **all** states of
`fnIdx` (`.dead`, `.uninit`, or provenance-free integer scalar
`transmute::<usize, fn()>(addr)`, matching `FunctionPointers.lean:124-125`
`DanglingIntPointer` and Stage-1 `Terminators.lean:384`). -/
theorem step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {fnIdx : Local} {fnDecl : LocalDecl}
    {callerInputs : List RigidTy} {callerOut : RigidTy}
    {callerSafety : Safety} {callerAbi : CallConv}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call (.copy ⟨fnIdx, .nil⟩) .nil destination (some targetBb) unwind)
    (hfn_decl : get? (activeMirBody rootBody s).localDecls fnIdx = some fnDecl)
    (hfn_ty : fnDecl.ty.kind = .fnPtr callerInputs callerOut callerSafety callerAbi)
    (hfn_imm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf fnIdx) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m) := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨callerMf, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some callerMf := by rw [harr]; simp
      have htf_eq : topFrame = callerMf := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      obtain ⟨slot_f, mls_f, _, hlt_mf_f, hslot_f, hmls_f, hmls_eq_f, hloc_f⟩ :=
        hframe.lookup_local hfn_decl
      have hcache_f := hloc_f.layout_eq
      have himm_f' := hfn_imm callerMf hback mls_f hmls_f
      rw [stepMirFn_activeMirBody_eq rootBody s hphase]
      have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
      simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
      unfold annealStepHooksForState
      rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none]
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (.Copy ⟨fnIdx, #[]⟩) #[]
              (translatePlace destination) (some targetBb) (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator; rw [hterm]; rfl
      have hop_ty :
          operandTy (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts (.copy ⟨fnIdx, .nil⟩) =
          some fnDecl.ty := by
        simp [operandTy, placeTy, hfn_decl]
      cases hloc_f with
      | indirect _ mp _ _ _ _ => exact False.elim (himm_f' mp rfl)
      | dead _ _ =>
        have heval_f :
            evalOperand s.frame.locals (.copy ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
              (activeMirBody rootBody s).layouts s.memory.callerLocals = .ub := by
          unfold evalOperand; dsimp only []; rw [hslot_f]
        have hcall_m :
            annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
              (translateTerminator bb.terminator) m s.memory.fnPtrs =
            ({ m with stack := ⟨⟨restMfs.reverse ++
                [cacheFrameLocalLayout callerMf fnIdx hlt_mf_f
                  (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
             .error (.undefinedBehavior "read of dead local")) := by
          unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
          rw [hback]; dsimp only []
          rw [hframe.location_eq]; dsimp only []
          rw [hbb]; dsimp only []
          rw [hterm, htk]
          unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
          dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
          rw [EStateM.bind_eq_error
            (annealEvalOperand_copy_dead_multiFrame harr hlt_mf_f hfn_decl hmls_eq_f hcache_f)]
        unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksLM4_1
        rw [hterm, htk]
        unfold resolveCallTarget
        dsimp only [Id.run, extractCalleeDefPath?]
        rw [heval_f, hcall_m]
        exact StepRelMultiFrame.ub _ _
      | immediate _ imm_f _ _ hval_f =>
        rcases hval_f with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · have heval_f :
              evalOperand s.frame.locals (.copy ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
                (activeMirBody rootBody s).layouts s.memory.callerLocals = .ub := by
            unfold evalOperand; dsimp only []; rw [hslot_f]
          have hcall_m :
              annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
                (translateTerminator bb.terminator) m s.memory.fnPtrs =
              ({ m with stack := ⟨⟨restMfs.reverse ++
                  [cacheFrameLocalLayout callerMf fnIdx hlt_mf_f
                    (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
               .error (.undefinedBehavior "read of uninitialized local")) := by
            unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
            rw [hback]; dsimp only []
            rw [hframe.location_eq]; dsimp only []
            rw [hbb]; dsimp only []
            rw [hterm, htk]
            unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
            dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
            rw [EStateM.bind_eq_ok
              (annealEvalOperand_copy_live_multiFrame harr hlt_mf_f hfn_decl hmls_eq_f hcache_f)]
            dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
            rw [hop_ty]
            cases hty_mk : fnDecl.ty with
            | mk k lidx =>
              rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
          unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
            annealTerminatorHooksLM4_1
          rw [hterm, htk]
          unfold resolveCallTarget
          dsimp only [Id.run, extractCalleeDefPath?]
          rw [heval_f, hcall_m]
          exact StepRelMultiFrame.ub _ _
        · have hsz8 :
              (translateTy fnDecl.ty (activeMirBody rootBody s).layouts).layout.size =
                Miri.ABI.Size.ofBytes 8 := by
            cases hty_mk : fnDecl.ty with
            | mk k lidx =>
              rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
          cases himmRel with
          | unit hz =>
            rw [hsz8] at hz; cases hz
          | scalarPair _ _ _ _ _ _ hagg _ =>
            rcases hagg with ⟨_, ht⟩ | ⟨_, _, ht⟩ <;> (rw [hfn_ty] at ht; cases ht)
          | scalar sc msc hsc_rel hsz_eq _ _ =>
            have hsc_sz8 : sc.sizeBytes = 8 := by
              rw [hsz8] at hsz_eq
              rcases hsc_rel.validBytes <;> rename_i hb
              · rw [hb] at hsz_eq; cases hsz_eq
              · rcases hb with hb | hb | hb | hb
                · rw [hb] at hsz_eq; cases hsz_eq
                · rw [hb] at hsz_eq; cases hsz_eq
                · exact hb
                · rw [hb] at hsz_eq; cases hsz_eq
            have htoPtr := scalar_fromScalarInt_toPointer_eq hsc_rel hsc_sz8
            have hcall_m :
                annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
                  (translateTerminator bb.terminator) m s.memory.fnPtrs =
                ({ m with stack := ⟨⟨restMfs.reverse ++
                    [cacheFrameLocalLayout callerMf fnIdx hlt_mf_f
                      (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)]⟩⟩ },
                 .error (.undefinedBehavior "DanglingIntPointer")) := by
              unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
              rw [hback]; dsimp only []
              rw [hframe.location_eq]; dsimp only []
              rw [hbb]; dsimp only []
              rw [hterm, htk]
              unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
              dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
              rw [EStateM.bind_eq_ok
                (annealEvalOperand_copy_live_multiFrame harr hlt_mf_f hfn_decl hmls_eq_f hcache_f)]
              dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
              rw [hop_ty]
              cases hty_mk : fnDecl.ty with
              | mk k lidx =>
                rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty
                dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
                  Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
                rw [htoPtr]
                rfl
            unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
              annealTerminatorHooksLM4_1
            rw [hterm, htk]
            unfold resolveCallTarget
            dsimp only [Id.run, extractCalleeDefPath?]
            have heval_a :
                evalOperand s.frame.locals (.copy ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
                  (activeMirBody rootBody s).layouts s.memory.callerLocals =
                .ok (.scalar sc) s.frame.locals := by
              unfold evalOperand; dsimp only []; rw [hslot_f]; rfl
            rw [heval_a, hcall_m]
            exact StepRelMultiFrame.ub _ _

/-- Pre-state relation (`IndirectFnPtrMovePre`) for a provenance-bearing indirect
function-pointer call `TerminatorKind.call (.move ⟨fnIdx, .nil⟩) ...`:
* Because `ImmediateRel` / `LocalRel` (`SimLM1_1.lean`) is the pointer-free
  scalar, scalar-pair, and unit immediate fragment shared across `LM-1.1..LM-4.1`,
  `IndirectFnPtrMovePre` serves as the intermediate state relation holding a
  reified function pointer in local `fnIdx` between its creation by
  `StatementKind.assign ⟨fnIdx, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer") ...)`
  (`step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`, which
  steps from `MultiFrameStateRel` into `IndirectFnPtrMovePre`) and its consumption
  by `TerminatorKind.call (.move ⟨fnIdx, .nil⟩) ...`
  (`step_terminator_call_indirect_fnPtr_move_simulation`, which moves `fnIdx` back
  to `.uninit` and steps back into `MultiFrameStateRel`);
* Before the `.move`, local `fnIdx` holds `Value.ptr ptrVal 8` in `s.frame.locals`
  and `Scalar.fromPointer annealTargetDataLayout mptr` in `topFrame.locals`, with
  `m.machine.lookupBaseAddr mAllocId = some baseAddr`,
  `mAllocId.value.toNat = ptrVal.allocId`,
  `mptr.offset = Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes)`
  (without `UInt64` wraparound), and `lookupBorrow s.memory.borrows ptrVal.tag = none`;
* Once `fnIdx` is moved to `.uninit` in both `s` and `m`, the deinitialized frame
  pair `(s_deinit, m_deinit)` satisfies full `MultiFrameStateRel rootBody s_deinit m_deinit`. -/
structure IndirectFnPtrMovePre
    (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit))
    (fnIdx : Local) (fnDecl : LocalDecl)
    (ptrVal : ProvenancePtr) (mAllocId : Miri.Memory.AllocId)
    (mTag : Miri.Memory.BorTag) (baseAddr : UInt64) : Prop where
  frames_eq : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩
  fn_lt_af : fnIdx < s.frame.locals.length
  fn_lt_mf : fnIdx < topFrame.locals.size
  fn_decl : get? (activeMirBody rootBody s).localDecls fnIdx = some fnDecl
  fn_slot : get? s.frame.locals fnIdx = some (.init (.ptr ptrVal 8))
  fn_mls :
    ∃ cachedLay,
      (topFrame.locals[fnIdx]'fn_lt_mf) =
        ⟨.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes),
             .concrete mAllocId mTag⟩))),
         cachedLay⟩ ∧
      (∀ l, cachedLay = some l → l = translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
  allocId_eq : mAllocId.value.toNat = ptrVal.allocId
  baseAddr_lookup : m.machine.lookupBaseAddr mAllocId = some baseAddr
  offset_no_wrap :
    baseAddr ≤ baseAddr + UInt64.ofNat ptrVal.offsetBytes ∧
    (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr).toNat = ptrVal.offsetBytes
  not_borrow : lookupBorrow s.memory.borrows ptrVal.tag = none
  deinit_rel :
    let tf₀ := cacheFrameLocalLayout topFrame fnIdx fn_lt_mf
      (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
    let tfDeinit := deinitFrameLocal tf₀ fnIdx (by rw [cacheFrameLocalLayout_size]; exact fn_lt_mf)
    MultiFrameStateRel rootBody
      { s with frame := { s.frame with locals := s.frame.locals.set fnIdx .uninit } }
      { m with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ }

/-- **Theorem 8c (`step_terminator_call_indirect_fnPtr_move_simulation`)**:
At arbitrary stack depth under `IndirectFnPtrMovePre`
(`fnDecl.ty.kind = .fnPtr callerInputs callerOut callerSafety callerAbi`),
executing `TerminatorKind.call (.move ⟨fnIdx, .nil⟩) [] ⟨destIdx, .nil⟩ (some targetBb) unwind`:
1. **Non-zero offset UB**: when `ptrVal.offsetBytes ≠ 0`, both Stage-1 `stepMirFn`
   and `lean-miri` fault with UB (`StepRelMultiFrame.ub`);
2. **Non-function allocation UB**: when `ptrVal.offsetBytes = 0` and
   `lookupFnPtr s.memory.fnPtrs ptrVal.allocId = none`, both fault with UB
   (`StepRelMultiFrame.ub`);
3. **Runtime ABI / arity mismatch UB**: when `ptrVal.offsetBytes = 0`,
   `lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry` (`fnEntry.typeArgs = []`),
   and `annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0 = false`
   (which implies `fnEntryCompatibleWithCallSite = false`), both fault with UB
   (`StepRelMultiFrame.ub`);
4. **Valid indirect function-pointer call**: when `ptrVal.offsetBytes = 0`,
   `lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry` (`fnEntry.typeArgs = []`),
   `fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty) = true`,
   `annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0 = true`,
   `findCallee? s.memory.callees fnEntry.defPath = some calleeBody`
   (`calleeBody.typeParamCount = 0`), and `annealCalleeAbiCompatible fnEntry calleeBody 0 = true`
   (matching `checkCalleeTargetCompatible = true`), **both** Stage-1 `stepMirFn`
   and `lean-miri` deinitialize `fnIdx` to `.uninit` and push `calleeBody` into
   `MultiFrameStateRel`-related states at depth `d + 1` (`StepRelMultiFrame.step`)! -/
theorem step_terminator_call_indirect_fnPtr_move_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {fnIdx destIdx : Local} {fnDecl destDecl : LocalDecl}
    {ptrVal : ProvenancePtr} {mAllocId : Miri.Memory.AllocId}
    {mTag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {callerInputs : List RigidTy} {callerOut : RigidTy}
    {callerSafety : Safety} {callerAbi : CallConv}
    {bb : BasicBlockData} {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    (hpre : IndirectFnPtrMovePre rootBody s m topFrame restMfs fnIdx fnDecl ptrVal mAllocId mTag baseAddr)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call (.move ⟨fnIdx, .nil⟩) .nil ⟨destIdx, .nil⟩ (some targetBb) unwind)
    (hfn_ty : fnDecl.ty.kind = .fnPtr callerInputs callerOut callerSafety callerAbi)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl) :
    (ptrVal.offsetBytes ≠ 0 →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) ∧
    (ptrVal.offsetBytes = 0 →
      lookupFnPtr s.memory.fnPtrs ptrVal.allocId = none →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) ∧
    (∀ fnEntry,
      ptrVal.offsetBytes = 0 →
      lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry →
      fnEntry.typeArgs = [] →
      annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0 = false →
      fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty) = false →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) ∧
    (∀ fnEntry calleeBody retDecl restDecls calleeBb0,
      ptrVal.offsetBytes = 0 →
      lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry →
      fnEntry.typeArgs = [] →
      fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty) = true →
      annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0 = true →
      findCallee? s.memory.callees fnEntry.defPath = some calleeBody →
      calleeBody.typeParamCount = 0 →
      calleeBody.localDecls = retDecl :: restDecls →
      get? calleeBody.basicBlocks 0 = some calleeBb0 →
      annealCalleeAbiCompatible fnEntry calleeBody 0 = true →
      (∀ tf, tf = deinitFrameLocal
        (cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
          (translateTy fnDecl.ty (activeMirBody rootBody s).layouts))
        fnIdx (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf) →
        CallerDestSlotWf m.machine tf destIdx destDecl ∧
        IsLiveFrameLocal tf destIdx) →
      (calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable) →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m)) := by
  obtain ⟨cachedLay, hmls_f, hcache_f⟩ := hpre.fn_mls
  have hdeinit_state := hpre.deinit_rel
  dsimp only at hdeinit_state
  let tf₀ := cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
    (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
  let tfDeinit := deinitFrameLocal tf₀ fnIdx
    (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf)
  let sDeinit : MachineState :=
    { s with frame := { s.frame with locals := s.frame.locals.set fnIdx .uninit } }
  let mDeinit : AnnealStepState :=
    { m with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ }
  rcases hdeinit_state with
    ⟨tf_d, hback_d, _, _, _, hlinks_d, hdisj_d, htb_d, hvalid_d,
      hcid_pos_d, hcid_act_d, hcid_bor_d, hbt_d⟩
  have htf_d_eq : tf_d = tfDeinit :=
    Option.some.inj (hback_d.symm.trans (array_back?_append_singleton restMfs.reverse tfDeinit))
  subst htf_d_eq
  have hforall_d := hlinks_d.toForall2
  have hrev_d : mDeinit.stack.frames.toList.reverse = tfDeinit :: restMfs :=
    array_toList_reverse_append_singleton restMfs tfDeinit
  rw [hrev_d] at hlinks_d hforall_d
  have hfr_d : FrameRel (activeMirBody rootBody s) m.machine sDeinit.frame tfDeinit := by
    cases hforall_d with | cons hfr _ => exact hfr
  have hbody_top : topFrame.body = translateBody (activeMirBody rootBody s) := hfr_d.body_eq
  have hloc_top : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfr_d.location_eq
  have hback_top : m.stack.frames.back? = some topFrame := by
    rw [hpre.frames_eq]; exact array_back?_append_singleton restMfs.reverse topFrame
  have hop_ty :
      operandTy (activeMirBody rootBody s).localDecls
        (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
      some fnDecl.ty := by
    simp [operandTy, placeTy, hpre.fn_decl]
  have htk :
      (translateTerminator bb.terminator).kind =
        .Call (.Move ⟨fnIdx, #[]⟩) #[]
          (translatePlace ⟨destIdx, .nil⟩) (some targetBb) (translateUnwindAction unwind)
          .Normal defaultSpanRef := by
    unfold translateTerminator; rw [hterm]; rfl
  let mptr : Miri.Memory.Pointer AnnealProv :=
    ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes),
     .concrete mAllocId mTag⟩
  have hmove_m :
      annealEvalOperand (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
        (.Move ⟨fnIdx, #[]⟩) none m =
      .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
           translateTy fnDecl.ty (activeMirBody rootBody s).layouts⟩ mDeinit :=
    annealEvalOperand_move_live_multiFrame hpre.frames_eq hpre.fn_lt_mf hpre.fn_decl hmls_f hcache_f
  have hmove_a :
      evalOperand s.frame.locals (.move ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
        (activeMirBody rootBody s).layouts s.memory.callerLocals =
      .ok (.ptr ptrVal 8) (s.frame.locals.set fnIdx .uninit) := by
    unfold evalOperand
    dsimp only []
    rw [hpre.fn_slot]
    dsimp only []
    rw [set?_eq_some_set hpre.fn_lt_af .uninit]
  have hres_ptr :
      annealResolvePtr mDeinit.machine mptr.withOptionalProvenance 0 =
        .ok ⟨mAllocId,
             Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr),
             mTag⟩ := by
    unfold annealResolvePtr
    dsimp only [mDeinit, mptr, Miri.Memory.Pointer.withOptionalProvenance, Miri.ABI.Size.ofBytes]
    rw [hpre.baseAddr_lookup]
    dsimp only []
    exact ite_eq_left_iff.mpr fun h => absurd hpre.offset_no_wrap.1 h
  have hm_step_eq :
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m =
        miriFinishStep
          (Miri.Interpreter.ControlFlow.evalTerminator
            (annealTerminatorHooksLM4_1 (activeMirBody rootBody s) s.memory.callees
              (annealPoppedFrameState s) s.memory.fnPtrs)
            () (translateTerminator bb.terminator) m) := by
    unfold annealStepHooksForState
    exact miri_step_at_terminator_multiFrame hback_top hbody_top hloc_top hbb hstmt_none
  have ha_step_eq :
      stepMirFn rootBody s = evalTerminator s bb.terminator (some (activeMirBody rootBody s)) := by
    rw [stepMirFn_activeMirBody_eq rootBody s hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hoff_ne
    have hbeq_off : Nat.beq ptrVal.offsetBytes 0 = false := by
      cases hb : Nat.beq ptrVal.offsetBytes 0
      · rfl
      · exact False.elim (hoff_ne (Nat.eq_of_beq_eq_true hb))
    have hsz_ne :
        (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
          Miri.ABI.Size.ZERO) = true := by
      rw [bne_iff_ne]
      intro heq
      have hbytes := congrArg (fun sz => sz.bytes.toNat) heq
      dsimp only [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hbytes
      rw [hpre.offset_no_wrap.2] at hbytes
      exact hoff_ne hbytes
    have hcall_m :
        annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
          (translateTerminator bb.terminator) m s.memory.fnPtrs =
        (mDeinit, .error (.undefinedBehavior "InvalidFunctionPointer")) := by
      unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
      rw [hback_top]; dsimp only []
      rw [hloc_top]; dsimp only []
      rw [hbb]; dsimp only []
      rw [hterm, htk]
      unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
      dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
      rw [EStateM.bind_eq_ok hmove_m]
      dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hop_ty]
      cases hty_mk : fnDecl.ty with
      | mk k lidx =>
        rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]
        dsimp only []
        rw [hsz_ne]
        rfl
    rw [ha_step_eq, hm_step_eq]
    unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, htk]
    unfold resolveCallTarget
    dsimp only [Id.run, extractCalleeDefPath?]
    rw [hmove_a]
    dsimp only []
    rw [hbeq_off, hcall_m]
    exact StepRelMultiFrame.ub _ _
  · intro hoff0 hlookup_none
    have hsz_eq0 :
        (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
          Miri.ABI.Size.ZERO) = false := by
      rw [bne_eq_false_iff_eq]
      have h0 : baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr = 0 := by
        rw [hoff0]; simp
      rw [h0]; rfl
    have hcall_m :
        annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
          (translateTerminator bb.terminator) m s.memory.fnPtrs =
        (mDeinit, .error (.undefinedBehavior "InvalidFunctionPointer")) := by
      unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
      rw [hback_top]; dsimp only []
      rw [hloc_top]; dsimp only []
      rw [hbb]; dsimp only []
      rw [hterm, htk]
      unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
      dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
      rw [EStateM.bind_eq_ok hmove_m]
      dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hop_ty]
      cases hty_mk : fnDecl.ty with
      | mk k lidx =>
        rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]; dsimp only []
        rw [hsz_eq0, hpre.allocId_eq, hlookup_none]; rfl
    rw [ha_step_eq, hm_step_eq]
    unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, htk]
    unfold resolveCallTarget
    dsimp only [Id.run, extractCalleeDefPath?]
    rw [hmove_a]
    dsimp only []
    rw [hoff0, hpre.not_borrow]
    dsimp only [Nat.beq, Bool.and]
    rw [hlookup_none, hcall_m]
    exact StepRelMultiFrame.ub _ _
  · intro fnEntry hoff0 hlookup_some htargs_nil habi_m habi_a
    have hsz_eq0 :
        (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
          Miri.ABI.Size.ZERO) = false := by
      rw [bne_eq_false_iff_eq]
      have h0 : baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr = 0 := by
        rw [hoff0]; simp
      rw [h0]; rfl
    have hcall_m :
        annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
          (translateTerminator bb.terminator) m s.memory.fnPtrs =
        (mDeinit, .error (.undefinedBehavior "indirect call ABI mismatch")) := by
      unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
      rw [hback_top]; dsimp only []
      rw [hloc_top]; dsimp only []
      rw [hbb]; dsimp only []
      rw [hterm, htk]
      unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
      dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
      rw [EStateM.bind_eq_ok hmove_m]
      dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hop_ty]
      cases hty_mk : fnDecl.ty with
      | mk k lidx =>
        rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]; dsimp only [List.length]
        rw [hsz_eq0, hpre.allocId_eq, hlookup_some]; dsimp only []
        rw [htargs_nil]
        simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty, Bool.not_true, Bool.not_false, habi_m]
    rw [ha_step_eq, hm_step_eq]
    unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
      annealTerminatorHooksLM4_1
    rw [hterm, htk]
    unfold resolveCallTarget
    dsimp only [Id.run, extractCalleeDefPath?, bodyLocalDeclsOf, length, List.length]
    rw [hmove_a]
    dsimp only []
    rw [hoff0, hpre.not_borrow]
    dsimp only [Nat.beq, Bool.and]
    rw [hlookup_some, hop_ty]; dsimp only []; rw [habi_a, hcall_m]
    exact StepRelMultiFrame.ub _ _
  · intro fnEntry calleeBody retDecl restDecls calleeBb0 hoff0 hlookup_some htargs_nil
      habi_a habi_m hcallee htparam hcallee_decls hcallee_bb0 hcal_abi hdest_deinit hcallee_unwind
    obtain ⟨hdest_wf_d, hdest_live_d⟩ := hdest_deinit tfDeinit rfl
    have hsz_eq0 :
        (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
          Miri.ABI.Size.ZERO) = false := by
      rw [bne_eq_false_iff_eq]
      have h0 : baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr = 0 := by
        rw [hoff0]; simp
      rw [h0]; rfl
    have hpush_sim :=
      step_terminator_call_args_simulation_ok
        (callerBody := activeMirBody rootBody s) (calleeBody := calleeBody)
        (callerAf := sDeinit.frame) (topFrame := tfDeinit) (restMfs := restMfs)
        (destIdx := destIdx) (destDecl := destDecl)
        (targetOpt := some targetBb) (unwind := unwind) (m := mDeinit)
        hcallee_decls hcallee_bb0 hdest_decl [] sDeinit.frame.locals tfDeinit []
        rfl rfl rfl (fun _ _ lay h => ⟨⟨lay, h⟩, rfl⟩)
        hdest_wf_d hdest_live_d id hfr_d (.nil restDecls)
    generalize ha_ops_eq : OperandsEvalResult.ok ([] : List Value) sDeinit.frame.locals = aOps at hpush_sim
    generalize hm_ops_eq :
      ({ mDeinit with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ },
       Except.ok ([] : List (Miri.Interpreter.RvalueImmTy AnnealProv))) = mOps at hpush_sim
    cases hpush_sim with
    | ub _ _ => cases ha_ops_eq
    | ok argVals' locals'' tfDeinit' calleeMf argImms' hid_eq hrc_eq hrp_eq hloc_sub _ hfr_caller'
        hres_dest hdest_rel_fn hrc_callee hcallee_no_ind hfr_callee _ hpush_spec =>
      cases ha_ops_eq
      have hm_imms : argImms' = [] := by
        injection hm_ops_eq with _ h; injection h with h2; exact h2.symm
      subst hm_imms
      have htf_eq : tfDeinit' = tfDeinit := by
        injection hm_ops_eq with hst _
        have hl := congrArg (fun st => st.stack.frames.toList) hst
        simpa using hl.symm
      subst htf_eq
      obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
      have hcall_m :
          annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
            (translateTerminator bb.terminator) m s.memory.fnPtrs =
          ({ stack := ⟨⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩⟩
             machine := m.machine }, .ok ()) := by
        unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
        rw [hback_top]; dsimp only []
        rw [hloc_top]; dsimp only []
        rw [hbb]; dsimp only []
        rw [hterm, htk]
        unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
        dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
        rw [EStateM.bind_eq_ok hmove_m]
        dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        have hsome_fn :
            operandTy (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
            some { kind := .fnPtr callerInputs callerOut callerSafety callerAbi,
                   layoutIdx := fnDecl.ty.layoutIdx } := by
          rw [hop_ty]
          cases hty_mk : fnDecl.ty with
          | mk k lidx => rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
        rw [hsome_fn]
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]; dsimp only [List.length]
        rw [hsz_eq0, hpre.allocId_eq, hlookup_some]; dsimp only []
        rw [htargs_nil]
        simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty, Bool.not_true, habi_m]
        rw [hcallee]; dsimp only []
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, hcal_abi]
        unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
        dsimp only [mDeinit]
        rw [array_back?_append_singleton restMfs.reverse tfDeinit]
        dsimp only []
        have hsize_after :
            (⟨restMfs.reverse ++ [tfDeinit]⟩ :
              Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
            restMfs.length := by simp
        change resolveCallerDestinationPlace _ _ _ { localId := destIdx, projection := #[] } = _ at hres_dest
        rw [hsize_after, hres_dest]
        dsimp only []
        dsimp only [mDeinit] at hraw_ok hraw_state hdone_eq
        rw [hraw_ok]; dsimp only []
        unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
        rw [hraw_curr]; dsimp only []
        rw [hraw_state, hdone_eq]
      have hcompat_a :
          checkCalleeTargetCompatible
            { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs,
              fnSig := fnEntry.fnSig, isIndirect := true }
            calleeBody 0 = true := by
        unfold checkCalleeTargetCompatible
        dsimp only []
        unfold annealCalleeAbiCompatible at hcal_abi
        exact hcal_abi
      rw [ha_step_eq, hm_step_eq]
      unfold evalTerminator Miri.Interpreter.ControlFlow.evalTerminator
        annealTerminatorHooksLM4_1
      rw [hterm, htk]
      unfold resolveCallTarget
      dsimp only [Id.run, extractCalleeDefPath?, bodyLocalDeclsOf, length, List.length]
      rw [hmove_a]
      dsimp only []
      rw [hoff0, hpre.not_borrow]
      dsimp only [Nat.beq, Bool.and]
      rw [hlookup_some, hop_ty]; dsimp only []; rw [habi_a]
      dsimp only [evalOperands, length]
      rw [htargs_nil,
        lookupCallee_nil_eq_of_findCallee_some _ _ _ _ hcallee htparam]
      dsimp only [List.length]
      have hcompat_a' :
          checkCalleeTargetCompatible
            { defPath := fnEntry.defPath, typeArgs := [],
              fnSig := fnEntry.fnSig, isIndirect := true }
            calleeBody 0 = true := by
        simpa [htargs_nil] using hcompat_a
      rw [hcompat_a', hcall_m]
      dsimp only [pushCalleeFrame]
      have hsize_ne :
          ((⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩ : Array _).size == m.stack.frames.size) =
            false := by rw [hpre.frames_eq]; simp
      simp only [Option.isSome_some, hsize_ne,
        Bool.false_eq_true, ↓reduceIte, Except.map, pure, Pure.pure,
        miriFinishStep]
      apply StepRelMultiFrame.step
      let savedCaller : SavedCallerFrame :=
        { callerBody := activeMirBody rootBody s
          frame := { s.frame with locals := s.frame.locals.set fnIdx .uninit }
          destination := ⟨destIdx, .nil⟩
          returnTarget := targetBb
          calleeProtectors := s.memory.activeProtectors
          returnUnwind := unwind
          isDiverging := false }
      have hlinks_caller' :
          CallerStackLinksRel rootBody m.machine savedCaller.callerBody savedCaller.frame
            s.memory.callStack s.memory.activeProtectors (tfDeinit :: restMfs) :=
        hlinks_d.update_top_frame hrc_eq hrp_eq hid_eq hfr_caller'
          (fun mp0 lay0 h0 => ⟨(hloc_sub 0 mp0 lay0 h0).1, Or.inl (hloc_sub 0 mp0 lay0 h0).2⟩)
      have hlinks_post :
          CallerStackLinksRel rootBody m.machine calleeBody
            { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody [] }
            (savedCaller :: s.memory.callStack)
            ([] ++ s.memory.activeProtectors)
            (calleeMf :: tfDeinit :: restMfs) :=
        .cons calleeBody
          { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody [] }
          savedCaller s.memory.callStack [] s.memory.activeProtectors
          calleeMf tfDeinit restMfs
          (by rw [hrc_callee, nounwind_cont_eq hcallee_unwind] <;> rfl)
          (hdest_rel_fn savedCaller rfl rfl rfl) hfr_callee
          (fun mp0 lay0 _ _ _ h0 _ _ _ => False.elim (hcallee_no_ind 0 mp0 lay0 h0))
          rfl (by intro _ h; cases h) hlinks_caller'
      have hd_calleeMf : MemoryAllocDisjoint calleeMf :=
        fun i _ mp₁ _ lay₁ _ _ hi _ => False.elim (hcallee_no_ind i mp₁ lay₁ hi)
      have hdisj_post :
          MultiFrameAllocDisjoint ⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩ := by
        have harr_eq :
            (⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩ : Array _) =
              ⟨(restMfs.reverse ++ [tfDeinit]) ++ [calleeMf]⟩ := by
          apply Array.ext'; simp [List.reverse_cons]
        rw [harr_eq]
        refine ⟨?_, ?_⟩
        · intro mf hmf
          rcases List.mem_append.mp hmf with hmem_old | hsingle
          · exact hdisj_d.intra_frame mf hmem_old
          · rcases List.mem_singleton.mp hsingle with rfl; exact hd_calleeMf
        · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
          have hlen_old : (restMfs.reverse ++ [tfDeinit]).length = restMfs.length + 1 := by simp
          by_cases hf₁_top : f₁ = restMfs.length + 1
          · subst hf₁_top
            rw [← hlen_old, array_getElem?_append_singleton_last] at hf₁
            injection hf₁ with hmf₁_eq; subst hmf₁_eq
            exact False.elim (hcallee_no_ind i mp₁ lay₁ hi)
          · by_cases hf₂_top : f₂ = restMfs.length + 1
            · subst hf₂_top
              rw [← hlen_old, array_getElem?_append_singleton_last] at hf₂
              injection hf₂ with hmf₂_eq; subst hmf₂_eq
              exact False.elim (hcallee_no_ind j mp₂ lay₂ hj)
            · have hlt₁ : f₁ < (restMfs.reverse ++ [tfDeinit]).length := by
                have := Array.getElem?_eq_some_iff.mp hf₁ |>.1; simp at this; omega
              have hlt₂ : f₂ < (restMfs.reverse ++ [tfDeinit]).length := by
                have := Array.getElem?_eq_some_iff.mp hf₂ |>.1; simp at this; omega
              rw [array_getElem?_append_singleton_of_lt _ _ hlt₁] at hf₁
              rw [array_getElem?_append_singleton_of_lt _ _ hlt₂] at hf₂
              exact hdisj_d.inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
      have hrev_post :
          (⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩ : Array _).toList.reverse =
            calleeMf :: tfDeinit :: restMfs :=
        array_toList_reverse_append_singleton (tfDeinit :: restMfs) calleeMf
      exact .mk calleeMf
        (array_back?_append_singleton (tfDeinit :: restMfs).reverse calleeMf)
        (fun hnil => nomatch hnil)
        (fun _ => rfl)
        (by
          unfold FrameStackRel annealFrameStackTopDown activeMirBody
          rw [hrev_post]; exact hlinks_post.toForall2)
        (by unfold activeMirBody; rw [hrev_post]; exact hlinks_post)
        hdisj_post htb_d hvalid_d hcid_pos_d hcid_act_d hcid_bor_d
        (hbt_d.of_pushFrame rfl)

/-- **Divergence (`step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence`)**:
When an `unsafe fn() -> T` (`fnEntry.fnSig = some (.fnPtr [] callerOut .unsafe_ callerAbi)`)
is transmuted to a safe `fn() -> T` local (`fnDecl.ty.kind = .fnPtr [] callerOut .safe callerAbi`)
and called indirectly (`TerminatorKind.call (.move ⟨fnIdx, .nil⟩) [] ⟨destIdx, .nil⟩ (some targetBb) unwind`),
with compatible runtime calling convention and layout:
1. **Stage-1 `Trusted`** (`fnEntryCompatibleWithCallSite` at `Terminators.lean:244-280`,
   `safetyCompatible .unsafe_ .safe = false` at `Terminators.lean:222`) faults with
   `stepMirFn rootBody s = .fail .ub`;
2. **Canonical `lean-miri`** (`Call.initStackFrame` at `Call.lean:254-264`,
   reflected by `annealEvalNonConstCallLM4_1`) checks only runtime `FnAbi`
   convention and argument/return layouts—ignoring HIR/MIR `Safety`—and steps
   normally (`.ok true`), pushing `calleeBody` onto `m'.stack.frames`. -/
theorem step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {fnIdx destIdx : Local} {fnDecl destDecl : LocalDecl}
    {ptrVal : ProvenancePtr} {mAllocId : Miri.Memory.AllocId}
    {mTag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {callerOut : RigidTy} {callerAbi : CallConv}
    {bb : BasicBlockData} {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {fnEntry : FnPtrEntry} {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl} {calleeBb0 : BasicBlockData}
    (hpre : IndirectFnPtrMovePre rootBody s m topFrame restMfs fnIdx fnDecl ptrVal mAllocId mTag baseAddr)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call (.move ⟨fnIdx, .nil⟩) .nil ⟨destIdx, .nil⟩ (some targetBb) unwind)
    (hfn_ty : fnDecl.ty.kind = .fnPtr .nil callerOut .safe callerAbi)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hlookup_some : lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry)
    (htargs_nil : fnEntry.typeArgs = [])
    (hsig : fnEntry.fnSig = some (.fnPtr .nil callerOut .unsafe_ callerAbi))
    (habi_m : annealFnPtrAbiCompatible fnEntry .nil callerOut callerAbi 0 = true)
    (hcallee : findCallee? s.memory.callees fnEntry.defPath = some calleeBody)
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hcal_abi : annealCalleeAbiCompatible fnEntry calleeBody 0 = true)
    (hdest_deinit : ∀ tf, tf = deinitFrameLocal
      (cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
        (translateTy fnDecl.ty (activeMirBody rootBody s).layouts))
      fnIdx (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf) →
      CallerDestSlotWf m.machine tf destIdx destDecl ∧
      IsLiveFrameLocal tf destIdx) :
    stepMirFn rootBody s = .fail .ub ∧
    ∃ m' calleeMf,
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m', .ok true) ∧
      m'.stack.frames.size = m.stack.frames.size + 1 ∧
      m'.stack.frames.back? = some calleeMf ∧
      calleeMf.body = translateBody calleeBody ∧
      calleeMf.location = .mir ⟨0, 0⟩ := by
  obtain ⟨cachedLay, hmls_f, hcache_f⟩ := hpre.fn_mls
  have hdeinit_state := hpre.deinit_rel
  dsimp only at hdeinit_state
  let tf₀ := cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
    (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
  let tfDeinit := deinitFrameLocal tf₀ fnIdx
    (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf)
  let sDeinit : MachineState :=
    { s with frame := { s.frame with locals := s.frame.locals.set fnIdx .uninit } }
  let mDeinit : AnnealStepState :=
    { m with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ }
  rcases hdeinit_state with
    ⟨tf_d, hback_d, _, _, _, hlinks_d, _, _, _, _, _, _, _⟩
  have htf_d_eq : tf_d = tfDeinit :=
    Option.some.inj (hback_d.symm.trans (array_back?_append_singleton restMfs.reverse tfDeinit))
  subst htf_d_eq
  have hforall_d := hlinks_d.toForall2
  have hrev_d : mDeinit.stack.frames.toList.reverse = tfDeinit :: restMfs :=
    array_toList_reverse_append_singleton restMfs tfDeinit
  rw [hrev_d] at hforall_d
  have hfr_d : FrameRel (activeMirBody rootBody s) m.machine sDeinit.frame tfDeinit := by
    cases hforall_d with | cons hfr _ => exact hfr
  have hbody_top : topFrame.body = translateBody (activeMirBody rootBody s) := hfr_d.body_eq
  have hloc_top : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfr_d.location_eq
  have hback_top : m.stack.frames.back? = some topFrame := by
    rw [hpre.frames_eq]; exact array_back?_append_singleton restMfs.reverse topFrame
  have hop_ty :
      operandTy (activeMirBody rootBody s).localDecls
        (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
      some fnDecl.ty := by
    simp [operandTy, placeTy, hpre.fn_decl]
  have habi_a_false : fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty) = false := by
    unfold fnEntryCompatibleWithCallSite
    rw [hsig]
    cases hty_mk : fnDecl.ty with
    | mk k lidx =>
      rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty
      simp [safetyCompatible]
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
    unfold evalTerminator
    rw [hterm]
    unfold resolveCallTarget
    dsimp only [extractCalleeDefPath?, bodyLocalDeclsOf, length, List.length]
    have hmove_a :
        evalOperand s.frame.locals (.move ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
          (activeMirBody rootBody s).layouts s.memory.callerLocals =
        .ok (.ptr ptrVal 8) (s.frame.locals.set fnIdx .uninit) := by
      unfold evalOperand; dsimp only []; rw [hpre.fn_slot]; dsimp only []
      rw [set?_eq_some_set hpre.fn_lt_af .uninit]
    rw [hmove_a]
    dsimp only []
    rw [hoff0, hpre.not_borrow]
    dsimp only [Nat.beq, Bool.and]
    rw [hlookup_some, hop_ty]; dsimp only []; rw [habi_a_false]
  · obtain ⟨hdest_wf_d, hdest_live_d⟩ := hdest_deinit tfDeinit rfl
    have hpush_sim :=
      step_terminator_call_args_simulation_ok
        (callerBody := activeMirBody rootBody s) (calleeBody := calleeBody)
        (callerAf := sDeinit.frame) (topFrame := tfDeinit) (restMfs := restMfs)
        (destIdx := destIdx) (destDecl := destDecl)
        (targetOpt := some targetBb) (unwind := unwind) (m := mDeinit)
        hcallee_decls hcallee_bb0 hdest_decl [] sDeinit.frame.locals tfDeinit []
        rfl rfl rfl (fun _ _ lay h => ⟨⟨lay, h⟩, rfl⟩)
        hdest_wf_d hdest_live_d id hfr_d (.nil restDecls)
    generalize ha_ops_eq : OperandsEvalResult.ok ([] : List Value) sDeinit.frame.locals = aOps at hpush_sim
    generalize hm_ops_eq :
      ({ mDeinit with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ },
       Except.ok ([] : List (Miri.Interpreter.RvalueImmTy AnnealProv))) = mOps at hpush_sim
    cases hpush_sim with
    | ub _ _ => cases ha_ops_eq
    | ok argVals' locals'' tfDeinit' calleeMf argImms' _ _ _ _ _ _
        hres_dest _ _ _ hfr_callee _ hpush_spec =>
      cases ha_ops_eq
      have hm_imms : argImms' = [] := by
        injection hm_ops_eq with _ h; injection h with h2; exact h2.symm
      subst hm_imms
      have htf_eq : tfDeinit' = tfDeinit := by
        injection hm_ops_eq with hst _
        have hl := congrArg (fun st => st.stack.frames.toList) hst
        simpa using hl.symm
      subst htf_eq
      obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (.Move ⟨fnIdx, #[]⟩) #[]
              (translatePlace ⟨destIdx, .nil⟩) (some targetBb) (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator; rw [hterm]; rfl
      let mptr : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes),
         .concrete mAllocId mTag⟩
      have hmove_m :
          annealEvalOperand (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
            (.Move ⟨fnIdx, #[]⟩) none m =
          .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
               translateTy fnDecl.ty (activeMirBody rootBody s).layouts⟩ mDeinit :=
        annealEvalOperand_move_live_multiFrame hpre.frames_eq hpre.fn_lt_mf hpre.fn_decl hmls_f hcache_f
      have hres_ptr :
          annealResolvePtr mDeinit.machine mptr.withOptionalProvenance 0 =
            .ok ⟨mAllocId,
                 Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr),
                 mTag⟩ := by
        unfold annealResolvePtr
        dsimp only [mDeinit, mptr, Miri.Memory.Pointer.withOptionalProvenance, Miri.ABI.Size.ofBytes]
        rw [hpre.baseAddr_lookup]
        dsimp only []
        exact ite_eq_left_iff.mpr fun h => absurd hpre.offset_no_wrap.1 h
      have hsz_eq0 :
          (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
            Miri.ABI.Size.ZERO) = false := by
        rw [bne_eq_false_iff_eq]
        have h0 : baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr = 0 := by
          rw [hoff0]; simp
        rw [h0]; rfl
      have hcall_m :
          annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
            (translateTerminator bb.terminator) m s.memory.fnPtrs =
          ({ stack := ⟨⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩⟩
             machine := m.machine }, .ok ()) := by
        unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
        rw [hback_top]; dsimp only []
        rw [hloc_top]; dsimp only []
        rw [hbb]; dsimp only []
        rw [hterm, htk]
        unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
        dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
        rw [EStateM.bind_eq_ok hmove_m]
        dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        have hsome_fn :
            operandTy (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
            some { kind := .fnPtr .nil callerOut .safe callerAbi,
                   layoutIdx := fnDecl.ty.layoutIdx } := by
          rw [hop_ty]
          cases hty_mk : fnDecl.ty with
          | mk k lidx => rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
        rw [hsome_fn]
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]; dsimp only [List.length]
        rw [hsz_eq0, hpre.allocId_eq, hlookup_some]; dsimp only []
        rw [htargs_nil]
        simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty, Bool.not_true, habi_m]
        rw [hcallee]; dsimp only []
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, hcal_abi]
        unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
        dsimp only [mDeinit]
        rw [array_back?_append_singleton restMfs.reverse tfDeinit]; dsimp only []
        have hsize_after :
            (⟨restMfs.reverse ++ [tfDeinit]⟩ :
              Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
            restMfs.length := by simp
        change resolveCallerDestinationPlace _ _ _ { localId := destIdx, projection := #[] } = _ at hres_dest
        rw [hsize_after, hres_dest]; dsimp only []
        dsimp only [mDeinit] at hraw_ok hraw_state hdone_eq
        rw [hraw_ok]; dsimp only []
        unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
        rw [hraw_curr]; dsimp only []
        rw [hraw_state, hdone_eq]
      let m' : AnnealStepState :=
        { stack := ⟨⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩⟩
          machine := m.machine }
      refine ⟨m', calleeMf, ?_, ?_,
        array_back?_append_singleton (tfDeinit :: restMfs).reverse calleeMf,
        hfr_callee.body_eq, hfr_callee.location_eq⟩
      · unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback_top hbody_top hloc_top hbb hstmt_none]
        unfold Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksLM4_1
        rw [htk]
        dsimp only [Id.run]
        rw [hcall_m]
        simp [Option.isSome_some, hpre.frames_eq, m', pure, Pure.pure, Except.map]
      · rw [hpre.frames_eq]; simp [m']

/-- **Divergence (`step_terminator_call_indirect_layoutCompat_fnPtr_divergence`)**:
Generalizes `step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence` to
any indirect function-pointer call
`TerminatorKind.call (.move ⟨fnIdx, .nil⟩) [] ⟨destIdx, .nil⟩ (some targetBb) unwind`
where Stage-1's syntactic signature check `fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty)`
returns `false` (for example, calling a `fn() -> u64` entry through a transmuted
`fn() -> usize` pointer on a 64-bit target where `rigidTyEq (.uint .usize) (.uint .u64) = false`,
or calling an `unsafe fn()` through a `fn()`), while canonical `lean-miri`'s
layout-based `annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0`
(`LayoutCompat.checkArgumentCompat` at `LayoutCompat.lean:208-238`) returns `true`:
1. **Stage-1 `Trusted`** faults with `stepMirFn rootBody s = .fail .ub`;
2. **Canonical `lean-miri`** (`annealStepHooksForState rootBody s`) succeeds
   (`.ok true`) and pushes `calleeBody` onto `m'.stack.frames`. -/
theorem step_terminator_call_indirect_layoutCompat_fnPtr_divergence
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {fnIdx destIdx : Local} {fnDecl destDecl : LocalDecl}
    {ptrVal : ProvenancePtr} {mAllocId : Miri.Memory.AllocId}
    {mTag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {callerInputs : List RigidTy} {callerOut : RigidTy}
    {callerSafety : Safety} {callerAbi : CallConv}
    {bb : BasicBlockData} {targetBb : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {fnEntry : FnPtrEntry} {calleeBody : CapturedMir}
    {retDecl : LocalDecl} {restDecls : List LocalDecl} {calleeBb0 : BasicBlockData}
    (hpre : IndirectFnPtrMovePre rootBody s m topFrame restMfs fnIdx fnDecl ptrVal mAllocId mTag baseAddr)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call (.move ⟨fnIdx, .nil⟩) .nil ⟨destIdx, .nil⟩ (some targetBb) unwind)
    (hfn_ty : fnDecl.ty.kind = .fnPtr callerInputs callerOut callerSafety callerAbi)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hlookup_some : lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some fnEntry)
    (htargs_nil : fnEntry.typeArgs = [])
    (habi_a_false : fnEntryCompatibleWithCallSite fnEntry 0 (some fnDecl.ty) = false)
    (habi_m : annealFnPtrAbiCompatible fnEntry callerInputs callerOut callerAbi 0 = true)
    (hcallee : findCallee? s.memory.callees fnEntry.defPath = some calleeBody)
    (hcallee_decls : calleeBody.localDecls = retDecl :: restDecls)
    (hcallee_bb0 : get? calleeBody.basicBlocks 0 = some calleeBb0)
    (hcal_abi : annealCalleeAbiCompatible fnEntry calleeBody 0 = true)
    (hdest_deinit : ∀ tf, tf = deinitFrameLocal
      (cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
        (translateTy fnDecl.ty (activeMirBody rootBody s).layouts))
      fnIdx (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf) →
      CallerDestSlotWf m.machine tf destIdx destDecl ∧
      IsLiveFrameLocal tf destIdx) :
    stepMirFn rootBody s = .fail .ub ∧
    ∃ m' calleeMf,
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m', .ok true) ∧
      m'.stack.frames.size = m.stack.frames.size + 1 ∧
      m'.stack.frames.back? = some calleeMf ∧
      calleeMf.body = translateBody calleeBody ∧
      calleeMf.location = .mir ⟨0, 0⟩ := by
  obtain ⟨cachedLay, hmls_f, hcache_f⟩ := hpre.fn_mls
  have hdeinit_state := hpre.deinit_rel
  dsimp only at hdeinit_state
  let tf₀ := cacheFrameLocalLayout topFrame fnIdx hpre.fn_lt_mf
    (translateTy fnDecl.ty (activeMirBody rootBody s).layouts)
  let tfDeinit := deinitFrameLocal tf₀ fnIdx
    (by rw [cacheFrameLocalLayout_size]; exact hpre.fn_lt_mf)
  let sDeinit : MachineState :=
    { s with frame := { s.frame with locals := s.frame.locals.set fnIdx .uninit } }
  let mDeinit : AnnealStepState :=
    { m with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ }
  rcases hdeinit_state with
    ⟨tf_d, hback_d, _, _, _, hlinks_d, _, _, _, _, _, _, _⟩
  have htf_d_eq : tf_d = tfDeinit :=
    Option.some.inj (hback_d.symm.trans (array_back?_append_singleton restMfs.reverse tfDeinit))
  subst htf_d_eq
  have hforall_d := hlinks_d.toForall2
  have hrev_d : mDeinit.stack.frames.toList.reverse = tfDeinit :: restMfs :=
    array_toList_reverse_append_singleton restMfs tfDeinit
  rw [hrev_d] at hforall_d
  have hfr_d : FrameRel (activeMirBody rootBody s) m.machine sDeinit.frame tfDeinit := by
    cases hforall_d with | cons hfr _ => exact hfr
  have hbody_top : topFrame.body = translateBody (activeMirBody rootBody s) := hfr_d.body_eq
  have hloc_top : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfr_d.location_eq
  have hback_top : m.stack.frames.back? = some topFrame := by
    rw [hpre.frames_eq]; exact array_back?_append_singleton restMfs.reverse topFrame
  have hop_ty :
      operandTy (activeMirBody rootBody s).localDecls
        (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
      some fnDecl.ty := by
    simp [operandTy, placeTy, hpre.fn_decl]
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
    unfold evalTerminator
    rw [hterm]
    unfold resolveCallTarget
    dsimp only [extractCalleeDefPath?, bodyLocalDeclsOf, length, List.length]
    have hmove_a :
        evalOperand s.frame.locals (.move ⟨fnIdx, .nil⟩) s.memory.borrows s.memory.globals
          (activeMirBody rootBody s).layouts s.memory.callerLocals =
        .ok (.ptr ptrVal 8) (s.frame.locals.set fnIdx .uninit) := by
      unfold evalOperand; dsimp only []; rw [hpre.fn_slot]; dsimp only []
      rw [set?_eq_some_set hpre.fn_lt_af .uninit]
    rw [hmove_a]
    dsimp only []
    rw [hoff0, hpre.not_borrow]
    dsimp only [Nat.beq, Bool.and]
    rw [hlookup_some, hop_ty]; dsimp only []; rw [habi_a_false]
  · obtain ⟨hdest_wf_d, hdest_live_d⟩ := hdest_deinit tfDeinit rfl
    have hpush_sim :=
      step_terminator_call_args_simulation_ok
        (callerBody := activeMirBody rootBody s) (calleeBody := calleeBody)
        (callerAf := sDeinit.frame) (topFrame := tfDeinit) (restMfs := restMfs)
        (destIdx := destIdx) (destDecl := destDecl)
        (targetOpt := some targetBb) (unwind := unwind) (m := mDeinit)
        hcallee_decls hcallee_bb0 hdest_decl [] sDeinit.frame.locals tfDeinit []
        rfl rfl rfl (fun _ _ lay h => ⟨⟨lay, h⟩, rfl⟩)
        hdest_wf_d hdest_live_d id hfr_d (.nil restDecls)
    generalize ha_ops_eq : OperandsEvalResult.ok ([] : List Value) sDeinit.frame.locals = aOps at hpush_sim
    generalize hm_ops_eq :
      ({ mDeinit with stack := ⟨⟨restMfs.reverse ++ [tfDeinit]⟩⟩ },
       Except.ok ([] : List (Miri.Interpreter.RvalueImmTy AnnealProv))) = mOps at hpush_sim
    cases hpush_sim with
    | ub _ _ => cases ha_ops_eq
    | ok argVals' locals'' tfDeinit' calleeMf argImms' _ _ _ _ _ _
        hres_dest _ _ _ hfr_callee _ hpush_spec =>
      cases ha_ops_eq
      have hm_imms : argImms' = [] := by
        injection hm_ops_eq with _ h; injection h with h2; exact h2.symm
      subst hm_imms
      have htf_eq : tfDeinit' = tfDeinit := by
        injection hm_ops_eq with hst _
        have hl := congrArg (fun st => st.stack.frames.toList) hst
        simpa using hl.symm
      subst htf_eq
      obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
      have htk :
          (translateTerminator bb.terminator).kind =
            .Call (.Move ⟨fnIdx, #[]⟩) #[]
              (translatePlace ⟨destIdx, .nil⟩) (some targetBb) (translateUnwindAction unwind)
              .Normal defaultSpanRef := by
        unfold translateTerminator; rw [hterm]; rfl
      let mptr : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes),
         .concrete mAllocId mTag⟩
      have hmove_m :
          annealEvalOperand (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts
            (.Move ⟨fnIdx, #[]⟩) none m =
          .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
               translateTy fnDecl.ty (activeMirBody rootBody s).layouts⟩ mDeinit :=
        annealEvalOperand_move_live_multiFrame hpre.frames_eq hpre.fn_lt_mf hpre.fn_decl hmls_f hcache_f
      have hres_ptr :
          annealResolvePtr mDeinit.machine mptr.withOptionalProvenance 0 =
            .ok ⟨mAllocId,
                 Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr),
                 mTag⟩ := by
        unfold annealResolvePtr
        dsimp only [mDeinit, mptr, Miri.Memory.Pointer.withOptionalProvenance, Miri.ABI.Size.ofBytes]
        rw [hpre.baseAddr_lookup]
        dsimp only []
        exact ite_eq_left_iff.mpr fun h => absurd hpre.offset_no_wrap.1 h
      have hsz_eq0 :
          (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) !=
            Miri.ABI.Size.ZERO) = false := by
        rw [bne_eq_false_iff_eq]
        have h0 : baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr = 0 := by
          rw [hoff0]; simp
        rw [h0]; rfl
      have hcall_m :
          annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
            (translateTerminator bb.terminator) m s.memory.fnPtrs =
          ({ stack := ⟨⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩⟩
             machine := m.machine }, .ok ()) := by
        unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
        rw [hback_top]; dsimp only []
        rw [hloc_top]; dsimp only []
        rw [hbb]; dsimp only []
        rw [hterm, htk]
        unfold annealEvalNonConstCallLM4_1 Miri.Interpreter.runRvalue
        dsimp only [extractCalleeDefPath?, translateOperand, translatePlace, List.map]
        rw [EStateM.bind_eq_ok hmove_m]
        dsimp only [annealEvalCallArgsLM4_1, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        have hsome_fn :
            operandTy (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts (.move ⟨fnIdx, .nil⟩) =
            some { kind := .fnPtr callerInputs callerOut callerSafety callerAbi,
                   layoutIdx := fnDecl.ty.layoutIdx } := by
          rw [hop_ty]
          cases hty_mk : fnDecl.ty with
          | mk k lidx => rw [hty_mk] at hfn_ty; dsimp only at hfn_ty; subst hfn_ty; rfl
        rw [hsome_fn]
        dsimp only [Miri.Interpreter.runRvalue, annealReadImmediate,
          Miri.Interpreter.Immediate.toScalar, EStateM.pure, pure]
        have hinto :
            mptr.withOptionalProvenance.intoPointerOrAddr =
              .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl
        rw [scalar_fromPointer_toPointer_eq mptr]
        dsimp only []
        rw [hinto]
        dsimp only []
        rw [hres_ptr]; dsimp only [List.length]
        rw [hsz_eq0, hpre.allocId_eq, hlookup_some]; dsimp only []
        rw [htargs_nil]
        simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty, Bool.not_true, habi_m]
        rw [hcallee]; dsimp only []
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, hcal_abi]
        unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
        dsimp only [mDeinit]
        rw [array_back?_append_singleton restMfs.reverse tfDeinit]; dsimp only []
        have hsize_after :
            (⟨restMfs.reverse ++ [tfDeinit]⟩ :
              Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
            restMfs.length := by simp
        change resolveCallerDestinationPlace _ _ _ { localId := destIdx, projection := #[] } = _ at hres_dest
        rw [hsize_after, hres_dest]; dsimp only []
        dsimp only [mDeinit] at hraw_ok hraw_state hdone_eq
        rw [hraw_ok]; dsimp only []
        unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
        rw [hraw_curr]; dsimp only []
        rw [hraw_state, hdone_eq]
      let m' : AnnealStepState :=
        { stack := ⟨⟨(tfDeinit :: restMfs).reverse ++ [calleeMf]⟩⟩
          machine := m.machine }
      refine ⟨m', calleeMf, ?_, ?_,
        array_back?_append_singleton (tfDeinit :: restMfs).reverse calleeMf,
        hfr_callee.body_eq, hfr_callee.location_eq⟩
      · unfold annealStepHooksForState
        rw [miri_step_at_terminator_multiFrame hback_top hbody_top hloc_top hbb hstmt_none]
        unfold Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksLM4_1
        rw [htk]
        dsimp only [Id.run]
        rw [hcall_m]
        simp [Option.isSome_some, hpre.frames_eq, m', pure, Pure.pure, Except.map]
      · rw [hpre.frames_eq]; simp [m']

/-- **Theorem 8d (`step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`)**:
Starting from any `MultiFrameStateRel rootBody s m` state at `(s.frame.blockIdx, s.frame.stmtIdx)`
(where `s.memory.borrows = .nil` and `fnIdx` is an immediate local), executing
`StatementKind.assign ⟨fnIdx, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer") (.constant { ty := { kind := .fnDef defPath .nil, layoutIdx := 0 }, val := .zeroSized }) fnDecl.ty)`
steps both Stage-1 `stepMirFn rootBody s = .step s₁` and `lean-miri`
`Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m₁, .ok true)`
such that `(s₁, m₁)` satisfies `IndirectFnPtrMovePre` at `(s.frame.blockIdx, s.frame.stmtIdx + 1)`
with `lookupFnPtr s₁.memory.fnPtrs allocId = some { allocId := allocId, defPath := defPath, typeArgs := .nil, fnSig := some fnDecl.ty.kind }`.

Scope of the hypotheses:
* `hfn_ty` (`.safe` target), `hnot_intr`, `hcheck_sig`, and `htraits_nil` are
  **Stage-1-only** preconditions of `evalReifyFnPointer` (`Places.lean:13784-13926`);
  canonical `lean-miri` (`Cast.lean:336-341`, `annealReifyFnPointerAlloc`) performs no
  reify-time signature, safety, or calling-convention validation, so its step does
  not depend on them (they hold for every rustc-typed `ReifyFnPointer`).
* `hfind_none` / `halloc_id` / `hmAlloc_eq` cover a first reification of `defPath`
  at this type, with both machines naming the function allocation `allocId`.
* `hbase_lookup` covers the case where `m.machine` already assigns `mAllocId` an
  address (the address-reuse branch of `annealReifyFnPointerAlloc`); the
  fresh-address branch, which records `annealStackBaseAddr mAllocId` in
  `m.machine.addresses`, is not covered here. -/
theorem step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {fnIdx : Local} {fnDecl : LocalDecl}
    {defPath : DefPath} {span : String}
    {callerInputs : List RigidTy} {callerOut : RigidTy} {callerAbi : CallConv}
    {allocId : Nat} {mAllocId : Miri.Memory.AllocId} {baseAddr : UInt64}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt :
      get? bb.statements s.frame.stmtIdx =
        some
          { kind :=
              .assign ⟨fnIdx, .nil⟩
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant { ty := { kind := .fnDef defPath .nil, layoutIdx := 0 }, val := .zeroSized })
                  fnDecl.ty)
            span := span })
    (hfn_decl : get? (activeMirBody rootBody s).localDecls fnIdx = some fnDecl)
    (hfn_ty : fnDecl.ty.kind = .fnPtr callerInputs callerOut .safe callerAbi)
    (hnot_intr : callConvEq callerAbi .rustIntrinsic = false)
    (hcheck_sig : checkCalleeSig s.memory.callees defPath callerInputs callerOut callerAbi .nil .nil = true)
    (htraits_nil : s.memory.traitImpls = .nil)
    (hbor_nil : s.memory.borrows = .nil)
    (hfn_imm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf fnIdx)
    (hfn_live : get? s.frame.locals fnIdx ≠ some .dead)
    (hfind_none : findFnPtrEntry? s.memory.fnPtrs defPath .nil (some fnDecl.ty.kind) = none)
    (halloc_id : nextFnPtrAllocId s.memory.fnPtrs = allocId)
    (hmAlloc_eq : mAllocId.value.toNat = allocId)
    (hbase_lookup : m.machine.lookupBaseAddr mAllocId = some baseAddr) :
    ∃ s₁ m₁ topFrame₁ restMfs,
      stepMirFn rootBody s = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m₁, .ok true) ∧
      s₁.frame.blockIdx = s.frame.blockIdx ∧
      s₁.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      s₁.memory.callees = s.memory.callees ∧
      activeMirBody rootBody s₁ = activeMirBody rootBody s ∧
      lookupFnPtr s₁.memory.fnPtrs allocId =
        some
          { allocId := allocId
            defPath := defPath
            typeArgs := .nil
            fnSig := some fnDecl.ty.kind } ∧
      (∀ j,
        (∀ tf, m.stack.frames.back? = some tf →
          IsImmediateFrameLocal tf j ∧ IsLiveFrameLocal tf j) →
        IsImmediateFrameLocal topFrame₁ j ∧ IsLiveFrameLocal topFrame₁ j) ∧
      IndirectFnPtrMovePre rootBody s₁ m₁ topFrame₁ restMfs fnIdx fnDecl
        { allocId := allocId, offsetBytes := 0 }
        mAllocId Miri.Memory.BorTag.one baseAddr := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      obtain ⟨slot_f, mls_f, hlt_af, hlt_mf, hslot_f, hmls_f, hmls_eq_f, hloc_f⟩ :=
        hframe.lookup_local hfn_decl
      have himm_f := hfn_imm topFrame₀ hback mls_f hmls_f
      have hslot_ne_dead : slot_f ≠ .dead := by
        intro hd; subst hd; exact hfn_live hslot_f
      have hmls_imm : ∃ imm₀, mls_f.value = .live (.immediate imm₀) := by
        cases hloc_f with
        | dead _ _ => exact False.elim (hslot_ne_dead rfl)
        | indirect _ mp _ _ _ _ => exact False.elim (himm_f mp rfl)
        | immediate _ imm₀ _ _ _ => exact ⟨imm₀, rfl⟩
      obtain ⟨imm₀, hmls_val⟩ := hmls_imm
      let fnEntry : FnPtrEntry :=
        { allocId := allocId
          defPath := defPath
          typeArgs := .nil
          fnSig := some fnDecl.ty.kind }
      let mem₁ : Memory := { s.memory with fnPtrs := fnEntry :: s.memory.fnPtrs }
      let ptrVal : ProvenancePtr := { allocId := allocId, offsetBytes := 0 }
      let s₁ : MachineState :=
        { frame :=
            { s.frame with
              stmtIdx := s.frame.stmtIdx + 1
              locals := s.frame.locals.set fnIdx (.init (.ptr ptrVal 8)) }
          memory := mem₁ }
      have hreify_coerc : isReifyFnPointerCoercion "ReifyFnPointer" = true := by decide
      have hnot_uns_coerc : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
      have hsafe_coerc : reifyCoercionSafetyCompatible "ReifyFnPointer" .safe = true := by decide
      have hextr_coerc :
          extractReifyCoercionTarget? "ReifyFnPointer"
            (some { kind := .fnDef defPath .nil, layoutIdx := 0 }) =
            some (defPath, .nil) := by
        have hc : isClosureFnPointerCoercion "ReifyFnPointer" = false := by decide
        unfold extractReifyCoercionTarget?
        rw [hc]
        rfl
      have ha_step : stepMirFn rootBody s = .step s₁ := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue evalReifyFnPointer
        dsimp only []
        rw [hreify_coerc, hnot_uns_coerc]
        dsimp only [evalOperand, evalConstValue, operandTy]
        rw [hfn_ty]
        dsimp only []
        rw [hnot_intr, hsafe_coerc, hextr_coerc]
        dsimp only [Bool.not, Bool.and, internFnPtr]
        rw [htraits_nil, hcheck_sig]
        dsimp only []
        rw [← hfn_ty, hfind_none, halloc_id]
        dsimp only []
        rw [hslot_f]
        cases hslot_cases : slot_f with
        | dead => exact False.elim (hslot_ne_dead hslot_cases)
        | uninit | init _ =>
          dsimp only []
          rw [set?_eq_some_set hlt_af (.init (.ptr ptrVal 8)), hbor_nil]
          rcases hprot : s.memory.activeProtectors with _ | ⟨ph, pt⟩ <;>
            simp [advanceStmt, s₁, mem₁, fnEntry, htraits_nil, hbor_nil, hprot,
              invalidateConflictingBorrows, hasProtectedWriteConflict]
      let lay_fn := translateTy fnDecl.ty (activeMirBody rootBody s).layouts
      let msc_ptr :=
        Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
           (Miri.Memory.Provenance.concrete mAllocId Miri.Memory.BorTag.one : AnnealProv)⟩
      let tf₀ := cacheFrameLocalLayout topFrame₀ fnIdx hlt_mf lay_fn
      let topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { topFrame₀ with
          locals :=
            topFrame₀.locals.set fnIdx
              ⟨.live (.immediate (.scalar msc_ptr)), some lay_fn⟩
              hlt_mf
          location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
      let m₁ : AnnealStepState :=
        { m with stack := ⟨⟨restMfs.reverse ++ [topFrame₁]⟩⟩ }
      have hu64 : UInt64.ofNat allocId = mAllocId.value := by
        rw [← hmAlloc_eq, UInt64.ofNat_toNat]
      have hnz : UInt64.ofNat allocId ≠ 0 := by
        rw [hu64]; exact mAllocId.nonzero
      have hma_eq : (⟨UInt64.ofNat allocId, hnz⟩ : Miri.Memory.AllocId) = mAllocId := by
        cases mAllocId; simp [hu64]
      have hty_enc : encodeTyId fnDecl.ty = 42 := by
        unfold encodeTyId; rw [hfn_ty]
      have hlay_ty : lay_fn.ty = 42 := hty_enc
      have htr_coerc : translatePointerCoercion "ReifyFnPointer" = .ReifyFnPointer .Safe := by
        decide
      have hcache_f :
          ∀ l, (topFrame₀.locals[fnIdx]'hlt_mf).layout = some l →
            l = translateTy fnDecl.ty (activeMirBody rootBody s).layouts := by
        rw [hmls_eq_f]; exact hloc_f.layout_eq
      have hres_f :=
        annealResolveAndCacheLocalLayout_multiFrame_eq (known := none) harr hlt_mf hfn_decl hcache_f
      have heval_pl :
          annealEvalPlace (activeMirBody rootBody s).localDecls
            (activeMirBody rootBody s).layouts ⟨fnIdx, #[]⟩ m =
          .ok ⟨.local restMfs.length fnIdx none topFrame₀.localsIdentity, lay_fn⟩
            { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } := by
        with_unfolding_all
          unfold annealEvalPlace
          simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
            Pure.pure, EStateM.pure,
            stack_currentFrame?_append_singleton m.stack restMfs topFrame₀ harr,
            Option.isNone_some, harr, array_size_append_singleton,
            List.length_reverse, Nat.add_sub_cancel, hres_f]
          rfl
      have heval_stmt :
          Miri.Interpreter.Step.evalStatement (annealStepHooksForState rootBody s) ()
            (translateStmt
              { kind :=
                  .assign ⟨fnIdx, .nil⟩
                    (.cast (.pointerCoercion "ReifyFnPointer")
                      (.constant { ty := { kind := .fnDef defPath .nil, layoutIdx := 0 }, val := .zeroSized })
                      fnDecl.ty)
                span := span }) m =
          ({ m with
             stack := ⟨⟨restMfs.reverse ++
               [{ topFrame₀ with
                  locals := topFrame₀.locals.set fnIdx
                    ⟨.live (.immediate (.scalar msc_ptr)), some lay_fn⟩ hlt_mf }]⟩⟩ },
           .ok ()) := by
        unfold annealStepHooksForState annealStepHooksLM4_1
          Miri.Interpreter.Step.evalStatement
        dsimp only [translateStmt, translateStmtKind, translatePlace, translateRvalue,
          translateCastKind, translateOperand,
          translateConstOperand, translateConstValue, List.map, List.toArray,
          Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace,
          annealRvalueHooksLM4_1, annealRvalueHooks]
        rw [htr_coerc, hty_enc]
        dsimp only [encodeTyId]
        rw [EStateM.bind_eq_ok heval_pl]
        have heval_op :
            annealEvalOperand (activeMirBody rootBody s).localDecls
              (activeMirBody rootBody s).layouts
              (.Constant { span := defaultSpanRef, userType := none, value := .Val .ZeroSized 51 })
              none { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } =
            .ok ⟨.immediate .uninit, { ty := 51, layout := zstLayoutData }⟩
              { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } := by
          with_unfolding_all
            unfold annealEvalOperand evalMirConstImmediate Miri.Interpreter.Stack.currentFrame?
            simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
              Pure.pure, EStateM.pure, array_back?_append_singleton restMfs.reverse tf₀,
              Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
              layoutOfEncodedTyId]
            rfl
        have hreify_ok :
            annealReifyFnPointerAlloc (activeMirBody rootBody s) s.memory.fnPtrs
              { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } =
            .ok ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
                 some (.concrete mAllocId Miri.Memory.BorTag.one)⟩
              { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } := by
          with_unfolding_all
            unfold annealReifyFnPointerAlloc Miri.Interpreter.Stack.currentFrame?
            rw [array_back?_append_singleton restMfs.reverse tf₀]
            dsimp only [tf₀, cacheFrameLocalLayout]
            rw [hframe.location_eq]
            dsimp only []
            rw [hbb]
            dsimp only []
            rw [hstmt]
            dsimp only [operandTy]
            rw [hextr_coerc]
            dsimp only []
            rw [hfind_none, halloc_id]
            simp +zetaHave only [hma_eq, hbase_lookup]
            exact ite_eq_left_iff.mpr fun h => absurd hnz h
        have hwrite_ok :
            annealWriteImmediate (.scalar msc_ptr)
              ⟨.local restMfs.length fnIdx none topFrame₀.localsIdentity, lay_fn⟩
              { m with stack := ⟨⟨restMfs.reverse ++ [tf₀]⟩⟩ } =
            .ok ()
              { m with
                stack := ⟨⟨restMfs.reverse ++
                  [{ topFrame₀ with
                     locals := topFrame₀.locals.set fnIdx
                       ⟨.live (.immediate (.scalar msc_ptr)), some lay_fn⟩ hlt_mf }]⟩⟩ } := by
          have hsize₀ :
              (⟨restMfs.reverse ++ [tf₀]⟩ :
                Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size - 1 =
              restMfs.length := by simp
          have hlt_idx₀ :
              restMfs.length <
                (⟨restMfs.reverse ++ [tf₀]⟩ :
                  Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)).size := by
            simp
          have hlt_mf₀ : fnIdx < tf₀.locals.size := by
            dsimp only [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt_mf
          have hget_c := cacheFrameLocalLayout_getLocal topFrame₀ hlt_mf lay_fn
          rw [hmls_eq_f] at hget_c
          dsimp only [] at hget_c
          rw [hmls_val] at hget_c
          have hgop := frame_getLocalOperand_live tf₀ hget_c
          have hrep :=
            frame_replaceLocalValue_of_lt tf₀ fnIdx hlt_mf₀ (.live (.immediate (.scalar msc_ptr)))
          have hlay_tf₀ : (tf₀.locals[fnIdx]'hlt_mf₀).layout = some lay_fn := by
            simp [tf₀, cacheFrameLocalLayout]
          with_unfolding_all
            unfold annealWriteImmediate Miri.Interpreter.Stack.currentFrame?
            simp +zetaHave only [get, getThe, MonadStateOf.get, EStateM.get,
              set, MonadStateOf.set, EStateM.set, Bind.bind, EStateM.bind,
              Pure.pure, EStateM.pure,
              array_back?_append_singleton restMfs.reverse tf₀,
              hsize₀, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hgop, hrep, hlt_idx₀, ↓reduceDIte]
            rw [hlay_tf₀]
            congr 3
            apply Array.ext'
            simp [tf₀, cacheFrameLocalLayout]
        with_unfolding_all
          dsimp only [Miri.Interpreter.Cast.cast, annealCastHooksLM4_1, annealCastHooks]
          rw [hlay_ty]
          simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
            Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            heval_op, hreify_ok]
          rw [hwrite_ok]
      have hm_step :
          Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m₁, .ok true) := by
        unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?
        rw [hback]
        dsimp only []
        rw [hframe.location_eq, hframe.body_eq]
        dsimp only []
        rw [translateBody_basicBlocks_getElem?, hbb]
        dsimp only [Option.map]
        rw [translateBasicBlockData_statements_getElem?, hstmt]
        dsimp only [Option.map]
        rw [heval_stmt]
        have hsize_m : m.stack.frames.size - 1 = restMfs.length := by rw [harr]; simp
        simp +zetaHave only [hsize_m, array_size_append_singleton, List.length_reverse,
          Nat.add_sub_cancel, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          array_back?_append_singleton, hframe.location_eq,
          Nat.lt_succ_self, ↓reduceDIte, pure, Id.run]
        congr 1
        congr 1
        congr 1
        apply Array.ext'
        simp [topFrame₁]
      refine ⟨s₁, m₁, topFrame₁, restMfs, ha_step, hm_step, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · unfold lookupFnPtr
        simp [fnEntry]
      · intro j hj
        obtain ⟨himm_j, hlive_j⟩ := hj topFrame₀ hback
        refine ⟨?_, ?_⟩
        · intro mls hmls mp hmp
          dsimp only [topFrame₁] at hmls
          rw [Array.getElem?_set] at hmls
          by_cases hfj : fnIdx = j
          · simp only [hfj, ↓reduceIte, Option.some.injEq] at hmls
            rw [← hmls] at hmp; cases hmp
          · simp only [hfj, ↓reduceIte] at hmls
            exact himm_j mls hmls mp hmp
        · intro mls hmls hdead
          dsimp only [topFrame₁] at hmls
          rw [Array.getElem?_set] at hmls
          by_cases hfj : fnIdx = j
          · simp only [hfj, ↓reduceIte, Option.some.injEq] at hmls
            rw [← hmls] at hdead; cases hdead
          · simp only [hfj, ↓reduceIte] at hmls
            exact hlive_j mls hmls hdead
      · have hlt_af₁ : fnIdx < s₁.frame.locals.length := by
          dsimp only [s₁]; rw [List.length_set]; exact hlt_af
        have hlt_mf₁ : fnIdx < topFrame₁.locals.size := by
          dsimp only [topFrame₁]; rw [Array.size_set]; exact hlt_mf
        refine
          { frames_eq := rfl
            fn_lt_af := hlt_af₁
            fn_lt_mf := hlt_mf₁
            fn_decl := hfn_decl
            fn_slot := by
              dsimp only [s₁]
              rw [get?_eq_getElem?, List.getElem?_set_self hlt_af]
            fn_mls :=
              ⟨some lay_fn,
               by dsimp only [topFrame₁]; rw [Array.getElem_set_self],
               fun _ h => (Option.some.inj h).symm⟩
            allocId_eq := hmAlloc_eq
            baseAddr_lookup := hbase_lookup
            offset_no_wrap := ⟨by simp, by simp⟩
            not_borrow := by dsimp only [s₁, mem₁]; rw [hbor_nil]; rfl
            deinit_rel := ?_ }
        dsimp only []
        let tfDeinit :=
          deinitFrameLocal
            (cacheFrameLocalLayout topFrame₁ fnIdx hlt_mf₁
              (translateTy fnDecl.ty (activeMirBody rootBody s₁).layouts))
            fnIdx (by rw [cacheFrameLocalLayout_size]; exact hlt_mf₁)
        have htfDeinit_eq :
            tfDeinit =
              { topFrame₀ with
                locals :=
                  topFrame₀.locals.set fnIdx
                    ⟨.live (.immediate .uninit), some lay_fn⟩ hlt_mf
                location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
          dsimp only [tfDeinit, deinitFrameLocal, cacheFrameLocalLayout, topFrame₁, lay_fn,
            activeMirBody, s₁, mem₁]
          congr 1
          apply Array.ext'
          simp
        have hsDeinit_locals :
            s₁.frame.locals.set fnIdx .uninit = s.frame.locals.set fnIdx .uninit := by
          dsimp only [s₁]
          exact List.set_set (LocalSlot.init (.ptr ptrVal 8))
        have hlt_mf_c : fnIdx < tf₀.locals.size := by
          rw [cacheFrameLocalLayout_size]; exact hlt_mf
        have hget_tf₀ :
            (tf₀.locals[fnIdx]'hlt_mf_c).layout = some lay_fn := by
          simp [tf₀, cacheFrameLocalLayout]
        have htfDeinit_eq2 :
            tfDeinit =
              { deinitFrameLocal tf₀ fnIdx hlt_mf_c with
                location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
          rw [htfDeinit_eq]
          unfold deinitFrameLocal
          dsimp only []
          rw [hget_tf₀]
          dsimp only [tf₀, cacheFrameLocalLayout]
          congr 1
          apply Array.ext'
          simp
        have hnew_loc_c :
            LocalRel m.machine fnDecl (activeMirBody rootBody s).layouts .uninit
              { tf₀.locals[fnIdx]'hlt_mf_c with
                value := .live (.immediate .uninit) } := by
          have hlay_c : (tf₀.locals[fnIdx]'hlt_mf_c).layout = some lay_fn := by
            simp [tf₀, cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay_c]; intro l hl; exact (Option.some.inj hl).symm)
            (Or.inl ⟨rfl, rfl⟩)
        have hfr₀ := hframe.cache_local_layout hfn_decl hlt_mf
        have hfr₁ := hfr₀.update_local hfn_decl .uninit (.live (.immediate .uninit)) hnew_loc_c
        have hfr_deinit :
            FrameRel (activeMirBody rootBody s₁) m.machine
              { s₁.frame with locals := s₁.frame.locals.set fnIdx .uninit }
              tfDeinit := by
          rw [htfDeinit_eq2]
          refine ⟨hfr₁.body_eq, rfl, ?_, hfr₁.mf_locals_size, ?_⟩
          · dsimp only [s₁]; rw [hsDeinit_locals]; exact hfr₁.af_locals_len
          · intro i decl slot mls hdecl_i hslot_i hmls_i
            rw [hsDeinit_locals] at hslot_i
            exact hfr₁.locals_rel i decl slot mls hdecl_i hslot_i hmls_i
        have hlinks_deinit :
            CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s₁)
              { s₁.frame with locals := s₁.frame.locals.set fnIdx .uninit }
              s₁.memory.callStack s₁.memory.activeProtectors
              (tfDeinit :: restMfs) := by
          refine hlinks.update_top_frame
            (by rw [htfDeinit_eq]) (by rw [htfDeinit_eq]) (by rw [htfDeinit_eq])
            hfr_deinit ?_
          intro mp0 lay0 h0
          rw [htfDeinit_eq] at h0
          dsimp only [] at h0
          by_cases hfn0 : fnIdx = 0
          · subst hfn0
            rw [Array.getElem?_set_self] at h0
            cases h0
          · rw [Array.getElem?_set_ne _ hfn0] at h0
            refine ⟨⟨lay0, h0⟩, Or.inl ?_⟩
            dsimp only []
            rw [hsDeinit_locals, get?_eq_getElem?, get?_eq_getElem?, List.getElem?_set_ne hfn0]
        have hd_top₀ : MemoryAllocDisjoint topFrame₀ := by
          apply hdisj.intra_frame topFrame₀; rw [harr]; simp
        have hd_tfDeinit : MemoryAllocDisjoint tfDeinit := by
          apply MemoryAllocDisjoint.mono_immediate hd_top₀
          intro k
          rw [htfDeinit_eq]
          by_cases hk : fnIdx = k
          · subst hk
            right
            exact ⟨.uninit, some lay_fn, by dsimp only []; rw [Array.getElem?_set_self]⟩
          · left
            dsimp only []
            rw [Array.getElem?_set_ne _ hk]
        have hdisj_deinit : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [tfDeinit]⟩ := by
          rw [harr] at hdisj
          apply hdisj.replace_top hd_tfDeinit
          intro i mp lay hi
          rw [htfDeinit_eq] at hi
          dsimp only [] at hi
          by_cases hi_fn : fnIdx = i
          · subst hi_fn
            rw [Array.getElem?_set_self] at hi
            cases hi
          · rw [Array.getElem?_set_ne _ hi_fn] at hi
            exact ⟨lay, hi⟩
        exact .mk tfDeinit
          (array_back?_append_singleton restMfs.reverse tfDeinit)
          hcal_root hcal_nonroot
          (by
            unfold FrameStackRel annealFrameStackTopDown activeMirBody
            simp only [m₁, List.reverse_append, List.reverse_singleton,
              List.reverse_reverse, List.singleton_append]
            exact hlinks_deinit.toForall2)
          (by
            unfold activeMirBody
            simp only [m₁, List.reverse_append, List.reverse_singleton,
              List.reverse_reverse, List.singleton_append]
            exact hlinks_deinit)
          hdisj_deinit htb hvalid hcid_pos hcid_act hcid_bor hbt

/-- **Theorem 9a (`step_terminator_call_linked_panic_unwind_simulation`)**:
When `"core::panicking::panic"` IS linked in `s.memory.callees` as `panicBody`
(`panicBody.basicBlocks = [{ statements := [], terminator := mkTerm .unwindResume, isCleanup := true }]`,
`panicBody.fnAbi.canUnwind = true`), executing a diverging panic call
`TerminatorKind.call panicFuncOp .nil ⟨destIdx, .nil⟩ .none unwind`
(`unwind = .cleanup cleanupBb ∨ unwind = .unreachable`) under `annealStepHooksForState`:
1. **Step 1 (Call Push)**: both Stage-1 `stepMirFn` and `lean-miri`
   (`annealStepHooksForState rootBody s`) step in lockstep (`StepRelMultiFrame.step`)
   to `MultiFrameStateRel`-related states `(s₁, m₁)` with `panicBody` pushed onto
   the call stack (`isDiverging = true`, `returnUnwind = unwind`);
2. **Step 2 (`UnwindResume` inside `panicBody`)**: from `(s₁, m₁)`, both machines
   step in lockstep (`StepRelMultiFrame`) via `step_terminator_unwindResume_callee_simulation`,
   popping `panicBody` and either jumping to the caller's `(cleanupBb, 0)` block
   (`StepRelMultiFrame.step` when `unwind = .cleanup cleanupBb`) or faulting with
   undefined behavior (`StepRelMultiFrame.ub` when `unwind = .unreachable`). -/
theorem step_terminator_call_linked_panic_unwind_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    {func : MirAst.Operand} {destIdx : Local} {destDecl : LocalDecl}
    {unwind : MirAst.UnwindAction}
    {defPath : DefPath} {panicBody : CapturedMir}
    {retDecl : LocalDecl} {panicBb0 : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .call func .nil ⟨destIdx, .nil⟩ .none unwind)
    (hfunc : extractCalleeDefPath? func = some defPath)
    (hcallee : findCallee? s.memory.callees defPath = some panicBody)
    (htypeArgs : extractCalleeTypeArgs func = .nil)
    (htparam : panicBody.typeParamCount = 0)
    (hdest_decl : get? (activeMirBody rootBody s).localDecls destIdx = some destDecl)
    (hpanic_decls : panicBody.localDecls = [retDecl])
    (hpanic_bb0 : get? panicBody.basicBlocks 0 = some panicBb0)
    (hpanic_stmts : panicBb0.statements = .nil)
    (hpanic_clean : panicBb0.isCleanup = true)
    (hpanic_term : panicBb0.terminator.kind = .unwindResume)
    (hpanic_phase : ∀ p, panicBody.phase ≠ .other p)
    (hpanic_unwind : panicBody.fnAbi.canUnwind = true)
    (hdest_wf : ∀ tf, m.stack.frames.back? = some tf →
      CallerDestSlotWf m.machine tf destIdx destDecl)
    (hdest_live : ∀ tf, m.stack.frames.back? = some tf → IsLiveFrameLocal tf destIdx)
    (hunwind : unwind = .unreachable ∨ ∃ cleanupBb, unwind = .cleanup cleanupBb) :
    StepRelMultiFrame rootBody m
      (stepMirFn rootBody s)
      (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m) ∧
    ∃ s₁ m₁,
      stepMirFn rootBody s = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = (m₁, .ok true) ∧
      MultiFrameStateRel rootBody s₁ m₁ ∧
      StepRelMultiFrame rootBody m₁
        (stepMirFn rootBody s₁)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s₁) () m₁) := by
  have hsim₁ :
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m) :=
    step_terminator_call_diverging_simulation hstate hphase hbb hstmt_none hstmt_len hterm
      hfunc hcallee htypeArgs htparam hdest_decl hpanic_decls hpanic_bb0
      hdest_wf hdest_live (fun _ _ => .nil []) (Or.inl hpanic_unwind) s.memory.fnPtrs
  rcases hstate with
    ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨callerMf, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some callerMf := by rw [harr]; simp
      have htf_eq : topFrame = callerMf := Option.some.inj (hback.symm.trans hback_tf)
      subst topFrame
      have ha_step₁ :
          stepMirFn rootBody s =
            .step
              (pushDivergingCalleeFrame s (activeMirBody rootBody s) s.frame.locals
                ⟨destIdx, .nil⟩ unwind panicBody []) := by
        rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm]
        unfold resolveCallTarget
        dsimp only []
        rw [hfunc, htypeArgs]
        dsimp only [evalOperands]
        rw [lookupCallee_nil_eq_of_findCallee_some _ _ _ _ hcallee htparam]
        rfl
      let s₁ :=
        pushDivergingCalleeFrame s (activeMirBody rootBody s) s.frame.locals
          ⟨destIdx, .nil⟩ unwind panicBody []
      have hsim₁' := hsim₁
      rw [ha_step₁] at hsim₁'
      generalize hm_res :
        Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m = mRes at hsim₁'
      cases hsim₁' with
      | step _ m₁ hrel₁ =>
        have hstack₁ :
            s₁.memory.callStack =
              { callerBody := activeMirBody rootBody s
                frame := s.frame
                destination := ⟨destIdx, .nil⟩
                returnTarget := 0
                callerProtector := none
                calleeProtectors := s.memory.activeProtectors
                returnUnwind := unwind
                isDiverging := true } :: s.memory.callStack := rfl
        have hact₁ : activeMirBody rootBody s₁ = panicBody := rfl
        have hdecl0_₁ : get? (activeMirBody rootBody s₁).localDecls 0 = some retDecl := by
          rw [hact₁, hpanic_decls]; rfl
        have hlive0_₁ : get? s₁.frame.locals 0 ≠ some .dead := by
          dsimp only [s₁, pushDivergingCalleeFrame, initLocals]
          rw [hpanic_decls]
          intro h; cases h
        have hva₁ : ∀ tf, m₁.stack.frames.back? = some tf → tf.vaList = #[] := by
          have hpush_sim :=
            step_terminator_call_args_simulation_ok
              (callerBody := activeMirBody rootBody s)
              (calleeBody := panicBody)
              (callerAf := s.frame)
              (topFrame := callerMf)
              (restMfs := restMfs)
              (destIdx := destIdx)
              (destDecl := destDecl)
              (targetOpt := none)
              (unwind := unwind)
              (m := m)
              hpanic_decls hpanic_bb0 hdest_decl [] s.frame.locals callerMf []
              rfl rfl rfl
              (fun _ _ lay hi => ⟨⟨lay, hi⟩, rfl⟩)
              (hdest_wf callerMf hback)
              (hdest_live callerMf hback)
              id hframe (.nil [])
          generalize ha_ops_eq :
            OperandsEvalResult.ok ([] : List Value) s.frame.locals = aOps at hpush_sim
          generalize hm_ops_eq :
            ({ m with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ },
             Except.ok ([] : List (Miri.Interpreter.RvalueImmTy AnnealProv))) = mOps at hpush_sim
          cases hpush_sim with
          | ub _ _ => cases ha_ops_eq
          | ok _ _ callerMf' calleeMf argImms' _ _ _ _ _ _
              hres_dest _ _ _ _ hva_callee hpush_spec =>
            cases ha_ops_eq
            have hm_imms : argImms' = [] := by
              injection hm_ops_eq with _ h; injection h with h2; exact h2.symm
            subst hm_imms
            have hcmf_eq : callerMf' = callerMf := by
              injection hm_ops_eq with hst _
              have hl := congrArg (fun st => st.stack.frames.toList) hst
              simpa using hl.symm
            subst callerMf'
            obtain ⟨hraw_ok, hraw_state, rawCalleeFrame, hraw_curr, hdone_eq⟩ := hpush_spec
            have htk :
                (translateTerminator bb.terminator).kind =
                  .Call (translateOperand func) #[] (translatePlace ⟨destIdx, .nil⟩)
                    none (translateUnwindAction unwind) .Normal defaultSpanRef := by
              unfold translateTerminator; rw [hterm]; rfl
            have hcall :
                annealEvalCallLM4_1 (activeMirBody rootBody s) s.memory.callees
                  (translateTerminator bb.terminator) m s.memory.fnPtrs =
                ({ stack := ⟨⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩⟩
                   machine := m.machine }, .ok ()) := by
              unfold annealEvalCallLM4_1 Miri.Interpreter.Stack.currentFrame?
              rw [hback]; dsimp only []
              rw [hframe.location_eq]; dsimp only []
              rw [hbb]; dsimp only []
              rw [hterm, htk]; dsimp only []
              rw [hfunc]
              dsimp only [List.map, annealEvalCallArgsLM4_1, Miri.Interpreter.runRvalue,
                pure, EStateM.pure]
              rw [hcallee]; dsimp only []
              unfold annealPushCalleeFrameLM4_1 Miri.Interpreter.Stack.currentFrame?
              rw [hback]; dsimp only []
              have hsize_m : m.stack.frames.size - 1 = restMfs.length := by rw [harr]; simp
              rw [hsize_m, hres_dest]; dsimp only []
              have hm_frames :
                  m.stack = ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ := by
                cases m with | mk st mach => cases st; dsimp only at harr ⊢; rw [harr]
              rw [hm_frames]
              rw [hraw_ok]; dsimp only []
              unfold Miri.Interpreter.Stack.currentFrame? at hraw_curr
              rw [hraw_curr]; dsimp only []
              rw [hraw_state, hdone_eq]
            unfold annealStepHooksForState at hm_res
            rw [miri_step_at_terminator_multiFrame hback hframe.body_eq hframe.location_eq hbb hstmt_none] at hm_res
            unfold Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksLM4_1 at hm_res
            rw [htk] at hm_res
            dsimp only [Id.run] at hm_res
            rw [hcall] at hm_res
            have hsize_ne :
                ((⟨(callerMf :: restMfs).reverse ++ [calleeMf]⟩ : Array _).size == m.stack.frames.size) =
                  false := by
              rw [harr]; simp
            simp only [hsize_ne, Bool.and_false, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, Except.map, pure, Pure.pure] at hm_res
            injection hm_res with hm₁_eq _
            intro tf htf
            rw [← hm₁_eq, array_back?_append_singleton] at htf
            injection htf with h_eq
            rw [← h_eq, hva_callee]
        have hsim₂ :
            StepRelMultiFrame rootBody m₁
              (stepMirFn rootBody s₁)
              (Miri.Interpreter.Step.step (annealStepHooksForState rootBody s₁) () m₁) :=
          step_terminator_unwindResume_callee_simulation hrel₁ hstack₁ hva₁
            (by rw [hact₁]; exact hpanic_phase)
            (by rw [hact₁]; exact hpanic_bb0)
            (by rw [hpanic_stmts]; rfl)
            (by rw [hpanic_stmts]; rfl)
            hpanic_clean hpanic_term hdecl0_₁ hlive0_₁ hunwind s₁.memory.fnPtrs
        exact ⟨by rw [hm_res] at hsim₁; exact hsim₁, s₁, m₁, ha_step₁, rfl, hrel₁, hsim₂⟩

/-- **Theorem 9b (`step_terminator_unwindTerminate_termination_abort_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, executing
`TerminatorKind.unwindTerminate` under `annealStepHooksWithDirectUnwind rootBody s`:
1. Stage-1 `stepMirFn rootBody s` halts with `MirStepNode.retOutcome .abort`;
2. `lean-miri` halts with `StepError.termination (.abort "panic in a function that cannot unwind")`,
   whose `Miri.Concurrency.TerminationInfo` classification is
   `.abnormalTermination` (`isUbReport = false`). -/
theorem step_terminator_unwindTerminate_termination_abort_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .unwindTerminate) :
    stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧
    Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m =
      (m, .error (.termination (.abort "panic in a function that cannot unwind"))) ∧
    (Miri.Concurrency.TerminationInfo.abort "panic in a function that cannot unwind").report =
      .abnormalTermination ∧
    (Miri.Concurrency.TerminationInfo.abort "panic in a function that cannot unwind").isUbReport =
      false := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, _⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      refine ⟨?_, ?_, rfl, rfl⟩
      · rw [stepMirFn_activeMirBody_eq rootBody s hphase]
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
        unfold evalTerminator
        rw [hterm]
      · unfold annealStepHooksWithDirectUnwind annealStepHooksForState annealStepHooksLM4_1
          annealStepHooks Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?
        rw [hback]
        dsimp only []
        rw [hframe.location_eq, hframe.body_eq]
        dsimp only []
        rw [translateBody_basicBlocks_getElem?, hbb]
        dsimp only [Option.map]
        rw [translateBasicBlockData_statements_getElem?, hstmt_none]
        dsimp only [Option.map, Id.run, translateBasicBlockData]
        unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
          annealTerminatorHooksWithDirectUnwind annealControlHooksWithDirectUnwind
        rw [hterm]
        rfl

/-- **Theorem 9c (`step_terminator_assert_failed_directUnwind_simulation`)**:
At arbitrary stack depth under `MultiFrameStateRel rootBody s m`, when
`TerminatorKind.assert (.copy ⟨condIdx, .nil⟩) expected target unwind` fails
(`get? s.frame.locals condIdx = some (.init (.scalar sc))`, `decide (sc.bits ≠ 0) ≠ expected`),
`Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m`
dispatches `Miri.Interpreter.ControlFlow.unwindToBlock`, simulating all four
cases of Stage-1 `applyUnwindAction s s.frame.locals s.memory unwind`
(`Terminators.lean:673-693`):
1. `unwind = .cleanup cleanupBb`: both machines jump in 1 step to `(cleanupBb, 0)`
   in the current frame, preserving `MultiFrameStateRel` (`StepRelMultiFrame.step`);
2. `unwind = .unreachable`: both machines fault in 1 step with undefined behavior
   (`StepRelMultiFrame.ub`);
3. `unwind = .terminate`: Stage-1 halts with `MirStepNode.retOutcome .abort` and
   `lean-miri` halts with `StepError.termination (.abort "panic in a function that cannot unwind")`;
4. `unwind = .continue_`: Stage-1 executes `unwindFromCallStack s.memory.callStack s.memory`,
   while `lean-miri` transitions the active frame to `.unwinding defaultSpanRef`
   in 1 step (`UnwindingStateRel rootBody s m₁`), from which
   `unwindFromCallStack_miri_multiStep_simulation` completes the multi-frame unwind. -/
theorem step_terminator_assert_failed_directUnwind_simulation
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {condIdx : Local} {condDecl : LocalDecl}
    {expected : Bool} {target : BasicBlockIdx} {unwind : MirAst.UnwindAction}
    {sc : MirAst.ScalarInt}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .assert (.copy ⟨condIdx, .nil⟩) expected target unwind)
    (hdecl : get? (activeMirBody rootBody s).localDecls condIdx = some condDecl)
    (hbool_ty : condDecl.ty.kind = .bool)
    (himm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf condIdx)
    (hsc : get? s.frame.locals condIdx = some (.init (.scalar sc)))
    (hne_exp : decide (sc.bits ≠ 0) ≠ expected) :
    (∀ cleanupBb, unwind = .cleanup cleanupBb →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m)) ∧
    (unwind = .unreachable →
      StepRelMultiFrame rootBody m
        (stepMirFn rootBody s)
        (Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m)) ∧
    (unwind = .terminate →
      stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧
      (Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m).2 =
        .error (.termination (.abort "panic in a function that cannot unwind"))) ∧
    (unwind = .continue_ →
      stepMirFn rootBody s =
        (match unwindFromCallStack s.memory.callStack s.memory with
         | .running nextState => .step nextState
         | .halted out => .retOutcome out
         | .faulted fk => .fail fk) ∧
      ∃ m₁,
        Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m =
          (m₁, .ok true) ∧
        UnwindingStateRel rootBody s m₁) := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid,
      hcid_pos, hcid_act, hcid_bor, hbt⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨topFrame₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
      dsimp only at hframe
      have harr := array_eq_of_toList_reverse_cons hmfs
      have hback_tf : m.stack.frames.back? = some topFrame₀ := by rw [harr]; simp
      have htf_eq : topFrame = topFrame₀ := Option.some.inj (hback.symm.trans hback_tf)
      subst htf_eq
      obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
      have hcache := hloc.layout_eq
      have himm' := himm topFrame hback mls hmls
      have hslot_eq : slot = .init (.scalar sc) := Option.some.inj (hslot.symm.trans hsc)
      subst hslot_eq
      cases hloc with
      | indirect _ mp _ _ _ _ => exact False.elim (himm' mp rfl)
      | immediate _ imm _ _ hval =>
        rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
        · cases h
        · injection hv with hv'; subst hv'
          obtain ⟨b, msc, hv_b, rfl, _, htoBool⟩ := bool_of_immediateRel hbool_ty himmRel
          have hsc_b : sc = boolToScalar b := by injection hv_b
          subst hsc_b
          have hdec_b : decide ((boolToScalar b).bits ≠ 0) = b := by cases b <;> rfl
          rw [hdec_b] at hne_exp
          have hexp_beq_false : (expected == b) = false :=
            beq_eq_false_iff_ne.mpr (Ne.symm hne_exp)
          let tfCached := cacheFrameLocalLayout topFrame condIdx hlt_mf
            (translateTy condDecl.ty (activeMirBody rootBody s).layouts)
          let hooks := annealTerminatorHooksWithDirectUnwind
            (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs
          have hread_ok :
              hooks.readAssertCondition () (.Copy ⟨condIdx, #[]⟩) m =
              ({ m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ }, .ok b) := by
            dsimp only [hooks]
            unfold annealTerminatorHooksWithDirectUnwind annealTerminatorHooksLM4_1
              annealTerminatorHooks Miri.Interpreter.runRvalue
            dsimp only []
            rw [EStateM.bind_eq_ok
              (annealEvalOperand_copy_live_multiFrame harr hlt_mf hdecl hmls_eq hcache)]
            dsimp only [annealReadImmediate, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
              Miri.Interpreter.Immediate.toScalar]
            rw [htoBool]
            rfl
          have hm_step_eq :
              Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m =
                miriFinishStep
                  (Miri.Interpreter.ControlFlow.evalTerminator hooks
                    () (translateTerminator bb.terminator) m) := by
            unfold annealStepHooksWithDirectUnwind annealStepHooksForState annealStepHooksLM4_1
              annealStepHooks Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?
            rw [hback]
            dsimp only []
            rw [hframe.location_eq, hframe.body_eq]
            dsimp only []
            rw [translateBody_basicBlocks_getElem?, hbb]
            dsimp only [Option.map]
            rw [translateBasicBlockData_statements_getElem?, hstmt_none]
            rfl
          have htk_assert :
              (translateTerminator bb.terminator).kind =
                .Assert (.Copy ⟨condIdx, #[]⟩) expected
                  (.BoundsCheck (.Copy ⟨condIdx, #[]⟩) (.Copy ⟨condIdx, #[]⟩))
                  target (translateUnwindAction unwind) := by
            unfold translateTerminator; rw [hterm]; rfl
          have hign :
              (hooks.ignoreOptionalOverflowChecks m &&
               Miri.Interpreter.ControlFlow.isOptionalOverflowCheck
                (.BoundsCheck (.Copy ⟨condIdx, #[]⟩) (.Copy ⟨condIdx, #[]⟩))) = false := rfl
          have ha_base :
              stepMirFn rootBody s =
                match applyUnwindAction s s.frame.locals s.memory unwind with
                | .running nextState => .step nextState
                | .halted out => .retOutcome out
                | .faulted fk => .fail fk := by
            rw [stepMirFn_activeMirBody_eq rootBody s hphase]
            have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
            simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
            unfold evalTerminator
            rw [hterm]
            have heval_a :
                evalOperand s.frame.locals (.copy ⟨condIdx, .nil⟩) s.memory.borrows s.memory.globals
                  (activeMirBody rootBody s).layouts s.memory.callerLocals =
                .ok (.scalar (boolToScalar b)) s.frame.locals := by
              unfold evalOperand; dsimp only []; rw [hsc]; rfl
            dsimp only []
            rw [heval_a]
            cases expected <;> cases b <;> (try exact False.elim (hne_exp rfl)) <;> rfl
          have hfr_cached := hframe.cache_local_layout hdecl hlt_mf
          have hdisj_orig : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [topFrame]⟩ := by
            rw [← harr]; exact hdisj
          have hd_top : MemoryAllocDisjoint topFrame :=
            hdisj_orig.intra_frame topFrame (by simp)
          have hd_tfCached : MemoryAllocDisjoint tfCached := by
            apply MemoryAllocDisjoint.mono_layout hd_top
            intro k
            by_cases hk : k = condIdx
            · subst hk
              exists (translateTy condDecl.ty (activeMirBody rootBody s).layouts)
              dsimp only [tfCached, cacheFrameLocalLayout]
              rw [Array.getElem?_set_self, hmls]
              simp [hmls_eq]
            · exists (topFrame.locals[k]?).bind (·.layout)
              dsimp only [tfCached, cacheFrameLocalLayout]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)]
              cases topFrame.locals[k]? <;> rfl
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro cleanupBb hunw
            subst hunw
            let tfTarget := { tfCached with location := .mir ⟨cleanupBb, 0⟩ }
            have hgo :
                Miri.Interpreter.ControlFlow.goToBlock cleanupBb
                  { m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ } =
                ({ m with stack := ⟨⟨restMfs.reverse ++ [tfTarget]⟩⟩ }, .ok ()) := by
              unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
                Miri.Interpreter.Stack.currentFrame?
              rw [array_back?_append_singleton restMfs.reverse tfCached]
              dsimp only []
              congr 3
              apply Array.ext'
              simp [tfTarget]
            rw [ha_base, hm_step_eq]
            unfold applyUnwindAction Miri.Interpreter.ControlFlow.evalTerminator
            rw [htk_assert]
            dsimp only [translateUnwindAction, Id.run]
            simp only [hign, hread_ok, Bool.false_or, hexp_beq_false, Bool.false_eq_true, ↓reduceIte]
            dsimp only [hooks, annealTerminatorHooksWithDirectUnwind,
              Miri.Interpreter.ControlFlow.unwindToBlock, Id.run]
            simp only [hgo, miriFinishStep, Except.map, Pure.pure, pure]
            apply StepRelMultiFrame.step
            have hfr_target :
                FrameRel (activeMirBody rootBody s) m.machine
                  { s.frame with blockIdx := cleanupBb, stmtIdx := 0 } tfTarget :=
              ⟨hfr_cached.body_eq, rfl, hfr_cached.af_locals_len,
               hfr_cached.mf_locals_size, hfr_cached.locals_rel⟩
            have hlinks_post :
                CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s)
                  { s.frame with blockIdx := cleanupBb, stmtIdx := 0 }
                  s.memory.callStack s.memory.activeProtectors (tfTarget :: restMfs) := by
              refine hlinks.update_top_frame rfl rfl rfl hfr_target ?_
              intro mp0 lay0 h0
              dsimp only [tfTarget, tfCached, cacheFrameLocalLayout] at h0
              by_cases hc0 : condIdx = 0
              · subst hc0
                rw [Array.getElem?_set_self] at h0
                injection h0 with h_eq
                have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                rw [hmls_eq] at hv_eq; cases hv_eq
              · rw [Array.getElem?_set_ne _ hc0] at h0
                exact ⟨⟨lay0, h0⟩, Or.inl rfl⟩
            have hd_tfTarget : MemoryAllocDisjoint tfTarget := hd_tfCached
            have hdisj_post : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [tfTarget]⟩ := by
              apply hdisj_orig.replace_top hd_tfTarget
              intro i mp lay hi
              dsimp only [tfTarget, tfCached, cacheFrameLocalLayout] at hi
              by_cases hi_c : condIdx = i
              · subst hi_c
                rw [Array.getElem?_set_self] at hi
                injection hi with h_eq
                have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                rw [hmls_eq] at hv_eq; cases hv_eq
              · rw [Array.getElem?_set_ne _ hi_c] at hi
                exact ⟨lay, hi⟩
            exact .mk tfTarget
              (array_back?_append_singleton restMfs.reverse tfTarget)
              hcal_root hcal_nonroot
              (by
                unfold FrameStackRel annealFrameStackTopDown activeMirBody
                rw [array_toList_reverse_append_singleton restMfs tfTarget]
                exact hlinks_post.toForall2)
              (by
                unfold activeMirBody
                rw [array_toList_reverse_append_singleton restMfs tfTarget]
                exact hlinks_post)
              hdisj_post htb hvalid hcid_pos hcid_act hcid_bor hbt
          · intro hunw
            subst hunw
            rw [ha_base, hm_step_eq]
            unfold applyUnwindAction Miri.Interpreter.ControlFlow.evalTerminator
            rw [htk_assert]
            dsimp only [translateUnwindAction, Id.run]
            simp only [hign, hread_ok, Bool.false_or, hexp_beq_false, Bool.false_eq_true, ↓reduceIte]
            exact StepRelMultiFrame.ub _ _
          · intro hunw
            subst hunw
            refine ⟨by rw [ha_base]; rfl, ?_⟩
            rw [hm_step_eq]
            unfold Miri.Interpreter.ControlFlow.evalTerminator
            rw [htk_assert]
            dsimp only [translateUnwindAction, Id.run]
            simp only [hign, hread_ok, Bool.false_or, hexp_beq_false, Bool.false_eq_true, ↓reduceIte]
            dsimp only [hooks, annealTerminatorHooksWithDirectUnwind,
              annealControlHooksWithDirectUnwind, annealControlHooksLM4_1,
              Miri.Interpreter.ControlFlow.unwindToBlock,
              Miri.Interpreter.ControlFlow.setLocation,
              Miri.Interpreter.Stack.currentFrame?, Id.run]
            rw [array_back?_append_singleton restMfs.reverse tfCached]
            rfl
          · intro hunw
            subst hunw
            refine ⟨by rw [ha_base]; rfl, ?_⟩
            let tfUnw := { tfCached with location := .unwinding defaultSpanRef }
            let m₁_mir : AnnealStepState :=
              { m with stack := ⟨⟨restMfs.reverse ++ [tfCached]⟩⟩ }
            let m₁ : AnnealStepState :=
              { m with stack := ⟨⟨restMfs.reverse ++ [tfUnw]⟩⟩ }
            refine ⟨m₁, ?_, ?_⟩
            · rw [hm_step_eq]
              unfold Miri.Interpreter.ControlFlow.evalTerminator
              rw [htk_assert]
              dsimp only [translateUnwindAction, Id.run]
              simp only [hign, hread_ok, Bool.false_or, hexp_beq_false, Bool.false_eq_true, ↓reduceIte]
              dsimp only [hooks, annealTerminatorHooksWithDirectUnwind,
                annealControlHooksWithDirectUnwind, annealControlHooksLM4_1,
                Miri.Interpreter.ControlFlow.unwindToBlock,
                Miri.Interpreter.ControlFlow.setLocation,
                Miri.Interpreter.Stack.currentFrame?, Id.run]
              rw [array_back?_append_singleton restMfs.reverse tfCached]
              simp only [miriFinishStep, Except.map, Pure.pure, pure, Bind.bind, bind]
              congr 2
              congr 1
              apply Array.ext'
              simp [tfUnw]
            · refine ⟨m₁_mir, tfCached, defaultSpanRef,
                array_back?_append_singleton restMfs.reverse tfCached, ?_, ?_⟩
              · dsimp only [m₁, m₁_mir, tfUnw]
                congr 2
                apply Array.ext'
                simp
              · have hlinks_cached :
                    CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s)
                      s.frame s.memory.callStack s.memory.activeProtectors
                      (tfCached :: restMfs) := by
                  refine hlinks.update_top_frame rfl rfl rfl hfr_cached ?_
                  intro mp0 lay0 h0
                  dsimp only [tfCached, cacheFrameLocalLayout] at h0
                  by_cases hc0 : condIdx = 0
                  · subst hc0
                    rw [Array.getElem?_set_self] at h0
                    injection h0 with h_eq
                    have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                    rw [hmls_eq] at hv_eq; cases hv_eq
                  · rw [Array.getElem?_set_ne _ hc0] at h0
                    exact ⟨⟨lay0, h0⟩, Or.inl rfl⟩
                have hdisj_cached : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [tfCached]⟩ := by
                  apply hdisj_orig.replace_top hd_tfCached
                  intro i mp lay hi
                  dsimp only [tfCached, cacheFrameLocalLayout] at hi
                  by_cases hi_c : condIdx = i
                  · subst hi_c
                    rw [Array.getElem?_set_self] at hi
                    injection hi with h_eq
                    have hv_eq := congrArg Miri.Interpreter.LocalState.value h_eq
                    rw [hmls_eq] at hv_eq; cases hv_eq
                  · rw [Array.getElem?_set_ne _ hi_c] at hi
                    exact ⟨lay, hi⟩
                exact .mk tfCached
                  (array_back?_append_singleton restMfs.reverse tfCached)
                  hcal_root hcal_nonroot
                  (by
                    unfold FrameStackRel annealFrameStackTopDown activeMirBody
                    dsimp only [m₁_mir]
                    rw [array_toList_reverse_append_singleton restMfs tfCached]
                    exact hlinks_cached.toForall2)
                  (by
                    unfold activeMirBody
                    dsimp only [m₁_mir]
                    rw [array_toList_reverse_append_singleton restMfs tfCached]
                    exact hlinks_cached)
                  hdisj_cached htb hvalid hcid_pos hcid_act hcid_bor hbt

end LeanMiriSpec.Correspondence
