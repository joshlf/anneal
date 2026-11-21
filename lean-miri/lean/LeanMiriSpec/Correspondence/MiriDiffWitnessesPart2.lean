/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.Correspondence.MiriDiffWitnessesPart1

/-!
# `LM-4.3`: `miri-diff` Formal Witness Suite (Sections 5–6)

Continuation of `MiriDiffWitnessesPart1` (Sections 0–4), covering multi-frame
calls, stack unwinding, indirect `FnPtr` calls, and intrinsics (`write_bytes`,
`copy_nonoverlapping`, `arith_offset`, `rotate_left`) in the same
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
`GlobalState.endCall` on the callee frame pop; modeled on `pass_direct_fn_call`, a
former `known_anneal_bug` ratchet): the caller calls `crate::five`,
which returns `5_u8` into `_1`; the caller returns `5_u8`. Both machines run the
whole program from their entry states (Anneal with `crate::five` as a callee). -/
theorem w5_call_return :
    AgreeReturnsBits callFiveBody (callHooks callFiveBody [fiveBody])
      (initMachineStateWithCallees callFiveBody [] [fiveBody]) (miriEntryState callFiveBody) 1 5 :=
  agreeReturnsBits_of_obs (N := 8) (M := 8) (by kernel_decide) (by kernel_decide)

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
    { root_depth := (by decide), root_protectors_nil := (fun h => by cases h), last_restores_nil := (fun _ h => by cases h; rfl) }

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
  have hs₁ : stepMirFn protCallerBody protReadyAnneal = .step s₁ := by kernel_rfl
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
    have hs₂ : stepMirFn protCallerBody s₁ = .retNormal (.scalar WitnessLM4_1.sc1)
        { s₁.memory with borrows := disableFrameBorrows s₁.memory.borrows 0 protCallerBody.localDecls.length } := by kernel_rfl
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
  agreeUB_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

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
  agreeUB_of_obs (N := 4) (M := 4) (by kernel_decide) (by kernel_decide)

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
  agreeReturnsBits_of_obs (N := 12) (M := 14) (by kernel_decide) (by kernel_decide)

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
  agreeUB_of_obs (N := 8) (M := 10) (by kernel_decide) (by kernel_decide)

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
    (m := miriEntryState unwindPastRootBody) (by kernel_decide)
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
  agreeReturnsBits_of_obs (N := 12) (M := 12) (by kernel_decide) (by kernel_decide)

/-- The static function-pointer table `[fiveFnPtrEntry]` of
`w5_indirect_fnPtr_call_returns` is the one Stage-1 builds: after
`StorageLive(_1); StorageLive(_2); _2 = crate::five as fn() -> u8 (ReifyFnPointer)`,
Anneal's `Memory.fnPtrs` is exactly `[fiveFnPtrEntry]`. -/
theorem indirectCallFive_reify_fnPtrs :
    ∃ s, runAnnealBounded indirectCallFiveBody 3
        (initMachineStateWithCallees indirectCallFiveBody [] [fiveBody]) = .running s ∧
      s.memory.fnPtrs = [fiveFnPtrEntry] :=
  ⟨_, rfl, rfl⟩

/-- `FnDef` type of the external `core::fmt::Arguments::<'a>::from_str` (no linked body). -/
def fmtFromStrFnTy : Ty :=
  { kind := .fnDef "core::fmt::Arguments::<'a>::from_str" [], layoutIdx := 0 }

/-- `FnDef` type of the diverging `core::panicking::panic_fmt`. -/
def panicFmtFnTy : Ty :=
  { kind := .fnDef "core::panicking::panic_fmt" [], layoutIdx := 0 }

/-- Root body modeled on the sole remaining open `known_anneal_bug` ratchet
`panic_explicit_macro` (`tests/miri-diff/manifest.toml`): an explicit `panic!("...")`
first calls `core::fmt::Arguments::<'a>::from_str` (`bb0 -> bb1`, `.continue_`)
before calling the diverging `core::panicking::panic_fmt` (`bb1`, `target := none`,
`.continue_`). -/
def panicExplicitMacroBody : CapturedMir :=
  mkBody "lm_4_3_witness::panic_explicit_macro" [dcl tyU8, dcl tyU8]
    [blk [st (.storageLive 1)]
       (.call (.constant { ty := fmtFromStrFnTy, val := .zeroSized }) []
         (pl 1) (some 1) .continue_),
     blk []
       (.call (.constant { ty := panicFmtFnTy, val := .zeroSized }) [.copy (pl 1)]
         (pl 0) none .continue_)]

/-- **Open `known_anneal_bug` ratchet boundary (`panic_explicit_macro`), from entry**:
after `StorageLive(_1)`, Stage-1 emits `MirStepNode.extCall` for
`"core::fmt::Arguments::<'a>::from_str"` before reaching `bb1`'s diverging
`core::panicking::panic_fmt`. When the environment returns (keeping the root
`callStack`), Stage-1 panics in `panic_fmt` (`ReachesRet … .panic`). The
`MirReachesUB` / `¬ TreeSafe` conjuncts do not come from the program: Stage-1's
`MirCallAns.panicked` answer carries a whole `Memory`, and `applyUnwindAction` for
the call's `UnwindAction::Continue` unwinds through that memory's `callStack`, so
the answer `memBad`, whose `callStack` holds a caller frame (never pushed by the
program) with `UnwindAction::Unreachable`, faults. Every reachable external call
with `UnwindAction::Continue` is exposed to such answers
(`anneal_extCall_continue_unwind_ub`; see the external-call boundary in
`Safety.lean`). `lean-miri`, which models no external functions, stops
with `.unsupported` (`¬ Safe`). -/
theorem w5_panic_explicit_macro_extCall_boundary :
    (∃ s₁ req k,
      stepMirFn panicExplicitMacroBody (initMachineState panicExplicitMacroBody []) = .step s₁ ∧
      stepMirFn panicExplicitMacroBody s₁ = MirStepNode.extCall req k ∧
      req.defPath = "core::fmt::Arguments::<'a>::from_str") ∧
    (∃ tr, ReachesRet (mirCallTree panicExplicitMacroBody []) tr .panic) ∧
    MirReachesUB (mirCallTree panicExplicitMacroBody []) ∧
    ¬ TreeSafe (mirCallTree panicExplicitMacroBody []) ∧
    (∃ e, (miriSystem (annealMiriHooks panicExplicitMacroBody)).ReachesOutcome
      (miriEntryState panicExplicitMacroBody) (.unsupported e)) ∧
    ¬ (miriSystem (annealMiriHooks panicExplicitMacroBody)).Safe
      (miriEntryState panicExplicitMacroBody) := by
  let s₀ := initMachineState panicExplicitMacroBody []
  let s₁ : MachineState := { s₀ with frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .uninit] } }
  let req : MirCallReq :=
    { defPath := "core::fmt::Arguments::<'a>::from_str", typeArgs := [], args := [], memory := s₁.memory }
  have hs₀ : stepMirFn panicExplicitMacroBody s₀ = .step s₁ := by kernel_rfl
  have hs₁ : stepMirFn panicExplicitMacroBody s₁ =
      MirStepNode.extCall req (resumeExternalCall s₁ s₁.frame.locals (pl 1) 1 .continue_) := by kernel_rfl
  let s₂ : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨0, 1⟩)] },
      memory := s₁.memory }
  have hres : resumeExternalCall s₁ s₁.frame.locals (pl 1) 1 .continue_
      (.returned (.scalar ⟨0, 1⟩) s₁.memory) = .running s₂ := rfl
  have hs₂ : stepMirFn panicExplicitMacroBody s₂ = MirStepNode.retOutcome .panic := by kernel_rfl
  have hco₁ := (AnnealPath.step .silent hs₀ (.refl _)).coReach
  have hco₂ : CoReach (stepMirState panicExplicitMacroBody) (.running s₀) (.running s₂) := by
    have h := hco₁.tail (coStep_of_extCall hs₁ (.returned (.scalar ⟨0, 1⟩) s₁.memory))
    rwa [hres] at h
  let memBad : Memory :=
    { s₁.memory with callStack :=
        [{ callerBody := panicExplicitMacroBody, frame := s₁.frame,
           destination := pl 0, returnUnwind := .unreachable }] }
  have hco_ub := hco₁.tail (coStep_of_extCall hs₁ (.panicked memBad))
  have hbad : resumeExternalCall s₁ s₁.frame.locals (pl 1) 1 .continue_ (.panicked memBad) =
      .faulted .ub := rfl
  rw [hbad] at hco_ub
  obtain ⟨hub, hns⟩ := anneal_ub_of_coReach hco_ub rfl
  obtain ⟨herr, hnm⟩ := miri_unsupported_of_obs (H := annealMiriHooks panicExplicitMacroBody)
    (N := 3) (m := miriEntryState panicExplicitMacroBody) (by kernel_decide)
  rw [mirCallTree, mirTree_eq_cofix]
  exact ⟨⟨s₁, req, _, hs₀, hs₁, rfl⟩, reachesRet_cofix_iff.2 ⟨.running s₂, hco₂, hs₂⟩,
    by rw [← mirTree_eq_cofix]; exact hub, by rw [← mirTree_eq_cofix]; exact hns, herr, hnm⟩

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

/-- `WitnessLM4_2.arithOffsetPosBody` behind the entry block of `ptr4EntryBody`:

```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 42_u64;
     goto -> bb1;
bb1: _2 = &raw mut _1;
     _0 = arith_offset::<u64>(copy _2, 5_isize) -> bb2;
bb2: return
``` -/
def arithOffsetPosEntryBody : CapturedMir :=
  ptr4EntryBody "lm_4_3_witness::arith_offset_pos"
    WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K WitnessLM4_2.rawMutU64K
    [WitnessLM4_2.mkStmt42 (.assign (WitnessLM4_2.local42 2) (.rawPtr .mut (WitnessLM4_2.local42 1)))]
    (arithOffsetEntryTerm 2 5)

/-- **`retArithOffset_trace`**: run of `arithOffsetPosEntryBody` from the
post-entry-block states `ptr4EntryPreAnneal` / `ptr4EntryPreMiri` (which
`initMachineState` / `miriEntryState` reach in `5` steps) to its root return.
Both machines take the two steps of `wit_lm4_2_arith_offset_pos` in lockstep (the
`arith_offset` call through Stage-1's `call_intrinsic_arithOffset_stage1_simulation`),
and then both return from the root frame. Anneal returns the raw pointer
`{ allocId := 1, offsetBytes := 40 }`, which points `40` bytes past the start of
the 8-byte stack allocation of `_1`, and `lean-miri` returns an immediate
related to it by `ImmediateRelLM3_1.rawPtr`. -/
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
      stepMirFn b s₂ = .retNormal (.ptr { allocId := 1, offsetBytes := 40 } 8)
        { s₂.memory with borrows := disableFrameBorrows s₂.memory.borrows 0 b.localDecls.length } ∧
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
  -- Step 2: `_0 = arith_offset::<u64>(copy _2, 5_isize) -> bb2`.
  let s₂ := WitnessLM4_2.mkPtrState b 2 0
    [.init (.ptr { allocId := 1, offsetBytes := 40 } 8), .init (.scalar ⟨42, 8⟩),
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
      .retNormal (.ptr { allocId := 1, offsetBytes := 40 } 8)
        { s₂.memory with borrows := disableFrameBorrows s₂.memory.borrows 0 b.localDecls.length } := by kernel_rfl
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
pre-Stage-1 reference model; Stage-1 Anneal returns the same bytes
(`w6_write_bytes_read_returns`). -/

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
      .running retWriteBytesReadPreAnneal := by kernel_rfl

/-- The entry block of `retWriteBytesReadBody`, from `miriEntryState`. -/
theorem retWriteBytesRead_prefix_miri :
    runLoopFuel (annealMiriHooks retWriteBytesReadBody) 5 (miriEntryState retWriteBytesReadBody) =
      .running retWriteBytesReadPreMiri := by kernel_rfl

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
2. `write_bytes::<u64>(copy _2, 0xAB_u8, 1_usize) -> bb2`, which `lean-miri`,
   the reference model, and Stage-1 `stepMirFn` (`evalWriteBytesCall`, since
   `ws-repatriate-leaked-ground-semantics-to-tcb`) all execute inline, filling
   all 8 bytes of `_1` with `0xAB`
   (`0xABAB_ABAB_ABAB_ABAB = 12370169555311111083`);
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
      (∃ sW, stepMirFn b s₁ = .step sW ∧
        get? sW.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩))) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨0xABABABABABABABAB, 8⟩)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      StepObsRelLM3_1 b m₃ [entry] (stepMirFn b s₃) (Miri.Interpreter.Step.step hooks () m₃) ∧
      stepMirFn b s₃ = .retNormal (.scalar ⟨0xABABABABABABABAB, 8⟩)
        { s₃.memory with borrows := disableFrameBorrows s₃.memory.borrows 0 b.localDecls.length } ∧
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
  have hs₁ : stepMirFn b retWriteBytesReadPreAnneal = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFnLM4_2 b s₁ = .step s₂ := by kernel_rfl
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
  have hs₃ : stepMirFn b s₂ = .step s₃ := by kernel_rfl
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
  have hs₄ : stepMirFn b s₃ = .retNormal (.scalar ⟨0xABABABABABABABAB, 8⟩)
      { s₃.memory with borrows := disableFrameBorrows s₃.memory.borrows 0 b.localDecls.length } := by kernel_rfl
  have hsim₄ := step_terminator_goto_return_lm3_1_simulation hrel₃ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, WitnessLM4_2.declOf WitnessLM4_2.u64K, rfl,
      (fun _ _ h => nomatch h), (by decide), himm₃⟩))
  have hobs₄ := hsim₄.toStepObsRelLM3_1
  rw [hs₄] at hsim₄
  obtain ⟨decl0, imm0, hdecl0, hop, himm, hmret⟩ := retStepRelLM3_1_retNormal_rel hsim₄
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, decl0, imm0, hs₁, hm₁, hrel₁, hs₂,
    ⟨_, by dsimp only [b, s₁, entry]; rfl, rfl⟩, hm₂, hrel₂, rfl,
    hs₃, hm₃, hrel₃, hobs₄, hs₄, hmret, hdecl0, hop, himm⟩

/-!
### Whole-program `copy_nonoverlapping` return trace

`retCopyBody` copies `42_u64` from `_1` into `_2` through raw pointers to the
two disjoint locals, reads the copied value back through the destination
pointer into `_0`, and returns it (modeled on
`pass_copy_nonoverlapping_disjoint_locals` of the `miri-diff` corpus):
```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); StorageLive(_4);
     _1 = const 42_u64; _2 = const 99_u64; goto -> bb1;
bb1: _3 = &raw const _1; _4 = &raw mut _2;
     copy_nonoverlapping(copy _3, copy _4, 1_usize); _0 = copy (*_4); return
```
`initMachineState` / `miriEntryState` run the entry block `bb0` in `7` steps to the
`StateRel`-related states `retCopyAnnealPre` / `retCopyMiriPre`
(`retCopy_prefix_anneal`, `retCopy_prefix_miri`; `_1 = 42_u64`, `_2 = 99_u64`),
from which `retCopy_trace` runs Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step` (`annealStepHooks`) in lockstep through the root
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
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3); StorageLive(_4);
     _1 = const 42_u64; _2 = const 99_u64; goto -> bb1;
bb1: _3 = &raw const _1; _4 = &raw mut _2;
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

/-- Anneal's state of `retCopyBody` after the entry block `bb0` (at `bb1`):
`_1 = 42_u64`, `_2 = 99_u64`, and all other locals `.uninit`. -/
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

/-- `lean-miri`'s state of `retCopyBody` after the entry block `bb0`. -/
def retCopyMiriPre : AnnealStepState :=
  { stack := ⟨#[retCopyMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- The entry block of `retCopyBody`, from `initMachineState`. -/
theorem retCopy_prefix_anneal :
    runAnnealBounded retCopyBody 7 (initMachineState retCopyBody []) =
      .running retCopyAnnealPre := by kernel_rfl

/-- The entry block of `retCopyBody`, from `miriEntryState`. -/
theorem retCopy_prefix_miri :
    runLoopFuel (annealMiriHooks retCopyBody) 7 (miriEntryState retCopyBody) =
      .running retCopyMiriPre := by kernel_rfl

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
post-entry-block states `retCopyAnnealPre` / `retCopyMiriPre` (`_1 = 42_u64`,
`_2 = 99_u64`, at `bb1`):
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
      stepMirFn b s₄ = .retNormal (.scalar ⟨42, 8⟩)
        { s₄.memory with borrows := disableFrameBorrows s₄.memory.borrows 0 b.localDecls.length } ∧
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
  have hs₁ : stepMirFn b retCopyAnnealPre = .step s₁ := by kernel_rfl
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
  have hs₂ : stepMirFn b s₁ = .step s₂ := by kernel_rfl
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
  have hs₃ : stepMirFn b s₂ = .step s₃ := by kernel_rfl
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
  have hs₄ : stepMirFn b s₃ = .step s₄ := by kernel_rfl
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
  have hret : stepMirFn b s₄ = .retNormal (.scalar ⟨42, 8⟩)
      { s₄.memory with borrows := disableFrameBorrows s₄.memory.borrows 0 b.localDecls.length } := by kernel_rfl
  rw [hret] at hsim₅
  generalize hm_res : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₄ =
    mRes at hsim₅
  cases hsim₅ with
  | retRoot decl0 _ imm0 _ m' hdecl0 hop0 himm0 hm' =>
    subst hm'
    exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂,
      hs₃, hm₃, hrel₃, rfl, hmem₂, hs₄, hm₄, hrel₄, hret, hm_res, hdecl0, hop0, himm0⟩


end LeanMiriSpec.Correspondence.MiriDiffWitnesses
