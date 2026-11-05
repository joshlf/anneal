import Anneal.MirFuelFree
import Anneal.FunctionalTranslation
open Trusted.Refinement
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.MirFuelFree
open Anneal.FunctionalTranslation
open Trusted.Rustc.V2026_06_01.Layout

namespace Anneal.MirLoops

-- Copyright 2026 The Fuchsia Authors. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE file.



def zipMachineState (cond : Bool) (sThen sElse : MachineState) : MachineState :=
  { frame :=
      { blockIdx := if cond then sThen.frame.blockIdx else sElse.frame.blockIdx,
        stmtIdx := if cond then sThen.frame.stmtIdx else sElse.frame.stmtIdx,
        locals := zipLocalSlots cond sThen.frame.locals sElse.frame.locals },
    memory := if cond then sThen.memory else sElse.memory }

def wpTransPlanConverges
    (body : CapturedMir)
    (plan : TransPlan)
    (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  match plan with
  | .ret _ => MirWpConverges body s post
  | .jump _ _ => False
  | .splitBranch _ _ _ => False
  | .loop _ _ _ _ _ => False
  | .seq targetBb cont stepFuel =>
    match runMirToBlock stepFuel body targetBb s with
    | .some s' => wpTransPlanConverges body cont s' post
    | .none => False
  | .branch joinBb thenPlan elsePlan cont preFuel =>
    joinPlanMemConsistent body plan s ∧
      match runMirToBinarySwitch preFuel body s with
      | .none => False
      | .some (cond, _, sThen₀, sElse₀) =>
        match evalPlanToJoin body thenPlan sThen₀, evalPlanToJoin body elsePlan sElse₀ with
        | .some sThen, .some sElse =>
          sThen.frame.blockIdx = joinBb ∧ sElse.frame.blockIdx = joinBb ∧
          sThen.frame.stmtIdx = 0 ∧ sElse.frame.stmtIdx = 0 ∧
          sThen.frame.locals.length = sElse.frame.locals.length ∧
          wpTransPlanConverges body cont (zipMachineState cond sThen sElse) post
        | _, _ => False

theorem MirWpConverges.join_of_branches
    {body : CapturedMir} {Q : MirOutcome → Prop} :
    (plan : TransPlan) → ∀ {s sJoin : MachineState},
      evalPlanToJoin body plan s = some sJoin →
      joinPlanMemConsistent body plan s →
      MirWpConverges body sJoin Q →
      MirWpConverges body s Q
  | .ret _, _, _, h, _, _ => by nomatch h
  | .splitBranch _ _ _, _, _, h, _, _ => by nomatch h
  | .loop _ _ _ _ _, _, _, h, _, _ => by nomatch h
  | .jump targetBlock fuel, _, _, h, _, h_next =>
    MirWpConverges.of_runMirToBlock h h_next
  | .seq nextBlock nextPlan fuel, s, sJoin, h, h_mem, h_next => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_blk : runMirToBlock fuel body nextBlock s with
    | none => rw [h_blk] at h; nomatch h
    | some s' =>
      rw [h_blk] at h h_mem
      exact MirWpConverges.of_runMirToBlock h_blk
        (MirWpConverges.join_of_branches nextPlan h h_mem h_next)
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s, sJoin, h, h_mem, h_next => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; nomatch h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h h_mem
      dsimp only at h h_mem
      cases h_t : evalPlanToJoin body thenPlan sThen₀ with
      | none => rw [h_t] at h; nomatch h
      | some sThen =>
        cases h_e : evalPlanToJoin body elsePlan sElse₀ with
        | none => rw [h_t, h_e] at h; nomatch h
        | some sElse =>
          rw [h_t, h_e] at h h_mem
          rcases h_mem with ⟨h_meq, h_mt, h_me, h_mj⟩
          dsimp only at h
          cases h_chk : (Nat.beq sThen.frame.blockIdx joinBlock && Nat.beq sElse.frame.blockIdx joinBlock &&
             sThen.frame.stmtIdx.beq 0 && sElse.frame.stmtIdx.beq 0 &&
             sThen.frame.locals.length.beq sElse.frame.locals.length)
          · rw [h_chk] at h; nomatch h
          · rw [h_chk] at h
            refine MirWpConverges.of_runMirToBinarySwitch h_sw ?_
            have h_joined : MirWpConverges body {
              frame := {
                blockIdx := joinBlock,
                stmtIdx := 0,
                locals := zipLocalSlots cond sThen.frame.locals sElse.frame.locals
              },
              memory := sThen.memory
            } Q := MirWpConverges.join_of_branches joinPlan h h_mj h_next
            simp at h_chk
            rcases h_chk with ⟨⟨⟨⟨h_tb, h_eb⟩, h_ts⟩, h_es⟩, h_len⟩
            have h_zip := zipLocalSlots_eq_ite cond h_len
            rw [h_zip] at h_joined
            cases cond
            · have h_mem_eq : sElse.memory = sThen.memory := h_meq.symm
              have h_eq : { frame := { blockIdx := joinBlock, stmtIdx := 0, locals := (if false then sThen.frame.locals else sElse.frame.locals) }, memory := sThen.memory } = sElse := by
                cases sElse with | mk f m =>
                cases f with | mk b s l =>
                simp [h_eb.symm, h_es.symm, h_mem_eq.symm]
              rw [h_eq] at h_joined
              exact MirWpConverges.join_of_branches elsePlan h_e h_me h_joined
            · have h_eq : { frame := { blockIdx := joinBlock, stmtIdx := 0, locals := (if true then sThen.frame.locals else sElse.frame.locals) }, memory := sThen.memory } = sThen := by
                cases sThen with | mk f m =>
                cases f with | mk b s l =>
                simp [h_tb.symm, h_ts.symm]
              rw [h_eq] at h_joined
              exact MirWpConverges.join_of_branches thenPlan h_t h_mt h_joined

theorem mirWpConverges_of_wpTransPlanConverges
    (body : CapturedMir) (plan : TransPlan) (s : MachineState) (post : MirOutcome → Prop)
    (h : wpTransPlanConverges body plan s post) :
    MirWpConverges body s post := by
  induction plan generalizing s with
  | ret _ => exact h
  | jump _ _ => exact False.elim h
  | splitBranch _ _ _ => exact False.elim h
  | loop _ _ _ _ _ => exact False.elim h
  | seq targetBb cont stepFuel ih =>
    unfold wpTransPlanConverges at h
    split at h
    · next s' h_blk =>
      exact MirWpConverges.of_runMirToBlock h_blk (ih s' h)
    · exact False.elim h
  | branch joinBb thenPlan elsePlan cont preFuel ihThen ihElse ihCont =>
    unfold wpTransPlanConverges at h
    rcases h with ⟨h_mem, h⟩
    split at h
    · exact False.elim h
    · next cond bits sThen₀ sElse₀ h_sw =>
      split at h
      · next sThen sElse h_t h_e =>
        rcases h with ⟨h_tb, h_eb, h_ts, h_es, h_len, h_cont⟩
        refine MirWpConverges.of_runMirToBinarySwitch h_sw ?_
        unfold joinPlanMemConsistent at h_mem
        rw [h_sw] at h_mem
        dsimp only at h_mem
        rw [h_t, h_e] at h_mem
        rcases h_mem with ⟨h_meq, h_mt, h_me, h_mj⟩
        have h_next : MirWpConverges body (zipMachineState cond sThen sElse) post := ihCont _ h_cont
        unfold zipMachineState at h_next
        have h_zip := zipLocalSlots_eq_ite cond h_len
        rw [h_zip] at h_next
        cases cond
        · have h_eq : { frame := { blockIdx := if false then sThen.frame.blockIdx else sElse.frame.blockIdx, stmtIdx := if false then sThen.frame.stmtIdx else sElse.frame.stmtIdx, locals := if false then sThen.frame.locals else sElse.frame.locals }, memory := if false then sThen.memory else sElse.memory } = sElse := by
            cases sElse with | mk f m =>
            cases f with | mk b s l =>
            simp
          rw [h_eq] at h_next
          exact MirWpConverges.join_of_branches elsePlan h_e h_me h_next
        · have h_eq : { frame := { blockIdx := if true then sThen.frame.blockIdx else sElse.frame.blockIdx, stmtIdx := if true then sThen.frame.stmtIdx else sElse.frame.stmtIdx, locals := if true then sThen.frame.locals else sElse.frame.locals }, memory := if true then sThen.memory else sElse.memory } = sThen := by
            cases sThen with | mk f m =>
            cases f with | mk b s l =>
            simp
          rw [h_eq] at h_next
          exact MirWpConverges.join_of_branches thenPlan h_t h_mt h_next
      · exact False.elim h

def forRangeUp {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo < hi then
    forRangeUp (lo + 1) hi (step lo (Nat.le_refl lo) h init) (fun i hlo hhi a => step i (Nat.le_trans (Nat.le_succ lo) hlo) hhi a)
  else
    init
termination_by hi - lo

theorem forRangeUp_unfold {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    forRangeUp lo hi init step =
    if h : lo < hi then
      forRangeUp (lo + 1) hi (step lo (Nat.le_refl lo) h init) (fun i hlo hhi a => step i (Nat.le_trans (Nat.le_succ lo) hlo) hhi a)
    else
      init := by
  conv =>
    lhs
    unfold forRangeUp

@[simp] theorem forRangeUp_eq_init_of_ge {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (hGe : lo ≥ hi) : forRangeUp lo hi init step = init := by
  rw [forRangeUp_unfold]
  have hNotLt : ¬(lo < hi) := by omega
  simp [hNotLt]

@[simp] theorem forRangeUp_step_of_lt {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (hLt : lo < hi) : forRangeUp lo hi init step =
    forRangeUp (lo + 1) hi (step lo (Nat.le_refl lo) hLt init) (fun i hlo hhi a => step i (Nat.le_trans (Nat.le_succ lo) hlo) hhi a) := by
  rw [forRangeUp_unfold]
  simp [hLt]

theorem forRangeUp_induction {α : Type}
    {P : Nat → α → Prop}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (hLo : lo ≤ hi)
    (hInit : P lo init)
    (hStep : ∀ i a hLe hLt, P i a → P (i + 1) (step i hLe hLt a)) :
    P hi (forRangeUp lo hi init step) := by
  generalize hd : hi - lo = d
  induction d generalizing lo init step with
  | zero =>
    have h_eq : lo = hi := by omega
    have h_rw : forRangeUp lo hi init step = init := forRangeUp_eq_init_of_ge _ _ _ _ (by omega)
    rw [h_rw]
    subst h_eq
    exact hInit
  | succ d ih =>
    have h_lt : lo < hi := by omega
    have h_rw : forRangeUp lo hi init step = _ := forRangeUp_step_of_lt _ _ _ _ h_lt
    rw [h_rw]
    refine ih (lo + 1) (step lo (Nat.le_refl lo) h_lt init) (fun i hlo hhi a => step i (Nat.le_trans (Nat.le_succ lo) hlo) hhi a) ?_ ?_ ?_ ?_
    · omega
    · exact hStep lo init (Nat.le_refl lo) h_lt hInit
    · intro i a hLe hLt' hP
      exact hStep i a (Nat.le_trans (Nat.le_succ lo) hLe) hLt' hP
    · omega

theorem mirWpConverges_forRangeUp {α : Type}
    {body : CapturedMir} {LoopInv : Nat → α → MachineState → Prop}
    {lo hi : Nat} (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    {s : MachineState} {post : MirOutcome → Prop}
    (hInit : LoopInv lo init s)
    (hStep : ∀ i a s' hLe hLt, LoopInv i a s' → ∃ sNext, MirReachState body s' sNext ∧ LoopInv (i + 1) (step i hLe hLt a) sNext)
    (hExit : ∀ i a s', i ≥ hi → LoopInv i a s' → MirWpConverges body s' post) :
    MirWpConverges body s post := by
  generalize hd : hi - lo = d
  induction d generalizing lo init step s with
  | zero =>
    have h_ge : lo ≥ hi := Nat.le_of_sub_eq_zero hd
    exact hExit lo init s h_ge hInit
  | succ d ih =>
    have h_lt : lo < hi := by omega
    rcases hStep lo init s (Nat.le_refl lo) h_lt hInit with ⟨sNext, h_reach, h_inv_next⟩
    have h_reach_mono : MirStepsConverges body s (· = sNext) post :=
      MirStepsConverges.mono (fun _ h => h) (fun _ h => False.elim h) h_reach
    refine MirWpConverges.bind h_reach_mono ?_
    intro s' h_eq
    subst h_eq
    refine ih (step lo (Nat.le_refl lo) h_lt init)
      (fun i hlo hhi a => step i (Nat.le_trans (Nat.le_succ lo) hlo) hhi a)
      h_inv_next ?_ ?_
    · intro i a s' hLe hLt hInv
      exact hStep i a s' (Nat.le_trans (Nat.le_succ lo) hLe) hLt hInv
    · omega

def whileRank {α : Type} (init : α) (hRank : α → Nat)
    (step : (a : α) → 0 < hRank a → α)
    (hRankDec : ∀ a h, hRank (step a h) < hRank a) : α :=
  if h : 0 < hRank init then
    whileRank (step init h) hRank step hRankDec
  else
    init
termination_by hRank init
decreasing_by exact hRankDec init h

theorem mirWpConverges_whileRank_aux {α : Type}
    {body : CapturedMir} {LoopInv : α → MachineState → Prop}
    (init : α) (hRank : α → Nat)
    (step : (a : α) → 0 < hRank a → α)
    (hRankDec : ∀ a h, hRank (step a h) < hRank a)
    {s : MachineState} {post : MirOutcome → Prop}
    (hInit : LoopInv init s)
    (hStep : ∀ a s' hLt, LoopInv a s' → ∃ sNext, MirReachState body s' sNext ∧ LoopInv (step a hLt) sNext)
    (hExit : ∀ a s', hRank a = 0 → LoopInv a s' → MirWpConverges body s' post)
    (d : Nat) (hd : hRank init ≤ d) :
    MirWpConverges body s post := by
  induction d generalizing init s with
  | zero =>
    have h_eq : hRank init = 0 := by omega
    exact hExit init s h_eq hInit
  | succ d ih =>
    by_cases h_z : hRank init = 0
    · exact hExit init s h_z hInit
    · have h_lt : 0 < hRank init := Nat.pos_of_ne_zero h_z
      rcases hStep init s h_lt hInit with ⟨sNext, h_reach, h_inv_next⟩
      have h_reach_mono : MirStepsConverges body s (· = sNext) post :=
        MirStepsConverges.mono (fun _ h => h) (fun _ h => False.elim h) h_reach
      refine MirWpConverges.bind h_reach_mono ?_
      intro s' h_eq
      subst h_eq
      have h_dec := hRankDec init h_lt
      refine ih (step init h_lt) h_inv_next ?_
      omega

theorem mirWpConverges_whileRank {α : Type}
    {body : CapturedMir} {LoopInv : α → MachineState → Prop}
    (init : α) (hRank : α → Nat)
    (step : (a : α) → 0 < hRank a → α)
    (hRankDec : ∀ a h, hRank (step a h) < hRank a)
    {s : MachineState} {post : MirOutcome → Prop}
    (hInit : LoopInv init s)
    (hStep : ∀ a s' hLt, LoopInv a s' → ∃ sNext, MirReachState body s' sNext ∧ LoopInv (step a hLt) sNext)
    (hExit : ∀ a s', hRank a = 0 → LoopInv a s' → MirWpConverges body s' post) :
    MirWpConverges body s post :=
  mirWpConverges_whileRank_aux init hRank step hRankDec hInit hStep hExit (hRank init) (Nat.le_refl _)


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

private def mkMirBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultU32FnAbi
  layouts := { pointerBits := 64, isLittleEndian := true, entries := [] }
  allocations := []
}

private def constU32 (v : Nat) : Operand :=
  .constant { ty := Anneal.MirFuelFree.u32Ty, val := .scalar (.int ⟨v, 4⟩) }

def countTo10Body : CapturedMir :=
  mkMirBody "Anneal::MirLoops::countTo10" 0
      [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
      , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" } ]
      [ { statements :=
            [ { kind := .assign { local_ := 1, projection := [] } (.use (constU32 0)), span := "init" } ]
          terminator := { kind := .goto 1, span := "goto bb1" }
          isCleanup := false }
      , { statements := []
          terminator := { kind := .switchInt (.copy { local_ := 1, projection := [] }) { branches := [(10, 3)], otherwise := 2 }, span := "switch" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 1, projection := [] } (.binaryOp .add (.copy { local_ := 1, projection := [] }) (constU32 1)), span := "add" } ]
          terminator := { kind := .goto 1, span := "goto bb1" }
          isCleanup := false }
      , { statements := [ { kind := .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 1, projection := [] })), span := "ret_assign" } ]
          terminator := { kind := .return_, span := "ret" }
          isCleanup := false }
      ]

def countState (bb : Nat) (i : Nat) : MachineState :=
  {
    frame := {
      blockIdx := bb,
      stmtIdx := 0,
      locals := [
        .init (.scalar ⟨0, 4⟩),
        .init (.scalar ⟨i, 4⟩)
      ]
    },
    memory := {}
  }

theorem bb0_converges :
    MirReachState countTo10Body (countState 0 0)
      (countState 1 0) := by
  apply MirStepsConverges.step
  apply MirStepsConverges.step
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_lt (i : Nat) (h : i < 10) :
    MirReachState countTo10Body (countState 1 i)
      (countState 2 i) := by
  apply MirStepsConverges.step
  have h_ne : i ≠ 10 := by omega
  have h_beq : i.beq 10 = false := by
    cases hc : i.beq 10
    · rfl
    · have h_eq : i = 10 := Nat.eq_of_beq_eq_true hc
      omega
  have h_tree : stepMirSymTree countTo10Body (countState 1 i) = 
    SymTree.branch (i.beq 10) 
      (SymTree.leaf (.vis (.inr (.inl (.emit (.event i)))) (fun _ => MirExecState.running (countState 3 i))))
      (SymTree.leaf (.vis (.inr (.inl (.emit (.event i)))) (fun _ => MirExecState.running (countState 2 i)))) := by rfl
  rw [h_tree]
  dsimp [evalSymNodeTreeNoCall]
  rw [h_beq]
  dsimp [evalSymNodeTreeNoCall]
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_eq10 :
    MirReachState countTo10Body (countState 1 10)
      (countState 3 10) := by
  apply MirStepsConverges.step
  have h_tree : stepMirSymTree countTo10Body (countState 1 10) = 
    SymTree.branch ((10 : Nat).beq 10) 
      (SymTree.leaf (.vis (.inr (.inl (.emit (.event 10)))) (fun _ => MirExecState.running (countState 3 10))))
      (SymTree.leaf (.vis (.inr (.inl (.emit (.event 10)))) (fun _ => MirExecState.running (countState 2 10)))) := by rfl
  rw [h_tree]
  dsimp [evalSymNodeTreeNoCall]
  apply MirStepsConverges.refl
  rfl

theorem bb2_converges (i : Nat) :
    MirReachState countTo10Body (countState 2 i)
      (countState 1 (wrapScalarBits (i + 1) 4294967296)) := by
  apply MirStepsConverges.step
  apply MirStepsConverges.step
  apply MirStepsConverges.refl
  rfl

theorem bb3_converges (i : Nat) :
    MirWpConverges countTo10Body (countState 3 i)
      (fun out => out = .normal (.scalar ⟨i, 4⟩, {})) := by
  apply MirWpConverges.step
  apply MirWpConverges.step
  rfl

def loopInv (i : Nat) (_ : Unit) (s : MachineState) : Prop :=
  i ≤ 10 ∧ s = countState 1 i

theorem countTo10_terminates :
    MirWpConverges countTo10Body (countState 0 0)
      (fun out => out = .normal (.scalar ⟨10, 4⟩, {})) := by
  apply MirWpConverges.bind_reachState bb0_converges
  
  apply mirWpConverges_forRangeUp (LoopInv := loopInv) (lo := 0) (hi := 10) (init := ()) (step := fun _ _ _ _ => ())
  · exact ⟨by omega, rfl⟩
  · intro i a s' hLe hLt hInv
    rcases hInv with ⟨hi10, h_eq⟩
    subst h_eq
    have h1 := bb1_converges_lt i hLt
    have h2 := bb2_converges i
    have h_wrap : wrapScalarBits (i + 1) 4294967296 = i + 1 := by
      dsimp [wrapScalarBits]
      cases hc : Nat.ble 4294967296 (i + 1)
      · rfl
      · have : 4294967296 ≤ i + 1 := Nat.le_of_ble_eq_true hc
        omega
    rw [h_wrap] at h2
    have h_reach : MirReachState countTo10Body (countState 1 i) (countState 1 (i + 1)) := by
      exact MirReachState.trans h1 h2
    exact ⟨countState 1 (i + 1), h_reach, ⟨by omega, rfl⟩⟩
  · intro i a s' hGe hInv
    rcases hInv with ⟨hLe, h_eq⟩
    subst h_eq
    have h_eq10 : i = 10 := by omega
    subst h_eq10
    have h1 := bb1_converges_eq10
    have h3 := bb3_converges 10
    apply MirWpConverges.bind_reachState h1
    exact h3


end Anneal.MirLoops
