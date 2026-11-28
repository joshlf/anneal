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
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence

namespace Anneal.MirLoops

def forRangeUp {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo < hi then
    forRangeUp (lo + 1) hi (step lo (Nat.le_refl _) h init) (fun i h_le h_lt a => step i (Nat.le_trans (Nat.le_succ _) h_le) h_lt a)
  else
    init
termination_by hi - lo

@[simp]
theorem forRangeUp_eq_init_of_ge {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α) (h : hi ≤ lo) :
    forRangeUp lo hi init step = init := by
  rw [forRangeUp]
  split
  · next h_lt => exact False.elim (Nat.not_lt_of_le h h_lt)
  · rfl

theorem forRangeUp_step_of_lt {α : Type} (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α) (h : lo < hi) :
    forRangeUp lo hi init step = forRangeUp (lo + 1) hi (step lo (Nat.le_refl _) h init) (fun i h_le h_lt a => step i (Nat.le_trans (Nat.le_succ _) h_le) h_lt a) := by
  rw [forRangeUp]
  split
  · rfl
  · next h_not_lt => exact False.elim (h_not_lt h)

theorem forRangeUp_induction {α : Type}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (Inv : Nat → α → Prop)
    (h_le : lo ≤ hi)
    (h_init : Inv lo init)
    (h_step : ∀ i h_i_le h_i_lt a, Inv i a → Inv (i + 1) (step i h_i_le h_i_lt a)) :
    Inv hi (forRangeUp lo hi init step) := by
  if h : lo < hi then
    rw [forRangeUp_step_of_lt lo hi init step h]
    have h_next : Inv (lo + 1) (step lo (Nat.le_refl _) h init) := h_step lo (Nat.le_refl _) h init h_init
    exact forRangeUp_induction (lo + 1) hi (step lo (Nat.le_refl _) h init) _ Inv (Nat.succ_le_of_lt h) h_next (fun i h_i_le h_i_lt a h_inv => h_step i (Nat.le_trans (Nat.le_succ _) h_i_le) h_i_lt a h_inv)
  else
    have h_eq : lo = hi := Nat.le_antisymm h_le (Nat.le_of_not_lt h)
    subst h_eq
    rw [forRangeUp_eq_init_of_ge _ _ _ _ (Nat.le_refl _)]
    exact h_init
termination_by hi - lo

/--
  Proves that a MIR loop representing `for i in lo..hi` converges.
  The invariant `LoopInv` is parameterized by the loop counter `i` and accumulated trace.
  If the loop terminates (when `i >= hi`), the exit condition determines the final postcondition.
-/
theorem mirTraceWpConverges_forRangeUp {α : Type}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (body : CapturedMir)
    (LoopInv : Nat → α → MachineState → List (Event MirEffect) → Prop)
    (s₀ : MachineState) (tr₀ : List (Event MirEffect))
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (h_init : LoopInv lo init s₀ tr₀)
    (h_body : ∀ i h_i_le h_i_lt a s tr, LoopInv i a s tr →
      MirTraceStepsConverges body s
        (fun s' tr_step => LoopInv (i + 1) (step i h_i_le h_i_lt a) s' (tr ++ tr_step))
        (fun tr_out out => post (tr ++ tr_out) out))
    (h_exit : ∀ i a s tr, i ≥ hi → LoopInv i a s tr → MirTraceWpConverges body s (fun tr_rest out => post (tr ++ tr_rest) out)) :
    MirTraceWpConverges body s₀ (fun tr_rest out => post (tr₀ ++ tr_rest) out) := by
  generalize h_d : hi - lo = d
  induction d generalizing lo init step s₀ tr₀ with
  | zero =>
    have h_ge : lo ≥ hi := Nat.le_of_sub_eq_zero h_d
    exact h_exit lo init s₀ tr₀ h_ge h_init
  | succ d ih =>
    have h_lt : lo < hi := Nat.lt_of_sub_eq_succ h_d
    have h_le : lo ≤ hi := Nat.le_of_lt h_lt
    have h_step_conv := h_body lo (Nat.le_refl _) h_lt init s₀ tr₀ h_init
    apply MirTraceWpConverges.bind h_step_conv
    intro s' tr_step h_mid
    have h_sub : hi - (lo + 1) = d := by omega
    have h_ih := ih (lo + 1) (step lo (Nat.le_refl _) h_lt init)
      (fun i h_le' h_lt' a => step i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a)
      s' (tr₀ ++ tr_step)
      h_mid
      (fun i h_le' h_lt' a s tr h_inv => by
        have h_body' := h_body i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a s tr h_inv
        exact h_body')
      h_sub
    have h_post_eq : (fun tr_rest out => post (tr₀ ++ tr_step ++ tr_rest) out) = (fun tr_rest out => post (tr₀ ++ (tr_step ++ tr_rest)) out) := by
      funext tr_rest out
      rw [List.append_assoc]
    rw [h_post_eq] at h_ih
    exact h_ih

theorem nat_strong_induction (P : Nat → Prop) (ind : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  intro n
  have aux : ∀ m, m ≤ n → P m := by
    induction n with
    | zero =>
      intro m hm
      have h_eq : m = 0 := Nat.le_zero.mp hm
      subst h_eq
      exact ind 0 (fun k hk => nomatch hk)
    | succ n ih =>
      intro m hm
      if h_eq : m = n + 1 then
        subst h_eq
        exact ind (n + 1) (fun k hk => ih k (Nat.le_of_lt_succ hk))
      else
        have h_lt : m < n + 1 := Nat.lt_of_le_of_ne hm h_eq
        exact ih m (Nat.le_of_lt_succ h_lt)
  exact aux n (Nat.le_refl _)

/--
  Proves convergence of a general `while` loop with trace accumulation using a well-founded ranking function.
  The ranking function `rank : α → Nat` must strictly decrease on every iteration.
-/
theorem mirTraceWpConverges_whileRank {α : Type}
    (rank : α → Nat)
    (body : CapturedMir)
    (LoopInv : α → MachineState → List (Event MirEffect) → Prop)
    (s₀ : MachineState) (tr₀ : List (Event MirEffect))
    (a₀ : α)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (h_init : LoopInv a₀ s₀ tr₀)
    (h_step : ∀ a s tr, LoopInv a s tr →
      MirTraceStepsConverges body s
        (fun s' tr_step => ∃ a', LoopInv a' s' (tr ++ tr_step) ∧ rank a' < rank a)
        (fun tr_out out => post (tr ++ tr_out) out)) :
    MirTraceWpConverges body s₀ (fun tr_rest out => post (tr₀ ++ tr_rest) out) := by
  have h_gen : ∀ r a s tr, rank a = r → LoopInv a s tr → MirTraceWpConverges body s (fun tr_rest out => post (tr ++ tr_rest) out) := by
    apply nat_strong_induction (fun r => ∀ a s tr, rank a = r → LoopInv a s tr → MirTraceWpConverges body s (fun tr_rest out => post (tr ++ tr_rest) out))
    intro r ih a s tr h_eq h_inv
    have h_step_conv := h_step a s tr h_inv
    apply MirTraceWpConverges.bind h_step_conv
    intro s' tr_step h_mid
    rcases h_mid with ⟨a', h_inv', h_lt⟩
    have h_sub : rank a' < r := by omega
    have h_ih := ih (rank a') h_sub a' s' (tr ++ tr_step) rfl h_inv'
    have h_post_eq : (fun tr_rest out => post (tr ++ tr_step ++ tr_rest) out) = (fun tr_rest out => post (tr ++ (tr_step ++ tr_rest)) out) := by
      funext tr_rest out
      rw [List.append_assoc]
    rw [h_post_eq] at h_ih
    exact h_ih
  exact h_gen (rank a₀) a₀ s₀ tr₀ rfl h_init

theorem runMirToBlock_eq_target
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s sOut : MachineState}
    (h : runMirToBlock fuel body targetBlock s = some sOut) :
    sOut.frame.blockIdx = targetBlock ∧ sOut.frame.stmtIdx = 0 := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirToBlock at h
    split at h
    · injection h with h_eq
      subst h_eq
      rename_i h_and
      have h1 : s.frame.blockIdx = targetBlock := by
        exact Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ |>.mp h_and).1
      have h2 : s.frame.stmtIdx = 0 := by
        exact Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ |>.mp h_and).2
      exact ⟨h1, h2⟩
    · cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis ef k =>
        simp only [h_step] at h
        cases ef with
        | inl inl_ef => nomatch h
        | inr inr_ef => cases inr_ef with
          | inl inl_inr_ef => cases inl_inr_ef with
            | emit ev =>
              cases h_k : k PUnit.unit with
              | running s_next =>
                simp only [h_k] at h
                exact ih h
              | halted _ => simp only [h_k] at h; nomatch h
              | faulted _ => simp only [h_k] at h; nomatch h
          | inr _ => nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ => exact ih h
        | halted _ => nomatch h
        | faulted _ => nomatch h

/--
  Pure variant of `mirTraceWpConverges_forRangeUp` without trace accumulation.
  Proves convergence of a bounded range loop in MIR by well-founded induction on `hi - i`.
-/
theorem mirWpConverges_forRangeUp {α : Type}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (body : CapturedMir)
    (LoopInv : Nat → α → MachineState → Prop)
    (s₀ : MachineState)
    (post : MirOutcome → Prop)
    (h_init : LoopInv lo init s₀)
    (h_body : ∀ i h_i_le h_i_lt a s, LoopInv i a s →
      MirStepsConverges body s
        (fun s' => LoopInv (i + 1) (step i h_i_le h_i_lt a) s')
        (fun _ => False))
    (h_exit : ∀ i a s, i ≥ hi → LoopInv i a s → MirWpConverges body s post) :
    MirWpConverges body s₀ post := by
  generalize h_d : hi - lo = d
  induction d generalizing lo init step s₀ with
  | zero =>
    have h_ge : lo ≥ hi := Nat.le_of_sub_eq_zero h_d
    exact h_exit lo init s₀ h_ge h_init
  | succ d ih =>
    have h_lt : lo < hi := Nat.lt_of_sub_eq_succ h_d
    have h_step_conv := h_body lo (Nat.le_refl _) h_lt init s₀ h_init
    have h_step_mono := MirStepsConverges.mono (post₂ := post) (fun _ h => h) (fun _ h => False.elim h) h_step_conv
    apply MirWpConverges.bind h_step_mono
    intro s' h_mid
    have h_sub : hi - (lo + 1) = d := by omega
    exact ih (lo + 1) (step lo (Nat.le_refl _) h_lt init)
      (fun i h_le' h_lt' a => step i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a)
      s'
      h_mid
      (fun i h_le' h_lt' a s h_inv => h_body i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a s h_inv)
      h_sub

/--
Call-forbidding (`MirNoCallWpConverges`) variant of `mirWpConverges_forRangeUp`,
suitable for `verifyStatefulEquivMir_of_wpConverges`.
-/
theorem mirNoCallWpConverges_forRangeUp {α : Type}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (body : CapturedMir)
    (LoopInv : Nat → α → MachineState → Prop)
    (s₀ : MachineState)
    (post : MirOutcome → Prop)
    (h_init : LoopInv lo init s₀)
    (h_body : ∀ i h_i_le h_i_lt a s, LoopInv i a s →
      MirStepsConverges body s
        (fun s' => LoopInv (i + 1) (step i h_i_le h_i_lt a) s')
        (fun _ => False))
    (h_exit : ∀ i a s, i ≥ hi → LoopInv i a s →
      MirNoCallWpConverges body s post) :
    MirNoCallWpConverges body s₀ post := by
  generalize h_d : hi - lo = d
  induction d generalizing lo init step s₀ with
  | zero =>
    have h_ge : lo ≥ hi := Nat.le_of_sub_eq_zero h_d
    exact h_exit lo init s₀ h_ge h_init
  | succ d ih =>
    have h_lt : lo < hi := Nat.lt_of_sub_eq_succ h_d
    have h_step_conv := h_body lo (Nat.le_refl _) h_lt init s₀ h_init
    have h_step_mono :=
      MirStepsConverges.mono (post₂ := post) (fun _ h => h)
        (fun _ h => False.elim h) h_step_conv
    apply MirNoCallWpConverges.bind h_step_mono
    intro s' h_mid
    have h_sub : hi - (lo + 1) = d := by omega
    exact ih (lo + 1) (step lo (Nat.le_refl _) h_lt init)
      (fun i h_le' h_lt' a =>
        step i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a)
      s'
      h_mid
      (fun i h_le' h_lt' a s h_inv =>
        h_body i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a s h_inv)
      h_sub

/--
  Proves convergence of a general `while` loop using a well-founded ranking function.
  The ranking function `rank : α → Nat` must strictly decrease on every iteration.
-/
theorem mirWpConverges_whileRank {α : Type}
    (rank : α → Nat)
    (body : CapturedMir)
    (LoopInv : α → MachineState → Prop)
    (s₀ : MachineState)
    (a₀ : α)
    (post : MirOutcome → Prop)
    (h_init : LoopInv a₀ s₀)
    (h_step : ∀ a s, LoopInv a s →
      MirStepsConverges body s
        (fun s' => ∃ a', LoopInv a' s' ∧ rank a' < rank a)
        post) :
    MirWpConverges body s₀ post := by
  have h_gen : ∀ r a s, rank a = r → LoopInv a s → MirWpConverges body s post := by
    apply nat_strong_induction (fun r => ∀ a s, rank a = r → LoopInv a s → MirWpConverges body s post)
    intro r ih a s h_eq h_inv
    have h_step_conv := h_step a s h_inv
    apply MirWpConverges.bind h_step_conv
    intro s' h_mid
    rcases h_mid with ⟨a', h_inv', h_lt⟩
    have h_sub : rank a' < r := by omega
    exact ih (rank a') h_sub a' s' rfl h_inv'
  exact h_gen (rank a₀) a₀ s₀ rfl h_init


/--
  Merges two divergent control flow paths (e.g. from a SwitchInt) into a single join block.
  Proves convergence of the merged path without exposing branch-specific fuel to the caller.
-/
theorem wpTransPlanConverges
    {body : CapturedMir}
    {s₀ sThen₀ sElse₀ sThenJoin sElseJoin : MachineState}
    {cond : Bool}
    {fuelThen fuelElse bits : Nat}
    {joinBb : BasicBlockIdx}
    {post : MirOutcome → Prop}
    (h_sw : runMirToBinarySwitch 1 body s₀ = some (cond, bits, sThen₀, sElse₀))
    (h_then : runMirToBlock fuelThen body joinBb sThen₀ = some sThenJoin)
    (h_else : runMirToBlock fuelElse body joinBb sElse₀ = some sElseJoin)
    (h_len : sThenJoin.frame.locals.length = sElseJoin.frame.locals.length)
    (h_mem : sThenJoin.memory = sElseJoin.memory)
    (h_join : MirWpConverges body
      { frame := {
          blockIdx := joinBb
          stmtIdx := 0
          locals := zipLocalSlots cond sThenJoin.frame.locals sElseJoin.frame.locals
        }
        memory := sThenJoin.memory }
      post) :
    MirWpConverges body s₀ post := by
  have h_sw_conv := MirStepsConverges.of_runMirToBinarySwitch (post := fun _ => False) h_sw
  have h_sw_mono := MirStepsConverges.mono (mid₂ := fun x => x = if cond then sThen₀ else sElse₀) (post₂ := post)
    (fun s_mid h_mid => h_mid)
    (fun out h_false => nomatch h_false)
    h_sw_conv
  apply MirWpConverges.bind h_sw_mono
  intro s' h_mid
  if h_cond : cond = true then
    have h_mid_then : s' = sThen₀ := by rw [h_cond] at h_mid; exact h_mid
    cases h_mid_then
    have h_then_conv := MirStepsConverges.of_runMirToBlock (post := fun _ => False) h_then
    have h_then_mono := MirStepsConverges.mono (mid₂ := fun x => x = sThenJoin) (post₂ := post)
      (fun s_mid h_mid => h_mid)
      (fun out h_false => nomatch h_false)
      h_then_conv
    apply MirWpConverges.bind h_then_mono
    intro s_join h_join_mid
    cases h_join_mid
    rw [h_cond] at h_join
    rw [zipLocalSlots_eq_ite true h_len] at h_join
    have ⟨h_blk, h_stmt⟩ := runMirToBlock_eq_target h_then
    have h_eq : sThenJoin = ({ frame := { blockIdx := joinBb, stmtIdx := 0, locals := sThenJoin.frame.locals }, memory := sThenJoin.memory } : MachineState) := by
      cases h_sThenJoin : sThenJoin with | mk frame memory =>
      cases h_frame : frame with | mk blockIdx stmtIdx locals =>
      subst h_sThenJoin h_frame
      dsimp at h_blk h_stmt
      subst h_blk h_stmt
      rfl
    rw [h_eq]
    exact h_join
  else
    have h_cond_false : cond = false := by cases cond; rfl; cases h_cond rfl
    have h_mid_else : s' = sElse₀ := by rw [h_cond_false] at h_mid; exact h_mid
    cases h_mid_else
    have h_else_conv := MirStepsConverges.of_runMirToBlock (post := fun _ => False) h_else
    have h_else_mono := MirStepsConverges.mono (mid₂ := fun x => x = sElseJoin) (post₂ := post)
      (fun s_mid h_mid => h_mid)
      (fun out h_false => nomatch h_false)
      h_else_conv
    apply MirWpConverges.bind h_else_mono
    intro s_join h_join_mid
    cases h_join_mid
    rw [h_cond_false] at h_join
    rw [zipLocalSlots_eq_ite false h_len] at h_join
    have ⟨h_blk, h_stmt⟩ := runMirToBlock_eq_target h_else
    have h_eq : sElseJoin = ({ frame := { blockIdx := joinBb, stmtIdx := 0, locals := sElseJoin.frame.locals }, memory := sElseJoin.memory } : MachineState) := by
      cases h_sElseJoin : sElseJoin with | mk frame memory =>
      cases h_frame : frame with | mk blockIdx stmtIdx locals =>
      subst h_sElseJoin h_frame
      dsimp at h_blk h_stmt
      subst h_blk h_stmt
      rfl
    have h_mem_eq : sThenJoin.memory = sElseJoin.memory := h_mem
    rw [h_mem_eq] at h_join
    rw [h_eq]
    exact h_join


theorem runMirTauToBlock_eq_target
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s sOut : MachineState}
    (h : runMirTauToBlock fuel body targetBlock s = some sOut) :
    sOut.frame.blockIdx = targetBlock ∧ sOut.frame.stmtIdx = 0 := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirTauToBlock at h
    split at h
    · injection h with h_eq
      subst h_eq
      next h_cond =>
        have h_cond_b := Bool.and_eq_true _ _ |>.mp h_cond
        have hb2 : s.frame.blockIdx = targetBlock := Nat.eq_of_beq_eq_true h_cond_b.1
        have hs2 : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_cond_b.2
        exact ⟨hb2, hs2⟩
    · cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis _ _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ => exact ih h
        | halted _ => nomatch h
        | faulted _ => nomatch h

theorem MirTraceStepsConverges_of_runMirToBinarySwitch
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {cond : Bool} {bits : Nat} {sThen sElse : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse)) :
    MirTraceStepsConverges body s (fun s₁ tr => s₁ = (if cond = true then sThen else sElse) ∧ tr = [⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩]) post := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirToBinarySwitch at h
    cases h_sw : inspectBinarySwitch body s with
    | some res =>
      rw [h_sw] at h
      injection h with h_eq
      subst h_eq
      have h_step := stepMirFn_of_inspectBinarySwitch h_sw
      have h_next : MirTraceStepsConverges body (if cond = true then sThen else sElse)
        (fun s'' tr₂ =>
          (s'' = (if cond = true then sThen else sElse)) ∧
          [⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩] ++ tr₂ = [⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩])
        (fun tr₂ out => post ([⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩] ++ tr₂) out) := by
        apply MirTraceStepsConverges.refl
        exact ⟨rfl, rfl⟩
      exact MirTraceStepsConverges.step_emit h_step h_next
    | none =>
      rw [h_sw] at h
      cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis _ _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ =>
          have h_ih := ih h
          exact MirTraceStepsConverges.step_tau h_step h_ih
        | halted _ => nomatch h
        | faulted _ => nomatch h

/--
  Trace-accumulating variant of `wpTransPlanConverges`.
  Merges two divergent control flow paths from a BinarySwitch into a single join block,
  while properly appending the `.emit` event of the switch evaluation to the execution trace.
-/
theorem mirTraceWpConverges_wpTransPlanConverges
    {body : CapturedMir}
    {s₀ sThen₀ sElse₀ sThenJoin sElseJoin : MachineState}
    {cond : Bool}
    {fuelThen fuelElse bits : Nat}
    {joinBb : BasicBlockIdx}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h_sw : runMirToBinarySwitch 1 body s₀ = some (cond, bits, sThen₀, sElse₀))
    (h_then : runMirTauToBlock fuelThen body joinBb sThen₀ = some sThenJoin)
    (h_else : runMirTauToBlock fuelElse body joinBb sElse₀ = some sElseJoin)
    (h_len : sThenJoin.frame.locals.length = sElseJoin.frame.locals.length)
    (h_mem : sThenJoin.memory = sElseJoin.memory)
    (h_join : MirTraceWpConverges body
      { frame := {
          blockIdx := joinBb
          stmtIdx := 0
          locals := zipLocalSlots cond sThenJoin.frame.locals sElseJoin.frame.locals
        }
        memory := sThenJoin.memory }
      (fun tr_rest out => post ([⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩] ++ tr_rest) out)) :
    MirTraceWpConverges body s₀ post := by
  have h_sw_conv := MirTraceStepsConverges_of_runMirToBinarySwitch (post := fun _ _ => False) h_sw
  have h_sw_mono := MirTraceStepsConverges.mono
    (mid₂ := fun x tr => x = (if cond = true then sThen₀ else sElse₀) ∧ tr = [⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩])
    (post₂ := post)
    (fun s_mid tr_mid h_mid => h_mid)
    (fun tr_out out h_false => nomatch h_false)
    h_sw_conv
  apply MirTraceWpConverges.bind h_sw_mono
  intro s' tr_sw h_mid
  rcases h_mid with ⟨h_s', h_tr_sw⟩
  subst h_s'
  cases h_cond : cond with
  | true =>
    simp
    have h_then_conv := MirTraceStepsConverges.of_runMirTauToBlock (post := fun tr_rest out => post (tr_sw ++ tr_rest) out) h_then
    have h_then_mono := MirTraceStepsConverges.mono
      (mid₂ := fun x tr => x = sThenJoin ∧ tr = [])
      (post₂ := fun tr_rest out => post (tr_sw ++ tr_rest) out)
      (fun s_mid tr_mid h_mid => h_mid)
      (fun tr_out out h_post => h_post)
      h_then_conv
    apply MirTraceWpConverges.bind_silent h_then_mono
    intro s_join h_join_mid
    subst s_join
    have h_eq : sThenJoin = ({ frame := { blockIdx := joinBb, stmtIdx := 0, locals := sThenJoin.frame.locals }, memory := sThenJoin.memory } : MachineState) := by
      have ⟨h_blk, h_stmt⟩ := runMirTauToBlock_eq_target h_then
      cases h_sThenJoin : sThenJoin
      rename_i frame memory
      cases h_frame : frame
      rename_i blockIdx stmtIdx locals
      subst h_sThenJoin h_frame
      dsimp at h_blk h_stmt
      subst h_blk h_stmt
      rfl
    rw [h_eq]
    rw [h_cond] at h_join
    rw [zipLocalSlots_eq_ite true h_len] at h_join
    simp at h_join
    rw [h_tr_sw]
    exact h_join
  | false =>
    simp
    have h_else_conv := MirTraceStepsConverges.of_runMirTauToBlock (post := fun tr_rest out => post (tr_sw ++ tr_rest) out) h_else
    have h_else_mono := MirTraceStepsConverges.mono
      (mid₂ := fun x tr => x = sElseJoin ∧ tr = [])
      (post₂ := fun tr_rest out => post (tr_sw ++ tr_rest) out)
      (fun s_mid tr_mid h_mid => h_mid)
      (fun tr_out out h_post => h_post)
      h_else_conv
    apply MirTraceWpConverges.bind_silent h_else_mono
    intro s_join h_join_mid
    subst s_join
    have h_eq : sElseJoin = ({ frame := { blockIdx := joinBb, stmtIdx := 0, locals := sElseJoin.frame.locals }, memory := sElseJoin.memory } : MachineState) := by
      have ⟨h_blk, h_stmt⟩ := runMirTauToBlock_eq_target h_else
      cases h_sElseJoin : sElseJoin
      rename_i frame memory
      cases h_frame : frame
      rename_i blockIdx stmtIdx locals
      subst h_sElseJoin h_frame
      dsimp at h_blk h_stmt
      subst h_blk h_stmt
      rfl
    have h_mem_eq : sThenJoin.memory = sElseJoin.memory := h_mem
    rw [h_eq]
    rw [h_cond] at h_join
    rw [zipLocalSlots_eq_ite false h_len] at h_join
    simp at h_join
    rw [h_mem_eq] at h_join
    rw [h_tr_sw]
    exact h_join

private def defaultU32TypeLayout : TypeLayout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive, variants := .single 0, isUninhabited := false }
private def defaultU32FnAbi : FnAbi := { args := [], ret := { layout := defaultU32TypeLayout, mode := .direct }, conv := .rust, canUnwind := false }

def mkMirBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks, phase := .runtimePostCleanup, role := .subject, fnAbi := defaultU32FnAbi, layouts := { pointerBits := 64, isLittleEndian := true, entries := [] }, allocations := []
}

def constU32 (v : Nat) : Operand := .constant { ty := Anneal.MirFuelFree.u32Ty, val := .scalar (.int ⟨v, 4⟩) }

/--
  A concrete MIR loop `countToN` CFG witness with a symbolic iteration bound `n`.
  This represents a `while (i != n) { i += 1 }` loop in MIR.
-/
def countToNBody (n : Nat) : CapturedMir :=
  mkMirBody "Anneal::MirLoops::countToN" 0
      [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
      , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" } ]
      [ { statements := [ { kind := .assign { local_ := 1, projection := [] } (.use (constU32 0)), span := "init" } ], terminator := { kind := .goto 1, span := "goto bb1" }, isCleanup := false }
      , { statements := [], terminator := { kind := .switchInt (.copy { local_ := 1, projection := [] }) { branches := [(n, 3)], otherwise := 2 }, span := "switch" }, isCleanup := false }
      , { statements := [ { kind := .assign { local_ := 1, projection := [] } (.binaryOp .add (.copy { local_ := 1, projection := [] }) (constU32 1)), span := "add" } ], terminator := { kind := .goto 1, span := "goto bb1" }, isCleanup := false }
      , { statements := [ { kind := .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 1, projection := [] })), span := "ret_assign" } ], terminator := { kind := .return_, span := "ret" }, isCleanup := false }
      ]

def countStateMem (bb : Nat) (stmt : Nat) (i : Nat) (mem : Memory) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [ .init (.scalar ⟨0, 4⟩), .init (.scalar ⟨i, 4⟩) ] }, memory := mem }

def countStateMemRet (bb : Nat) (stmt : Nat) (i : Nat) (mem : Memory) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [ .init (.scalar ⟨i, 4⟩), .init (.scalar ⟨i, 4⟩) ] }, memory := mem }

theorem bb0_converges_mem (n : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) :
    MirReachState (countToNBody n) (countStateMem 0 0 0 mem)
      (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
  have h_step : stepMirFn (countToNBody n) (countStateMem 0 0 0 mem) = MirStepNode.step (countStateMem 0 1 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?]
  have h_term : stepMirFn (countToNBody n) (countStateMem 0 1 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) = MirStepNode.step (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length]
  apply MirReachState.step_tau h_step
  apply MirReachState.step_tau h_term
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_lt (n : Nat) (i : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_lt : i ≠ n) :
    MirReachState (countToNBody n) (countStateMem 1 0 i mem)
      (countStateMem 2 0 i mem) := by
  have h_beq : Nat.beq i n = false := by exact (Bool.not_eq_true _).mp (by exact h_lt ∘ Nat.eq_of_beq_eq_true)
  have h_fn : stepMirFn (countToNBody n) (countStateMem 1 0 i mem) = MirStepNode.emitStep (.event i) (countStateMem 2 0 i mem) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, Trusted.Sequence.length, evalOperand, readProjectedValue, lookupSwitchTarget, h_beq]
  apply MirReachState.step_emit h_fn
  apply MirStepsConverges.refl
  rfl

theorem bb2_converges_mem (n : Nat) (i : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) :
    MirReachState (countToNBody n) (countStateMem 2 0 i mem)
      (countStateMem 1 0 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
  have h_step : stepMirFn (countToNBody n) (countStateMem 2 0 i mem) = MirStepNode.step (countStateMem 2 1 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?, placeTyResolved, placeTy, materializeReadPtrValue, validateValueForTy?]
  have h_term : stepMirFn (countToNBody n) (countStateMem 2 1 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) = MirStepNode.step (countStateMem 1 0 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length]
  apply MirReachState.step_tau h_step
  apply MirReachState.step_tau h_term
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_eqn (n : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) :
    MirReachState (countToNBody n) (countStateMem 1 0 n mem)
      (countStateMem 3 0 n mem) := by
  have h_fn : stepMirFn (countToNBody n) (countStateMem 1 0 n mem) = MirStepNode.emitStep (.event n) (countStateMem 3 0 n mem) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, Trusted.Sequence.length, evalOperand, readProjectedValue, lookupSwitchTarget]
  apply MirReachState.step_emit h_fn
  apply MirStepsConverges.refl
  rfl

theorem bb3_converges_mem (n : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) (h_stack : mem.callStack = []) :
    MirWpConverges (countToNBody n) (countStateMem 3 0 n mem)
      (fun out => out = Outcome.normal (Value.scalar ⟨n, 4⟩, { mem with borrows := disableFrameBorrows (invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack)) (length mem.callStack) 2 })) := by
  have h_step : stepMirFn (countToNBody n) (countStateMem 3 0 n mem) = MirStepNode.step (countStateMemRet 3 1 n { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack) }) := by
      unfold stepMirFn
      dsimp [countStateMem, countStateMemRet]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, readProjectedValue, evalRvalue, advanceStmt, Trusted.Sequence.set?, placeTyResolved, materializeReadPtrValue, validateValueForTy?]
  have h_term : stepMirFn (countToNBody n) (countStateMemRet 3 1 n { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack) }) = MirStepNode.retNormal (Value.scalar ⟨n, 4⟩) { mem with borrows := disableFrameBorrows (invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack)) (length mem.callStack) 2 } := by
      unfold stepMirFn
      dsimp [countStateMemRet]
      simp [Option.getD, countToNBody, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length, h_stack, hasFrameDeallocProtectorConflict]
  have h_wp_term : MirWpConverges (countToNBody n) (countStateMemRet 3 1 n { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack) }) (fun out => out = Outcome.normal (Value.scalar ⟨n, 4⟩, { mem with borrows := disableFrameBorrows (invalidateConflictingBorrows mem.borrows 0 none (length mem.callStack)) (length mem.callStack) 2 })) := by
      apply MirWpConverges.ret_of_step h_term
      rfl
  exact MirWpConverges.step_tau h_step h_wp_term

/--
  Proves that the concrete symbolic MIR loop `countToNBody n` converges to exactly `i = n`
  and returns `Outcome.normal n` natively inside the Lean kernel, without exposing fuel.
  This demonstrates that the structural loop combinator `mirWpConverges_forRangeUp` successfully
  abstracts unbounded iteration for arbitrary caller limits.
-/
theorem countToN_terminates (n : Nat) (hn : n < 4294967296) (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) (h_stack : mem.callStack = []) :
    MirWpConverges (countToNBody n) (countStateMem 0 0 0 mem)
      (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨n, 4⟩, mem')) := by
  have h0 := bb0_converges_mem n mem h_callee h_prot
  apply MirWpConverges.bind_reachState h0
  have h_loop : MirWpConverges (countToNBody n) (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) })
    (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨n, 4⟩, mem')) := by
    refine mirWpConverges_forRangeUp 0 n () (fun _ _ _ _ => ()) (countToNBody n)
      (fun i _ s => i ≤ n ∧ ∃ m, s = countStateMem 1 0 i m ∧ m.activeCallee = none ∧ m.activeProtectors = [] ∧ m.callStack = [])
      (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) })
      (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨n, 4⟩, mem'))
      ?_
      ?_
      ?_
    · exact ⟨Nat.zero_le n, { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none (length mem.callStack) }, rfl, h_callee, h_prot, h_stack⟩
    · intro i h_le h_lt _ s h_inv
      rcases h_inv with ⟨h_i_le_n, m, h_eq, hm_callee, hm_prot, hm_stack⟩
      subst h_eq
      have h1 := bb1_converges_lt n i m hm_callee (Nat.ne_of_lt h_lt)
      have h2 := bb2_converges_mem n i m hm_callee hm_prot
      have h12 := MirReachState.trans h1 h2
      have hi_mod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hi_mod] at h12
      exact MirStepsConverges.mono (post₂ := fun _ => False) (fun s' hs' => ⟨Nat.succ_le_of_lt h_lt, { m with borrows := invalidateConflictingBorrows m.borrows 1 none (length m.callStack) }, hs', hm_callee, hm_prot, hm_stack⟩) (fun _ h => False.elim h) h12
    · intro i a s h_ge h_inv
      rcases h_inv with ⟨h_i_le_n, m, h_eq, hm_callee, hm_prot, hm_stack⟩
      subst h_eq
      have h_i_eq : i = n := Nat.le_antisymm h_i_le_n h_ge
      cases h_i_eq
      have h1 := bb1_converges_eqn n m hm_callee
      have h3 := bb3_converges_mem n m hm_callee hm_prot hm_stack
      apply MirWpConverges.bind_reachState h1
      exact MirWpConverges.mono (fun out h => ⟨_, h⟩) h3
  exact h_loop

end Anneal.MirLoops

section MovedPureMirExecHelpers
set_option linter.all false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.MirLoops

def defaultSpecSteps (body : CapturedMir) : Nat :=
  Nat.add (Nat.mul (length body.basicBlocks) 16) 80

def defaultCfgSteps (body : CapturedMir) : Nat :=
  Nat.add (Nat.mul (length body.basicBlocks) 16) 40

structure Hold (P : Prop) : Prop where
  val : P

theorem get?_append_cons {α : Type u} (pfx rest : List α) (x : α) :
    get? (pfx ++ (x :: rest)) (length pfx) = some x := by
  simp [get?, length]

theorem get?_length_none {α : Type u} (xs : List α) :
    get? xs (length xs) = none := by
  simp [get?, length]

theorem length_append_singleton {α : Type u} (pfx : List α) (x : α) :
    length (pfx ++ [x]) = Nat.add (length pfx) 1 := by
  simp [length]

theorem scalarModulus_1 : scalarModulus 1 = 256 := rfl
theorem scalarModulus_2 : scalarModulus 2 = 65536 := rfl
theorem scalarModulus_4 : scalarModulus 4 = 4294967296 := rfl
theorem scalarModulus_8 : scalarModulus 8 = 18446744073709551616 := rfl
theorem mul_1_8 : Nat.mul 1 8 = 8 := rfl
theorem mul_2_8 : Nat.mul 2 8 = 16 := rfl
theorem mul_4_8 : Nat.mul 4 8 = 32 := rfl
theorem mul_8_8 : Nat.mul 8 8 = 64 := rfl
theorem mod_1_2 : 1 % 2 = 1 := rfl
theorem bitwiseAndBits_8_1_0 : bitwiseAndBits 8 1 0 = 0 := rfl
theorem bitwiseAndBits_one_one : bitwiseAndBits 8 1 1 = 1 := rfl
theorem bitwiseAndBits_one_zero : bitwiseAndBits 8 1 0 = 0 := rfl

theorem eq_zero_or_one_of_mod2_eq {x a : Nat} (h : x = a % 2) :
    x = 0 ∨ x = 1 := by omega

theorem beq_mod2_zero_of_odd {a : Nat} (h : a % 2 = 1) :
    Nat.beq (a % 2) 0 = false := by
  rw [h]; rfl

theorem beq_mod2_zero_of_not_odd {a : Nat} (h : ¬ a % 2 = 1) :
    Nat.beq (a % 2) 0 = true := by
  have h0 : a % 2 = 0 := by omega
  rw [h0]; rfl

theorem eq_one_of_zero_or_one_and_odd {a : Nat}
    (h1 : a = 0 ∨ a = 1) (h2 : a % 2 = 1) : a = 1 := by omega

theorem eq_zero_of_zero_or_one_and_not_odd {a : Nat}
    (h1 : a = 0 ∨ a = 1) (h2 : ¬ a % 2 = 1) : a = 0 := by omega

theorem isBorrowProtected_nil (entry : BorrowEntry) :
    isBorrowProtected .nil entry = false := by
  unfold isBorrowProtected
  cases entry.protector <;> rfl

theorem hasProtectedWriteConflict_nil
    (borrows : List BorrowEntry)
    (targetLocal : LocalIdx)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    {targetFrameDepth : Nat} :
    hasProtectedWriteConflict borrows .nil targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict
    simp only [isBorrowProtected_nil, Bool.false_and, Bool.and_false]
    exact ih

theorem readProjectedValue_nil (locals : List LocalSlot) (sc : ScalarVal) :
    readProjectedValue locals (.scalar sc) [] = .ok (.scalar sc) := rfl

theorem readProjectedValue_field
    (locals : List LocalSlot) (vIdx : Nat) (fields : List Value)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) =
      match get? fields idx with
      | .some fieldVal => readProjectedValue locals fieldVal rest
      | .none => .ub := rfl

theorem readProjectedValue_index
    (locals : List LocalSlot) (fields : List Value)
    (idxLocal : LocalIdx) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => readProjectedValue locals elemVal rest
        | .none => .ub
      | _ => .ub := rfl

def evalOperandFallback (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : PlaceReadResult :=
  evalOperand locals op borrows globals layouts callerLocals localDecls callStack

def evalDerefGlobalFallback
    (globals : List CapturedAllocation) (ptrVal : ProvenancePtr) (sz : Nat)
    (locals : List LocalSlot) (restProj : List ProjectionElem)
    (layouts : LayoutTable) : PlaceReadResult :=
  match lookupGlobalAlloc globals ptrVal.allocId with
  | .some alloc =>
    evalGlobalDerefRead locals alloc ptrVal.offsetBytes sz restProj layouts .none
  | .none => .ub

def evalThinPtrElemDerefReadFallback
    (locals callerLocals : List LocalSlot) (entry : BorrowEntry)
    (ptrVal : ProvenancePtr) (restProj : List ProjectionElem) : PlaceReadResult :=
  match get? locals entry.targetLocal with
  | .some (.init targetRootVal) =>
    match resolveStackThinPtrTargetProj? locals targetRootVal entry ptrVal restProj with
    | .none => .ub
    | .some fullProj =>
      match readProjectedValue locals targetRootVal fullProj with
      | .ok fieldVal => .ok fieldVal locals
      | .ub => .ub
      | .unsupported => .unsupported
  | .some _ => .ub
  | .none =>
    match get? callerLocals entry.targetLocal with
    | .some (.init targetRootVal) =>
      match resolveStackThinPtrTargetProj? locals targetRootVal entry ptrVal restProj with
      | .none => .ub
      | .some fullProj =>
        match readProjectedValue locals targetRootVal fullProj with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
    | _ => .ub

def evalOperandFast (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect _ _ =>
      evalOperandFallback locals (.constant c) borrows globals body.layouts callerLocals localDecls
        callStack
    | .unevaluated _ => .unsupported
    | cv =>
      match evalConstValue cv c.ty globals body.layouts with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
      match localDecls, callStack with
      | .nil, _ :: _ =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals .nil callStack
      | .nil, .nil =>
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              let needsElemRes :=
                match entry.targetProjection with
                | .nil => false
                | pHead :: pTail =>
                  let norm :=
                    normalizeSubsliceProjections (stripTransparentProjections (pHead :: pTail))
                  match endsWithSubslice norm with
                  | true => true
                  | false => Bool.not (Nat.beq ptrVal.offsetBytes 0)
              match needsElemRes with
              | false =>
                match get? locals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let fullProj :=
                    match entry.targetProjection with
                    | .nil => restProj
                    | ph :: pt => ph :: appendProjections pt restProj
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match get? callerLocals entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              | true =>
                evalThinPtrElemDerefReadFallback locals callerLocals entry ptrVal restProj
          | .none => evalDerefGlobalFallback globals ptrVal sz locals restProj body.layouts
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead locals ptrVal ptrSz lenSc restProj borrows globals
            body.layouts callerLocals .none
        | .some (.init (.aggregate 0 (.scalar ptrSc :: .scalar lenSc :: .nil))) =>
          match Bool.and (Nat.beq lenSc.bits 0) (Bool.not (Nat.beq ptrSc.bits 0)) with
          | true =>
            evalSliceFatPtrDerefRead locals { allocId := 0, offsetBytes := ptrSc.bits }
              ptrSc.sizeBytes lenSc restProj borrows globals body.layouts callerLocals .none
          | false => .ub
        | _ => .ub
      | d :: ds, _ =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
    | .nil =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue locals rootVal .nil with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
      | d :: ds =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
    | _ =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue locals rootVal p.projection with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
      | d :: ds =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
  | .move p =>
    match p.projection with
    | .nil =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init v) =>
          match readProjectedValue locals v .nil with
          | .ok validVal =>
            match set? locals p.local_ .uninit with
            | .some locals' => .ok validVal locals'
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
      | d :: ds =>
        evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
    | .field idx ty :: rest =>
      match localDecls with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue locals rootVal (.field idx ty :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
      | d :: ds =>
        evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
    | _ =>
      evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals localDecls
        callStack

theorem evalOperandFast_eq (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandFast body locals op borrows globals callerLocals localDecls callStack =
      evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val <;> rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil =>
      cases localDecls <;> rfl
    | cons hd tl =>
      cases hd with
      | deref =>
        cases localDecls <;> cases callStack <;> rfl
      | field _ _ | downcast _ _ | index _ | constantIndex _ _ _ | subslice _ _ _
      | opaqueCast _ | unwrapUnsafeBinder _ =>
        cases localDecls with
        | nil =>
          dsimp only [evalOperandFast, evalOperand]
          cases get? locals loc with
          | none => rfl
          | some s =>
            cases s with
            | uninit | dead => rfl
            | init rootVal => rfl
        | cons d ds => rfl
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil =>
      cases localDecls <;> rfl
    | cons hd tl =>
      cases hd with
      | field idx ty =>
        cases localDecls with
        | nil =>
          dsimp only [evalOperandFast, evalOperand]
          cases get? locals loc with
          | none => rfl
          | some s =>
            cases s with
            | uninit | dead => rfl
            | init rootVal => rfl
        | cons d ds => rfl
      | deref | downcast _ _ | index _ | constantIndex _ _ _ | subslice _ _ _
      | opaqueCast _ | unwrapUnsafeBinder _ => rfl

def evalOperandWithBodyCastFast
    (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (bodyLocalDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : PlaceReadResult :=
  match operandIsLeadingOpaqueCastMove op with
  | true =>
    evalOperandFast body locals op borrows globals callerLocals bodyLocalDecls callStack
  | false =>
    evalOperandFast body locals op borrows globals callerLocals .nil callStack

theorem evalOperandWithBodyCastFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (bodyLocalDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandWithBodyCastFast body locals op borrows globals callerLocals bodyLocalDecls callStack =
      evalOperandWithBodyCast locals op borrows globals body.layouts callerLocals bodyLocalDecls callStack := by
  unfold evalOperandWithBodyCastFast evalOperandWithBodyCast
  cases operandIsLeadingOpaqueCastMove op <;> simp only [evalOperandFast_eq]

def evalOperandsFast
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandFast body locals op borrows globals callerLocals localDecls callStack with
    | .ok v locals₁ =>
      match evalOperandsFast body locals₁ rest borrows globals callerLocals localDecls callStack with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

theorem evalOperandsFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandsFast body locals ops borrows globals callerLocals localDecls callStack =
      evalOperands locals ops borrows globals body.layouts callerLocals localDecls callStack := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    change
      (match evalOperandFast body locals op borrows globals callerLocals localDecls callStack with
       | .ok v locals₁ =>
         match evalOperandsFast body locals₁ rest borrows globals callerLocals localDecls callStack with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported) =
      (match evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack with
       | .ok v locals₁ =>
         match evalOperands locals₁ rest borrows globals body.layouts callerLocals localDecls
             callStack with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported)
    rw [evalOperandFast_eq]
    cases evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack with
    | ok v locals₁ =>
      dsimp only
      rw [ih locals₁]
    | ub => rfl
    | unsupported => rfl

private theorem bitwiseAndBits_8_1_local (a : Nat) :
    bitwiseAndBits 8 a 1 = a % 2 := by
  rw [Anneal.Scalars.bitwiseAndBits_eq_land, Nat.and_one_is_mod]
  omega

def bitwiseAndBitsFast (numBits a b : Nat) : Nat :=
  match Nat.beq numBits 8, Nat.beq b 1 with
  | true, true => a % 2
  | _, _ => bitwiseAndBits numBits a b

theorem bitwiseAndBitsFast_eq (numBits a b : Nat) :
    bitwiseAndBitsFast numBits a b = bitwiseAndBits numBits a b := by
  unfold bitwiseAndBitsFast
  cases h1 : Nat.beq numBits 8 with
  | false => rfl
  | true =>
    cases h2 : Nat.beq b 1 with
    | false => rfl
    | true =>
      rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
      exact (bitwiseAndBits_8_1_local a).symm

def evalByteCastAfterOperand
    (body : CapturedMir)
    (op : Operand)
    (targetTy : Ty)
    (v : Value)
    (locals' : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  let rTargetTy := resolveTyWithLocalDecls body.localDecls body.layouts targetTy
  match tyByteSize body.localDecls body.layouts rTargetTy with
  | .none => .unsupported
  | .some dstSize =>
    match operandTy body.localDecls body.layouts op with
    | .some srcTy =>
      match resolveByteCastSrcTyAndSize body.localDecls body.layouts op srcTy with
      | .none => .unsupported
      | .some (rSrcTy, srcSize) =>
        match Nat.beq srcSize dstSize with
        | false => .unsupported
        | true =>
          let encodedOpt : Option (List AbstractByte) :=
            encodeByteCastSourceBytes body.layouts rSrcTy v
          match encodedOpt with
          | .none => .ub
          | .some bs =>
            match Nat.beq (length bs) dstSize with
            | false => .ub
            | true =>
              match decodeTypedValueFromBytes defaultCodecFuel body.layouts rTargetTy bs with
              | .some v' => .ok v' locals' mem
              | .none => .ub
    | .none =>
      match encodeUntypedValueToBytes defaultCodecFuel v with
      | .none => .unsupported
      | .some bs =>
        match Nat.beq (length bs) dstSize with
        | false => .unsupported
        | true =>
          match decodeTypedValueFromBytes defaultCodecFuel body.layouts rTargetTy bs with
          | .some v' => .ok v' locals' mem
          | .none => .ub

def evalRvalueFallback (locals : List LocalSlot) (rv : Rvalue)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  evalRvalue locals rv mem localDecls layouts

def evalRvalueFast
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok v locals' =>
      match validateLoadedValue body.layouts body.localDecls op v with
      | false => .ub
      | true =>
        match op, mem.borrows with
        | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | _, _ => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast ck op targetTy =>
    match ck with
    | .intToInt =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        match Nat.beq sc.sizeBytes 0 with
        | true => .unsupported
        | false =>
          match intCastTargetBytes targetTy.kind with
          | .some targetBytes =>
            let modulus := scalarModulus targetBytes
            let castedBits :=
              match operandIsSigned body.localDecls op body.layouts with
              | false => wrapScalarBits sc.bits modulus
              | true =>
                match Nat.ble targetBytes sc.sizeBytes with
                | true => wrapScalarBits sc.bits modulus
                | false => signExtendBits sc.bits sc.sizeBytes targetBytes
            .ok (.scalar ⟨castedBits, targetBytes⟩) locals' mem
          | .none => .unsupported
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .transmute =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok v locals' =>
        evalByteCastAfterOperand body op targetTy v locals' mem
    | _ => evalRvalueFallback locals (.cast ck op targetTy) mem body.localDecls body.layouts
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset =>
            evalScalarPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp lhs rhs
          | _ =>
            let lhsTy := operandTy body.localDecls body.layouts lhsOp
            let rhsTy := operandTy body.localDecls body.layouts rhsOp
            match Bool.or (isFloatOptTy lhsTy) (isFloatOptTy rhsTy) with
            | true =>
              evalFloatScalarBinOp op lhs rhs lhsTy rhsTy locals₂ mem
            | false =>
              let isSigned := operandIsSigned body.localDecls lhsOp body.layouts
              evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  body.localDecls
                  body.layouts
                  (layoutPointerBytes body.layouts)
                  ptrVal
                  sz
                  mem.callStack
              with
              | .some lhsAddrSc =>
                evalScalarBinOp op lhsAddrSc offsetSc locals₂ mem false
              | .none => .unsupported
            | false => .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                (layoutPointerBytes body.layouts)
                ptrVal
                sz
                mem.callStack
            with
            | .some rhsAddrSc =>
              evalScalarBinOp op lhsSc rhsAddrSc locals₂ mem false
            | .none => .unsupported
          | false => .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes body.layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                lhsPtr
                lhsSz
                mem.callStack,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                rhsPtr
                rhsSz
                mem.callStack
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOp op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .unsupported
          | false => .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          evalWidePtrAggregateRelBinOp
            op
            lhsOp
            lhsVar
            lhsFields
            rhsVar
            rhsFields
            locals₂
            mem
            body.localDecls
            body.layouts
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        evalUnaryNot sc (operandTy body.localDecls body.layouts op) locals' mem
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | _ => evalRvalueFallback locals (.unaryOp uop op) mem body.localDecls body.layouts
  | _ => evalRvalueFallback locals rv mem body.localDecls body.layouts

theorem evalRvalueFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueFast body locals rv mem =
      evalRvalue locals rv mem body.localDecls body.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | transmute =>
      dsimp only [evalRvalueFast, evalRvalue, evalByteCast]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

def evalRvalueSymTreeFast
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    SymTree RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok v locals' =>
      .leaf (match validateLoadedValue body.layouts body.localDecls op v with
      | false => .ub
      | true =>
        match op, mem.borrows with
        | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | _, _ => .ok v locals' mem)
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .ref bk p =>
    match bk, p.projection with
    | .shared, .nil =>
      match get? locals p.local_ with
      | .none => .leaf .ub
      | .some .dead => .leaf .ub
      | .some _ =>
        let tag := mem.nextTag
        let entry : BorrowEntry := {
          tag := tag
          targetLocal := p.local_
          targetProjection := .nil
          perm :=
            sharedBorrowPerm body.localDecls body.layouts
              { local_ := p.local_, projection := .nil }
          targetFrameDepth := length mem.callStack
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .leaf (.ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem')
    | _, _ => .leaf (evalRvalueFallback locals (.ref bk p) mem body.localDecls body.layouts)
  | .cast .transmute op targetTy =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
    | .ok v locals' =>
      .leaf (evalByteCastAfterOperand body op targetTy v locals' mem)
  | .aggregate ak ops =>
    match ak with
    | .tuple =>
      match evalOperandsFast body locals ops mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok vals locals' => .leaf (.ok (.aggregate 0 vals) locals' mem)
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.aggregate ak ops) mem body.localDecls body.layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset =>
            .leaf (evalScalarPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp lhs rhs)
          | _ =>
            let lhsTy := operandTy body.localDecls body.layouts lhsOp
            let rhsTy := operandTy body.localDecls body.layouts rhsOp
            match Bool.or (isFloatOptTy lhsTy) (isFloatOptTy rhsTy) with
            | true =>
              .leaf (evalFloatScalarBinOp op lhs rhs lhsTy rhsTy locals₂ mem)
            | false =>
              match op with
              | .bitAnd =>
                .branch (Nat.beq lhs.sizeBytes 0) (.leaf .unsupported)
                  (.branch (Nat.beq lhs.sizeBytes rhs.sizeBytes)
                    (.leaf
                      (.ok
                        (.scalar
                          ⟨bitwiseAndBitsFast (Nat.mul lhs.sizeBytes 8) lhs.bits rhs.bits,
                           lhs.sizeBytes⟩)
                        locals₂ mem))
                    (.leaf .unsupported))
              | .eq => evalScalarBinOpSymTree .eq lhs rhs locals₂ mem false
              | .ne => evalScalarBinOpSymTree .ne lhs rhs locals₂ mem false
              | _ =>
                let isSigned := operandIsSigned body.localDecls lhsOp body.layouts
                evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOpSymTree locals₂ mem body.localDecls body.layouts
              lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  body.localDecls
                  body.layouts
                  (layoutPointerBytes body.layouts)
                  ptrVal
                  sz
                  mem.callStack
              with
              | .some lhsAddrSc =>
                evalScalarBinOpSymTree op lhsAddrSc offsetSc locals₂ mem false
              | .none => .leaf .unsupported
            | false => .leaf .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                (layoutPointerBytes body.layouts)
                ptrVal
                sz
                mem.callStack
            with
            | .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsSc rhsAddrSc locals₂ mem false
            | .none => .leaf .unsupported
          | false => .leaf .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes body.layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                lhsPtr
                lhsSz
                mem.callStack,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                rhsPtr
                rhsSz
                mem.callStack
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .leaf .unsupported
          | false => .leaf .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          .leaf
            (evalWidePtrAggregateRelBinOp
              op
              lhsOp
              lhsVar
              lhsFields
              rhsVar
              rhsFields
              locals₂
              mem
              body.localDecls
              body.layouts)
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        evalUnaryNotSymTree sc (operandTy body.localDecls body.layouts op) locals' mem
      | .ok _ _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.unaryOp uop op) mem body.localDecls body.layouts)
  | _ => .leaf (evalRvalueFallback locals rv mem body.localDecls body.layouts)

theorem evalRvalueSymTreeFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueSymTreeFast body locals rv mem =
      evalRvalueSymTree locals rv mem body.localDecls body.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | ref bk p =>
    cases bk with
    | shared =>
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
        cases get? locals loc with
        | none => rfl
        | some slot => cases slot <;> rfl
      | cons hd _ => cases hd <;> rfl
    | _ => rfl
  | cast ck op targetTy =>
    cases ck with
    | transmute =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalueFallback,
        evalRvalue, evalByteCast]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
      rw [evalOperandsFast_eq]
      cases evalOperands locals ops mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v₂ locals₂ =>
        cases v with
        | scalar lhs =>
          cases v₂ with
          | scalar rhs =>
            cases op with
            | offset => rfl
            | _ =>
              dsimp only
              cases Bool.or (isFloatOptTy (operandTy body.localDecls body.layouts lhsOp))
                  (isFloatOptTy (operandTy body.localDecls body.layouts rhsOp)) with
              | true => rfl
              | false => simp only [evalScalarBinOpSymTree, bitwiseAndBitsFast_eq]
          | _ => rfl
        | _ => cases v₂ <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

def finishAssignStmtNodeFast
    (s : MachineState) (dst : Place) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvalueEvalResult → MirStepNode
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok val locals₁ mem₁ =>
    match dst.projection with
    | .nil =>
      match get? locals₁ dst.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dst.local_ (.init val) with
        | .some locals₂ =>
          match hasProtectedWriteConflict mem₁.borrows mem₁.activeProtectors
              dst.local_ .none .nil 0 0 (length mem₁.callStack) with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none
                (length mem₁.callStack)
            MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => finishAssignStmtNode s dst localDecls layouts (.ok val locals₁ mem₁)

theorem finishAssignStmtNodeFast_eq
    (s : MachineState) (dst : Place) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult) :
    finishAssignStmtNodeFast s dst localDecls layouts res =
      finishAssignStmtNode s dst localDecls layouts res := by
  cases res with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨loc, proj⟩
    cases proj with
    | nil =>
      dsimp only [finishAssignStmtNodeFast, finishAssignStmtNode]
      cases get? locals₁ loc with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
        | init _ =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
    | cons _ _ => rfl

def evalStmtFallback (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmt s stmt localDecls layouts

def evalStmtFast
    (body : CapturedMir) (s : MachineState) (stmt : Statement) : MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignStmtNodeFast s dst body.localDecls body.layouts
      (evalRvalueFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .nop => MirStepNode.step (advanceStmt s s.frame.locals)
  | _ => evalStmtFallback s stmt body.localDecls body.layouts

theorem evalStmtFast_eq
    (body : CapturedMir) (s : MachineState) (stmt : Statement) :
    evalStmtFast body s stmt =
      evalStmt s stmt body.localDecls body.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignStmtNodeFast s dst body.localDecls body.layouts
      (evalRvalueFast body s.frame.locals rv s.memory) = _
    rw [finishAssignStmtNodeFast_eq, evalRvalueFast_eq]
    dsimp only [finishAssignStmtNode, evalStmt]
    cases evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts <;> rfl
  | _ => rfl

def finishAssignSymTree (s : MachineState) (dst : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    SymTree RvalueEvalResult → SymTree MirStepNode
  | .leaf res => .leaf (finishAssignStmtNode s dst localDecls layouts res)
  | .branch c t1 t2 =>
    .branch c (finishAssignSymTree s dst localDecls layouts t1)
      (finishAssignSymTree s dst localDecls layouts t2)

theorem finishAssignSymTree_eq (s : MachineState) (dst : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (t : SymTree RvalueEvalResult) :
    finishAssignSymTree s dst localDecls layouts t =
      t.bind (fun res => .leaf (finishAssignStmtNode s dst localDecls layouts res)) := by
  induction t with
  | leaf _ => rfl
  | branch _ _ _ ih1 ih2 =>
    dsimp only [finishAssignSymTree, SymTree.bind]
    rw [ih1, ih2]

def evalStmtSymTreeFast
    (body : CapturedMir) (s : MachineState) (stmt : Statement) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignSymTree s dst body.localDecls body.layouts
      (evalRvalueSymTreeFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .uninit with
         | .some locals' =>
           match s.memory.activeProtectors with
           | .nil =>
             MirStepNode.step
               (advanceStmt s locals'
                 { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
           | protHead :: protTail =>
             match
               hasProtectedLocalBorrow
                 s.memory.borrows
                 (protHead :: protTail)
                 loc
                 (length s.memory.callStack)
             with
             | true => MirStepNode.fail .ub
             | false =>
               MirStepNode.step
                 (advanceStmt s locals'
                   { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .storageDead loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .dead with
         | .some locals' =>
           match s.memory.activeProtectors with
           | .nil =>
             MirStepNode.step
               (advanceStmt s locals'
                 { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
           | protHead :: protTail =>
             match
               hasProtectedLocalBorrow
                 s.memory.borrows
                 (protHead :: protTail)
                 loc
                 (length s.memory.callStack)
             with
             | true => MirStepNode.fail .ub
             | false =>
               MirStepNode.step
                 (advanceStmt s locals'
                   { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .nop => .leaf (MirStepNode.step (advanceStmt s s.frame.locals))
  | _ => .leaf (evalStmtFallback s stmt body.localDecls body.layouts)

theorem evalStmtSymTreeFast_eq
    (body : CapturedMir) (s : MachineState) (stmt : Statement) :
    evalStmtSymTreeFast body s stmt =
      evalStmtSymTree s stmt body.localDecls body.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignSymTree s dst body.localDecls body.layouts
        (evalRvalueSymTreeFast body s.frame.locals rv s.memory) =
      (evalRvalueSymTree s.frame.locals rv s.memory body.localDecls body.layouts).bind _
    rw [finishAssignSymTree_eq, evalRvalueSymTreeFast_eq]
  | _ => rfl

def evalTerminatorFallback (s : MachineState) (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  evalTerminatorSymTree s term currentBody

def evalTerminatorSymTreeFast
    (body : CapturedMir) (s : MachineState) (term : Terminator) : SymTree MirStepNode :=
  match term.kind with
  | .goto target =>
    .leaf (MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) =>
        .leaf
          (match
            hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length s.memory.callStack) (length s.frame.locals)
          with
          | true => MirStepNode.fail .ub
          | false =>
            match valueContainsUninit retVal with
            | true => MirStepNode.fail .ub
            | false =>
              MirStepNode.retNormal retVal
                { s.memory with
                  borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
                    (length s.frame.locals) })
      | _ => .leaf (MirStepNode.fail .ub)
    | _ :: _ => evalTerminatorFallback s term body
  | .switchInt discr targets =>
    match evalOperandWithBodyCastFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | .ok (.scalar sc) locals' =>
      (lookupSwitchTargetTree sc.bits targets.branches targets.otherwise).bind
        (fun target =>
          .leaf (.vis (.inr (.inl (.emit (.event sc.bits))))
            (fun _ =>
              .running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | .assert cond expected target unwind =>
    match evalOperandWithBodyCastFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .branch (Nat.beq sc.bits expectedBit)
        (.leaf
          (MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }))
        (.leaf
          (match applyUnwindAction s locals' s.memory unwind with
          | .running nextState => MirStepNode.step nextState
          | .halted out => .ret out
          | .faulted fk => MirStepNode.fail fk))
    | _ => evalTerminatorFallback s term body
  | _ => evalTerminatorFallback s term body

theorem evalTerminatorSymTreeFast_eq
    (body : CapturedMir) (s : MachineState) (term : Terminator) :
    evalTerminatorSymTreeFast body s term =
      evalTerminatorSymTree s term body := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | return_ =>
    show evalTerminatorSymTreeFast body s { kind := .return_, span := span } =
      evalTerminatorSymTree s { kind := .return_, span := span } body
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree evalTerminator
    dsimp only
    cases s.memory.callStack with
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit => rfl
        | init retVal =>
          dsimp only
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rfl
          | false =>
            cases valueContainsUninit retVal <;> rfl
    | cons _ _ => rfl
  | switchInt discr targets =>
    show evalTerminatorSymTreeFast body s { kind := .switchInt discr targets, span := span } =
      evalTerminatorSymTree s { kind := .switchInt discr targets, span := span } body
    unfold evalTerminatorSymTreeFast evalTerminatorSymTree
    dsimp only
    rw [evalOperandWithBodyCastFast_eq]
    rfl
  | assert cond expected target unwind =>
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree
    dsimp only
    rw [evalOperandWithBodyCastFast_eq]
    cases evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok v _ => cases v <;> rfl
  | _ => rfl

def stepMirSymTreeFast (body : CapturedMir) (s : MachineState) : SymTree MirStepNode :=
  match s.memory.activeCallee with
  | .some _ => stepMirSymTree body s
  | .none =>
    match body.phase with
    | .other _ => .leaf MirStepNode.unsupported
    | _ =>
      match get? body.basicBlocks s.frame.blockIdx with
      | none => .leaf (MirStepNode.fail .ub)
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt =>
          evalStmtSymTreeFast body s stmt
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminatorSymTreeFast body s bb.terminator
          else
            .leaf (MirStepNode.fail .ub)

theorem stepMirSymTreeFast_eq (body : CapturedMir) (s : MachineState) :
    stepMirSymTreeFast body s = stepMirSymTree body s := by
  unfold stepMirSymTreeFast stepMirSymTree
  cases s.memory.activeCallee with
  | some _ => rfl
  | none =>
    dsimp only [Option.getD]
    cases body.phase with
    | other _ => rfl
    | _ =>
      all_goals
        dsimp only
        cases get? body.basicBlocks s.frame.blockIdx with
        | none => rfl
        | some bb =>
          dsimp only
          cases get? bb.statements s.frame.stmtIdx with
          | some stmt =>
            dsimp only
            rw [evalStmtSymTreeFast_eq]
          | none =>
            dsimp only
            split
            · exact evalTerminatorSymTreeFast_eq body s bb.terminator
            · rfl

def wpExecGen (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, _ => zeroVal
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpExecGen zeroVal body post fuel') post (stepMirSymTreeFast body s)

theorem wpMirExecSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecSym fuel body st post = wpExecGen False body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn : (fun st' => wpMirExecSym fuel' body st' post) = wpExecGen False body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq body s]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpExecGen]

theorem wpMirExecOrExhaustedSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecOrExhaustedSym fuel body st post = wpExecGen True body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn :
        (fun st' => wpMirExecOrExhaustedSym fuel' body st' post) =
          wpExecGen True body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq body s]
    | halted out =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree,
          MirStepNode.fail, wpExecGen]

def wpExecFallback (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) : Prop :=
  wpExecGen zeroVal body post fuel st

def lookupBlock (body : CapturedMir) (idx : Nat) : Option BasicBlockData :=
  get? body.basicBlocks idx

def dispatchBlock
    (fallback : Prop)
    (s : MachineState)
    (body : CapturedMir)
    (post : MirOutcome → Prop)
    (kNone : MirExecState → Prop)
    (kSome : Nat → List Statement → Terminator → MirExecState → Prop) :
    Option BasicBlockData → Prop
  | .none => fallback
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalSymNodeTree kNone post (evalTerminatorSymTreeFast body s term)
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    evalSymNodeTree (kSome s.frame.blockIdx rest term) post (evalStmtSymTreeFast body s stmt)

def wpCfgStep
    (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → Option (Nat × Nat × List Statement × Terminator) → MirExecState → Prop
  | 0, _, _ => zeroVal
  | _ + 1, _, .halted out => post out
  | _ + 1, _, .faulted _ => False
  | fuel' + 1, .none, .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          dispatchBlock
            False
            s body post
            (wpCfgStep zeroVal body post fuel' .none)
            (fun bIdx rest term => wpCfgStep zeroVal body post fuel' (.some (bIdx, 1, rest, term)))
            (lookupBlock body s.frame.blockIdx)
  | fuel' + 1, .some (blockIdx, stmtIdx, [], term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal body post fuel' .none)
              post
              (evalTerminatorSymTreeFast body s term)
  | fuel' + 1, .some (blockIdx, stmtIdx, stmt :: rest, term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal body post fuel' (.some (blockIdx, Nat.add stmtIdx 1, rest, term)))
              post
              (evalStmtSymTreeFast body s stmt)

abbrev wpBlockLinear
    (zeroVal : Prop) (body : CapturedMir)
    (term : Terminator) (post : MirOutcome → Prop)
    (blockIdx stmtIdx fuel : Nat)
    (stmts : List Statement) (locals : List LocalSlot) (mem : Memory) : Prop :=
  wpCfgStep zeroVal body post fuel (.some (blockIdx, stmtIdx, stmts, term))
    (.running { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }, memory := mem })

theorem wpCfgStep_eq
    (zeroVal : Prop) (body : CapturedMir)
    (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cur : Option (Nat × Nat × List Statement × Terminator))
      (st : MirExecState),
      (∀ bIdx sIdx stmts term,
        cur = .some (bIdx, sIdx, stmts, term) →
        ∃ bb pfx,
          get? body.basicBlocks bIdx = some bb ∧
          sIdx = length pfx ∧
          bb.statements = pfx ++ stmts ∧
          term = bb.terminator) →
      wpExecGen zeroVal body post fuel st =
        wpCfgStep zeroVal body post fuel cur st := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel' ih =>
    intro cur st h_cur
    cases st with
    | halted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | faulted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | running s =>
      cases cur with
      | none =>
        dsimp only [wpCfgStep, wpExecFallback]
        cases h_ac : s.memory.activeCallee with
        | some _ => rfl
        | none =>
          dsimp only
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false => rfl
          | true =>
            dsimp only [lookupBlock]
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            dsimp only [wpExecGen, stepMirSymTreeFast]
            rw [h_ac]
            dsimp only
            rw [h_phase]
            dsimp only
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              dsimp only [evalSymNodeTree, MirStepNode.fail, dispatchBlock]
            | some bb =>
              rcases bb with ⟨stmts, term, isCleanup⟩
              dsimp only
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlock, get?, length, BEq.beq, instBEqOfDecidableEq,
                  Nat.decEq, instDecidableEqNat, decide]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
              | cons stmt rest =>
                dsimp only [dispatchBlock, get?]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (s.frame.blockIdx, 1, rest, term)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                exact ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
      | some tup =>
        rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
        rcases h_cur blockIdx stmtIdx stmts term rfl with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
        cases stmts with
        | nil =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                subst h_eq
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
        | cons stmt rest =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, h_stmts, get?_append_cons]
                dsimp only
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                refine ⟨bb, pfx ++ [stmt], h_bb, ?_, by simp [h_stmts, List.append_assoc], rfl⟩
                exact (length_append_singleton pfx stmt).symm

theorem wpExecGen_eq_wpCfgStep
    (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (st : MirExecState) :
    wpExecGen zeroVal body post fuel st =
      wpCfgStep zeroVal body post fuel .none st :=
  wpCfgStep_eq zeroVal body post h_phase fuel .none st (fun _ _ _ _ h => nomatch h)

theorem wpStartBlock0_eq
    (zeroVal : Prop) (body : CapturedMir) (bb : BasicBlockData)
    (post : MirOutcome → Prop) (fuel : Nat) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb : get? body.basicBlocks 0 = some bb) :
    wpExecGen zeroVal body post fuel (.running (initMachineState body args)) =
      wpBlockLinear zeroVal body bb.terminator post
        0 0 fuel bb.statements (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory := by
  refine wpCfgStep_eq zeroVal body post h_phase fuel
    (.some (0, 0, bb.statements, bb.terminator))
    (.running (initMachineState body args)) ?_
  intro bIdx sIdx stmts term h_some
  injection h_some with h_tup
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
  exact ⟨bb, [], h_bb, rfl, rfl, rfl⟩

def boolTruePost : MirOutcome → Prop :=
  fun out =>
    ∀ retVal mem',
      out = .normal (retVal, mem') →
      retVal = .scalar { bits := 1, sizeBytes := 1 }

theorem boolTruePost_normal_one (mem' : Memory) :
    boolTruePost (.normal (.scalar { bits := 1, sizeBytes := 1 }, mem')) := by
  intro retVal _ h
  injection h with hp
  injection hp with hv _
  exact hv.symm

theorem mirBoolPredicateHolds_of_wpMirSym_true
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : wpMirSym fuel specBody (initMachineState specBody args) boolTruePost) :
    MirBoolPredicateHolds specBody args :=
  (mirBoolPredicateHolds_iff_dwlp specBody args).2 (dwlp_of_wpMirSym h)

def dummyBB : BasicBlockData :=
  { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

def entryBB (body : CapturedMir) : BasicBlockData :=
  (get? body.basicBlocks 0).getD dummyBB

theorem hold_mirBool_of_blockLinear
    (body : CapturedMir) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : Hold
      (wpBlockLinear False body (entryBB body).terminator
        boolTruePost 0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory)) :
    Hold (MirBoolPredicateHolds body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true (defaultSpecSteps body) body args ?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen,
      wpStartBlock0_eq False body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0]
  exact h.val

theorem holdBoolReq_of_mirBool
    (body : CapturedMir) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : MirBoolPredicateHolds body args) :
    Hold
      (wpBlockLinear True body (entryBB body).terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory) := by
  refine ⟨?_⟩
  rw [← wpStartBlock0_eq True body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0,
      ← wpMirExecOrExhaustedSym_eq_gen]
  exact holdBoolMirSym_of_mirBoolPredicateHolds (defaultSpecSteps body) body args h

theorem hold_wpMirSym_of_blockLinear
    (body : CapturedMir) (args : List Value) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : Hold
      (wpBlockLinear False body (entryBB body).terminator
        post 0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory)) :
    Hold (wpMirSym (defaultSpecSteps body) body (initMachineState body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen,
      wpStartBlock0_eq False body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0]
  exact h.val

theorem verifyMirNoPanic_of_blockLinear
    (c : Claim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_bb0 : get? c.body.basicBlocks 0 = some (entryBB c.body))
    (h_callees : c.callees = [])
    (h_wp : ∀ args, c.pre args →
      Hold
        (wpBlockLinear False c.body (entryBB c.body).terminator
          (mirNormalPost (fun retVal _ => c.post args retVal))
          0 0 (defaultSpecSteps c.body) (entryBB c.body).statements
          (initLocalsAux 0 c.body.localDecls args)
          (initMachineState c.body args).memory)) :
    VerificationResult c := by
  refine verifyMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args h_pre
  rw [h_callees]
  exact (hold_wpMirSym_of_blockLinear c.body args _ h_phase h_bb0 (h_wp args h_pre)).val

theorem verifyMirNoPanic_of_cfg
    (c : Claim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_callees : c.callees = [])
    (h_wp : ∀ args, c.pre args →
      Hold
        (wpCfgStep False c.body (mirNormalPost (fun retVal _ => c.post args retVal))
          (defaultSpecSteps c.body) .none (.running (initMachineState c.body args)))) :
    VerificationResult c := by
  refine verifyMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args h_pre
  rw [h_callees]
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen, wpExecGen_eq_wpCfgStep False c.body _ h_phase]
  exact (h_wp args h_pre).val

theorem verifyStatefulMirNoPanic_of_cfg
    (c : StatefulClaim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_callees : c.callees = [])
    (h_wp : ∀ args mem, c.pre args mem →
      Hold
        (wpCfgStep False c.body (mirNormalPost (c.post args mem))
          (defaultSpecSteps c.body) .none
          (.running (initMachineStateWithMemory c.body args mem)))) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args mem h_pre
  rw [h_callees]
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen, wpExecGen_eq_wpCfgStep False c.body _ h_phase]
  exact (h_wp args mem h_pre).val

inductive CfgExecState where
  | running
      (ok : Bool)
      (cur : Option (Nat × Nat × List Statement × Terminator))
      (s : MachineState)
  | halted (ok : Bool) (out : MirOutcome)
  | faulted

def cfgOk : CfgExecState → Bool
  | .running ok _ _ => ok
  | .halted ok _ => ok
  | .faulted => false

def cfgStateWP (post : MirOutcome → Prop) : CfgExecState → Prop
  | .halted ok out => ok = true ∧ post out
  | _ => False

def stepNodeToCfg
    (ok : Bool)
    (nextCur : Option (Nat × Nat × List Statement × Terminator)) :
    MirStepNode → CfgExecState
  | .ret out => .halted ok out
  | .tau (.running s') => .running ok nextCur s'
  | .tau (.halted out) => .halted ok out
  | .tau (.faulted _) => .faulted
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => .running ok nextCur s'
    | .halted out => .halted ok out
    | .faulted _ => .faulted
  | .vis _ _ => .faulted

def evalTerminatorCfg
    (body : CapturedMir) (ok : Bool) (s : MachineState)
    (term : Terminator) : CfgExecState :=
  match term.kind with
  | .goto target =>
    .running ok .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } }
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) =>
        match
          hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
            (length s.memory.callStack) (length s.frame.locals)
        with
        | true => .faulted
        | false =>
          match valueContainsUninit retVal with
          | true => .faulted
          | false =>
            .halted ok
              (.normal (retVal,
                { s.memory with
                  borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
                    (length s.frame.locals) }))
      | _ => .faulted
    | _ :: _ => .faulted
  | .switchInt discr targets =>
    match evalOperandWithBodyCastFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | .ok (.scalar sc) locals' =>
      let target := lookupSwitchTarget sc.bits targets.branches targets.otherwise
      .running ok .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | .assert cond expected target _ =>
    match evalOperandWithBodyCastFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .running (Bool.and ok (Nat.beq sc.bits expectedBit)) .none
        { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | _ => .faulted

def dispatchBlockCfg
    (ok : Bool) (s : MachineState) (body : CapturedMir) :
    Option BasicBlockData → CfgExecState
  | .none => .faulted
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalTerminatorCfg body ok s term
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    stepNodeToCfg ok (.some (s.frame.blockIdx, 1, rest, term)) (evalStmtFast body s stmt)

def stepCfgState (body : CapturedMir) : CfgExecState → CfgExecState
  | .halted ok out => .halted ok out
  | .faulted => .faulted
  | .running ok cur s =>
    match s.memory.activeCallee with
    | .some _ => .faulted
    | .none =>
      match cur with
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => .faulted
        | true => dispatchBlockCfg ok s body (lookupBlock body s.frame.blockIdx)
      | .some (blockIdx, stmtIdx, [], term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true => evalTerminatorCfg body ok s term
      | .some (blockIdx, stmtIdx, stmt :: rest, term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true =>
            stepNodeToCfg ok
              (.some (blockIdx, Nat.add stmtIdx 1, rest, term))
              (evalStmtFast body s stmt)

def runCfgSteps (body : CapturedMir) (cfg : CfgExecState) : Nat → CfgExecState
  | 0 => cfg
  | fuel' + 1 => stepCfgState body (runCfgSteps body cfg fuel')

theorem runCfgSteps_step (body : CapturedMir) (cfg : CfgExecState) (fuel : Nat) :
    runCfgSteps body cfg (fuel + 1) = runCfgSteps body (stepCfgState body cfg) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    change stepCfgState body (runCfgSteps body cfg (fuel' + 1)) =
      stepCfgState body (runCfgSteps body (stepCfgState body cfg) fuel')
    rw [ih]

theorem runCfgSteps_halted (body : CapturedMir) (ok : Bool) (out : MirOutcome) (fuel : Nat) :
    runCfgSteps body (.halted ok out) fuel = .halted ok out := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    dsimp only [runCfgSteps]
    rw [ih]
    rfl

def CurValid (body : CapturedMir) :
    Option (Nat × Nat × List Statement × Terminator) → Prop
  | .none => True
  | .some (bIdx, sIdx, stmts, term) =>
    ∃ bb pfx,
      get? body.basicBlocks bIdx = some bb ∧
      sIdx = length pfx ∧
      bb.statements = pfx ++ stmts ∧
      term = bb.terminator

def CfgValid (body : CapturedMir) : CfgExecState → MirExecState → Prop
  | .running _ cur s, st => st = .running s ∧ CurValid body cur
  | .halted _ out, st => st = .halted out
  | .faulted, _ => True

theorem cfgOk_stepNodeToCfg_false
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode) :
    cfgOk (stepNodeToCfg false nextCur node) = false := by
  cases node with
  | ret _ => rfl
  | tau st' => cases st' <;> rfl
  | vis i k =>
    rcases i with f | (e | c)
    · rfl
    · dsimp only [stepNodeToCfg, cfgOk]
      cases k PUnit.unit <;> rfl
    · rfl

theorem cfgOk_evalTerminatorCfg_false
    (body : CapturedMir) (s : MachineState) (term : Terminator) :
    cfgOk (evalTerminatorCfg body false s term) = false := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ => rfl
  | return_ =>
    dsimp only [evalTerminatorCfg]
    cases s.memory.callStack with
    | cons _ _ => rfl
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit => rfl
        | init retVal =>
          dsimp only
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rfl
          | false =>
            cases valueContainsUninit retVal <;> rfl
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandWithBodyCastFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandWithBodyCastFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals body.localDecls s.memory.callStack with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | _ => rfl

theorem cfgOk_dispatchBlockCfg_false
    (s : MachineState) (body : CapturedMir) (bbOpt : Option BasicBlockData) :
    cfgOk (dispatchBlockCfg false s body bbOpt) = false := by
  cases bbOpt with
  | none => rfl
  | some bb =>
    rcases bb with ⟨stmts, term, isCleanup⟩
    cases stmts with
    | nil => exact cfgOk_evalTerminatorCfg_false body s term
    | cons stmt rest => exact cfgOk_stepNodeToCfg_false _ _

theorem cfgOk_stepCfgState_false
    (body : CapturedMir) (cfg : CfgExecState) (h : cfgOk cfg = false) :
    cfgOk (stepCfgState body cfg) = false := by
  cases cfg with
  | faulted => rfl
  | halted ok out => exact h
  | running ok cur s =>
    change ok = false at h
    subst h
    cases h_ac : s.memory.activeCallee with
    | some _ =>
      dsimp only [stepCfgState]
      rw [h_ac]
      rfl
    | none =>
      cases cur with
      | none =>
        dsimp only [stepCfgState]
        rw [h_ac]
        dsimp only
        cases Nat.beq s.frame.stmtIdx 0 with
        | false => rfl
        | true => exact cfgOk_dispatchBlockCfg_false s body _
      | some tup =>
        rcases tup with ⟨bIdx, sIdx, stmts, term⟩
        cases stmts with
        | nil =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_evalTerminatorCfg_false body s term
        | cons stmt rest =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_stepNodeToCfg_false _ _

theorem cfgOk_of_runCfgSteps_true
    (body : CapturedMir) (fuel : Nat) (cfg : CfgExecState)
    (h : cfgOk (runCfgSteps body cfg fuel) = true) :
    cfgOk cfg = true := by
  cases h_ok : cfgOk cfg with
  | true => rfl
  | false =>
    have h_false : ∀ n, cfgOk (runCfgSteps body cfg n) = false := by
      intro n
      induction n with
      | zero => exact h_ok
      | succ fuel' ih =>
        dsimp only [runCfgSteps]
        exact cfgOk_stepCfgState_false body (runCfgSteps body cfg fuel') ih
    have h_f := h_false fuel
    rw [h] at h_f
    nomatch h_f

def stepNodeWP (body : CapturedMir) (post : MirOutcome → Prop) (fuel : Nat)
    (node : MirStepNode) : Prop :=
  match node with
  | .ret out => post out
  | .tau st' =>
    wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) st' PUnit.unit
  | .vis i k =>
    mirNoCallWP.wp i
      (fun o s' =>
        wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) (k o) s')
      PUnit.unit

theorem wpCoalBounded_succ_eq
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel : Nat) (st : MirExecState) :
    wpCoalBounded (fuel + 1) mirNoCallWP (stepMirState body)
      (fun out _ => post out) st PUnit.unit =
    stepNodeWP body post fuel (stepMirState body st) := by
  unfold wpCoalBounded stepNodeWP
  cases stepMirState body st <;> rfl

theorem wpCoalBounded_stepNodeToCfg
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel' : Nat)
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode)
    (h_cur : CurValid body nextCur)
    (h_ok : cfgOk (stepNodeToCfg true nextCur node) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStateWP post (runCfgSteps body cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps body (stepNodeToCfg true nextCur node) fuel')) :
    stepNodeWP body post (fuel' + 1) node := by
  cases node with
  | ret out =>
    dsimp only [stepNodeToCfg] at h_wp
    rw [runCfgSteps_halted] at h_wp
    exact h_wp.2
  | tau st' =>
    cases st' with
    | running s' =>
      exact ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
    | halted out =>
      exact ih (.halted true out) (.halted out) rfl h_wp
    | faulted _ => nomatch h_ok
  | vis i k =>
    rcases i with f | (e | c)
    · nomatch h_ok
    · cases e
      dsimp only [stepNodeToCfg] at h_ok h_wp
      cases h_k : k PUnit.unit with
      | running s' =>
        rw [h_k] at h_wp
        have h_res := ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
        rw [← h_k] at h_res
        exact h_res
      | halted out =>
        rw [h_k] at h_wp
        have h_res := ih (.halted true out) (.halted out) rfl h_wp
        rw [← h_k] at h_res
        exact h_res
      | faulted _ =>
        rw [h_k] at h_ok
        nomatch h_ok
    · nomatch h_ok

theorem wpCoalBounded_evalTerminatorCfg
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel' : Nat)
    (s : MachineState) (term : Terminator)
    (h_ok : cfgOk (evalTerminatorCfg body true s term) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStateWP post (runCfgSteps body cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps body (evalTerminatorCfg body true s term) fuel')) :
    stepNodeWP body post (fuel' + 1) (evalTerminator s term (some body)) := by
  rcases term with ⟨kind, span⟩
  revert h_ok h_wp
  cases kind with
  | goto target =>
    intro _ h_wp
    exact ih (.running true .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      (.running { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      ⟨rfl, trivial⟩ h_wp
  | return_ =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    cases s.memory.callStack with
    | cons _ _ => rintro ⟨⟩ _
    | nil =>
      dsimp only
      cases get? s.frame.locals 0 with
      | none => rintro ⟨⟩ _
      | some slot =>
        cases slot with
        | dead => rintro ⟨⟩ _
        | uninit => rintro ⟨⟩ _
        | init retVal =>
          dsimp only
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rintro ⟨⟩ _
          | false =>
            dsimp only
            cases valueContainsUninit retVal with
            | true => rintro ⟨⟩ _
            | false =>
              intro _ h_wp
              dsimp only [stepNodeWP, MirStepNode.retNormal] at h_wp ⊢
              rw [runCfgSteps_halted] at h_wp
              exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator, bodyLocalDeclsOf]
    rw [evalOperandWithBodyCastFast_eq]
    cases evalOperandWithBodyCast s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only [stepNodeWP, MirStepNode.step]
        intro _ h_wp
        exact ih
          (.running true .none
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          (.running
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg, evalTerminator, bodyLocalDeclsOf]
    rw [evalOperandWithBodyCastFast_eq]
    cases evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected <;>
        · dsimp only [cfgOk, Bool.and]
          intro h_ok h_wp
          rw [h_ok] at h_wp ⊢
          dsimp only [stepNodeWP, MirStepNode.step] at h_wp ⊢
          exact ih
            (.running true .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            (.running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | _ => rintro ⟨⟩ _

theorem wpCoalBounded_of_runCfgSteps
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cfg : CfgExecState) (st : MirExecState),
      CfgValid body cfg st →
      cfgStateWP post (runCfgSteps body cfg fuel) →
      wpCoalBounded (fuel + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg st h_valid h_wp
    dsimp only [runCfgSteps] at h_wp
    cases cfg with
    | running _ _ _ => exact False.elim h_wp
    | faulted => exact False.elim h_wp
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      exact h_wp.2
  | succ fuel' ih =>
    intro cfg st h_valid h_wp
    rw [runCfgSteps_step] at h_wp
    have h_ok1 : cfgOk (stepCfgState body cfg) = true :=
      cfgOk_of_runCfgSteps_true body fuel' (stepCfgState body cfg)
        (by
          cases h_end : runCfgSteps body (stepCfgState body cfg) fuel' with
          | halted ok out =>
            rw [h_end] at h_wp
            exact h_wp.1
          | running _ _ _ =>
            rw [h_end] at h_wp
            exact False.elim h_wp
          | faulted =>
            rw [h_end] at h_wp
            exact False.elim h_wp)
    have h_ok0 : cfgOk cfg = true := by
      cases h_c : cfgOk cfg with
      | true => rfl
      | false =>
        rw [cfgOk_stepCfgState_false body cfg h_c] at h_ok1
        nomatch h_ok1
    cases cfg with
    | faulted => nomatch h_ok0
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      change ok = true at h_ok0
      subst h_ok0
      dsimp only [stepCfgState] at h_wp
      rw [runCfgSteps_halted] at h_wp
      exact h_wp.2
    | running ok cur s =>
      change ok = true at h_ok0
      subst h_ok0
      rcases h_valid with ⟨rfl, h_cur⟩
      dsimp only [stepCfgState] at h_ok1 h_wp
      cases h_ac : s.memory.activeCallee with
      | some _ =>
        rw [h_ac] at h_ok1
        nomatch h_ok1
      | none =>
        rw [h_ac] at h_ok1 h_wp
        dsimp only at h_ok1 h_wp
        rw [wpCoalBounded_succ_eq]
        dsimp only [stepMirState, stepMirFn]
        rw [h_ac]
        dsimp only [Option.getD]
        rw [h_phase]
        dsimp only
        cases cur with
        | none =>
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false =>
            rw [h_si] at h_ok1
            nomatch h_ok1
          | true =>
            rw [h_si] at h_ok1 h_wp
            dsimp only [lookupBlock] at h_ok1 h_wp
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              rw [h_bb] at h_ok1
              nomatch h_ok1
            | some bb =>
              rw [h_bb] at h_ok1 h_wp
              rcases bb with ⟨stmts, term, isCleanup⟩
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal, length, BEq.beq,
                  instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide] at h_ok1 h_wp ⊢
                exact wpCoalBounded_evalTerminatorCfg body post fuel' s term h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal] at h_ok1 h_wp ⊢
                rw [← evalStmtFast_eq body s stmt]
                exact wpCoalBounded_stepNodeToCfg body post fuel'
                  (.some (s.frame.blockIdx, 1, rest, term))
                  (evalStmtFast body s stmt)
                  ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
                  h_ok1 ih h_wp
        | some tup =>
          rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
          rcases h_cur with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
          cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
          | false =>
            cases stmts <;> (dsimp only at h_ok1; rw [h_bi] at h_ok1; nomatch h_ok1)
          | true =>
            have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
            cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
            | false =>
              cases stmts <;> (dsimp only at h_ok1; rw [h_bi, h_si] at h_ok1; nomatch h_ok1)
            | true =>
              have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
              rw [h_bi_eq, h_bb, h_si_eq]
              dsimp only
              cases stmts with
              | nil =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                rw [← h_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq, if_pos rfl]
                exact wpCoalBounded_evalTerminatorCfg body post fuel' s bb.terminator h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                rw [h_stmts, get?_append_cons]
                dsimp only
                rw [← evalStmtFast_eq body s stmt]
                exact wpCoalBounded_stepNodeToCfg body post fuel'
                  (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator))
                  (evalStmtFast body s stmt)
                  ⟨bb, pfx ++ [stmt], h_bb, (length_append_singleton pfx stmt).symm,
                    by simp [h_stmts, List.append_assoc], rfl⟩
                  h_ok1 ih h_wp

theorem wpCoalBounded_default_of_noCall
    (fuel : Nat) (body : CapturedMir) (post : MirOutcome → Prop) (st : MirExecState)
    (h : wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) st PUnit.unit) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body) (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih (k PUnit.unit) h
      · exact False.elim h

theorem cfgStateWP_of_eq
    {post : MirOutcome → Prop} {cfg : CfgExecState} {out : MirOutcome}
    (h_eq : cfg = .halted true out) (h_post : post out) :
    cfgStateWP post cfg := by
  rw [h_eq]
  exact ⟨rfl, h_post⟩

def evalMirSpecBool (specBody : CapturedMir) (args : List Value) : Bool :=
  match runCfgSteps specBody
    (.running true .none (initMachineState specBody args))
    (defaultSpecSteps specBody) with
  | .halted true (.normal (.scalar { bits := 1, sizeBytes := 1 }, _)) => true
  | _ => false

theorem mirBoolPredicateHolds_of_evalMirSpecBool_true
    (specBody : CapturedMir) (args : List Value)
    (h_phase : specBody.phase = .runtimeOptimized)
    (h_eval : evalMirSpecBool specBody args = true) :
    MirBoolPredicateHolds specBody args := by
  apply mirBoolPredicateHolds_of_wpMirSym_true (defaultSpecSteps specBody + 1) specBody args
  unfold wpMirSym
  rw [wpMirExecSym_eq_wpCoalBounded]
  apply wpCoalBounded_default_of_noCall
  refine wpCoalBounded_of_runCfgSteps specBody boolTruePost h_phase (defaultSpecSteps specBody)
    (.running true .none (initMachineState specBody args))
    (.running (initMachineState specBody args))
    ⟨rfl, trivial⟩ ?_
  unfold evalMirSpecBool at h_eval
  revert h_eval
  cases runCfgSteps specBody
    (.running true .none (initMachineState specBody args))
    (defaultSpecSteps specBody) with
  | running _ _ _ => intro h; contradiction
  | faulted => intro h; contradiction
  | halted ok out =>
    cases ok with
    | false => intro h; contradiction
    | true =>
      cases out with
      | panic => intro h; contradiction
      | abort => intro h; contradiction
      | normal rv =>
        rcases rv with ⟨v, mem'⟩
        cases v with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          cases bits with
          | zero => intro h; contradiction
          | succ b' =>
            cases b' with
            | zero =>
              cases sz with
              | zero => intro h; contradiction
              | succ sz' =>
                cases sz' with
                | zero => intro _; exact ⟨rfl, boolTruePost_normal_one mem'⟩
                | succ _ => intro h; contradiction
            | succ _ => intro h; contradiction
        | _ => intro h; contradiction

theorem verifyStatefulMirNoPanic_of_runCfgSteps
    (c : StatefulClaim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_bb0 : get? c.body.basicBlocks 0 = some (entryBB c.body))
    (h_callees : c.callees = [])
    (h_wp : ∀ args mem, c.pre args mem →
      ∃ retVal,
        runCfgSteps c.body
          (.running true (.some (0, 0, (entryBB c.body).statements, (entryBB c.body).terminator))
            (initMachineStateWithMemory c.body args mem))
          (defaultCfgSteps c.body) = .halted true (.normal (retVal, mem)) ∧
        c.post args mem retVal mem) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanicSym c (defaultCfgSteps c.body + 1) ?_
  intro args mem h_pre
  rw [h_callees]
  rcases h_wp args mem h_pre with ⟨retVal, h_eq, h_post⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_wpCoalBounded]
  exact wpCoalBounded_default_of_noCall (defaultCfgSteps c.body + 1) c.body
    (mirNormalPost (c.post args mem))
    (.running (initMachineStateWithMemory c.body args mem))
    (wpCoalBounded_of_runCfgSteps c.body
      (mirNormalPost (c.post args mem))
      h_phase (defaultCfgSteps c.body)
      (.running true (.some (0, 0, (entryBB c.body).statements, (entryBB c.body).terminator))
        (initMachineStateWithMemory c.body args mem))
      (.running (initMachineStateWithMemory c.body args mem))
      ⟨rfl, ⟨entryBB c.body, [], h_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq h_post))

theorem verifyStatefulEquivMir_of_runCfgSteps
    (c : StatefulEquivClaim)
    (model : List Value → Memory → Value × Memory)
    (h_impl_phase : c.implBody.phase = .runtimeOptimized)
    (h_impl_bb0 : get? c.implBody.basicBlocks 0 = some (entryBB c.implBody))
    (h_impl_callees : c.implCallees = [])
    (h_spec_phase : c.specBody.phase = .runtimeOptimized)
    (h_spec_bb0 : get? c.specBody.basicBlocks 0 = some (entryBB c.specBody))
    (h_spec_callees : c.specCallees = [])
    (h_impl : ∀ args mem, c.pre args mem →
      runCfgSteps c.implBody
        (.running true
          (.some (0, 0, (entryBB c.implBody).statements, (entryBB c.implBody).terminator))
          (initMachineStateWithMemory c.implBody args mem))
        (defaultCfgSteps c.implBody) = .halted true (.normal (model args mem)) ∧
      c.post args mem (model args mem).1 (model args mem).2)
    (h_spec : ∀ args mem, c.pre args mem →
      runCfgSteps c.specBody
        (.running true
          (.some (0, 0, (entryBB c.specBody).statements, (entryBB c.specBody).terminator))
          (initMachineStateWithMemory c.specBody args mem))
        (defaultCfgSteps c.specBody) = .halted true (.normal (model args mem))) :
    StatefulEquivVerificationResult c := by
  refine verifyStatefulEquivMirBounded c
    (defaultCfgSteps c.implBody + 1) (defaultCfgSteps c.specBody + 1) model
    (fun args mem h_pre => ?_)
    (fun args mem h_pre => ?_)
  · rcases h_impl args mem h_pre with ⟨h_eq, h_post⟩
    unfold wpMirNoCallBounded
    rw [h_impl_callees]
    exact wpCoalBounded_of_runCfgSteps c.implBody _ h_impl_phase (defaultCfgSteps c.implBody)
      (.running true
        (.some (0, 0, (entryBB c.implBody).statements, (entryBB c.implBody).terminator))
        (initMachineStateWithMemory c.implBody args mem))
      (.running (initMachineStateWithMemory c.implBody args mem))
      ⟨rfl, ⟨entryBB c.implBody, [], h_impl_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq ⟨rfl, h_post⟩)
  · have h_eq := h_spec args mem h_pre
    unfold wpMirNoCallBounded
    rw [h_spec_callees]
    exact wpCoalBounded_of_runCfgSteps c.specBody _ h_spec_phase (defaultCfgSteps c.specBody)
      (.running true
        (.some (0, 0, (entryBB c.specBody).statements, (entryBB c.specBody).terminator))
        (initMachineStateWithMemory c.specBody args mem))
      (.running (initMachineStateWithMemory c.specBody args mem))
      ⟨rfl, ⟨entryBB c.specBody, [], h_spec_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq rfl)

def stepsExecMid (mid : MachineState → Prop) (post : MirOutcome → Prop) : MirExecState → Prop
  | .running s' => mid s'
  | .halted out => post out
  | .faulted _ => False

def cfgStepsWP (mid : MachineState → Prop) (post : MirOutcome → Prop) : CfgExecState → Prop
  | .running ok _ s => ok = true ∧ mid s
  | .halted ok out => ok = true ∧ post out
  | .faulted => False

theorem cfgOk_of_cfgStepsWP
    {mid : MachineState → Prop} {post : MirOutcome → Prop} {cfg : CfgExecState}
    (h : cfgStepsWP mid post cfg) :
    cfgOk cfg = true := by
  cases cfg with
  | running ok _ _ => exact h.1
  | halted ok _ => exact h.1
  | faulted => exact False.elim h

def stepNodeStepsWP
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (node : MirStepNode) : Prop :=
  match node with
  | .ret out => post out
  | .tau st' =>
    wpMirExecStepsSym fuel body st' (stepsExecMid mid post) post
  | .vis i k =>
    mirNoCallWP.wp i
      (fun o _ =>
        wpMirExecStepsSym fuel body (k o) (stepsExecMid mid post) post)
      PUnit.unit

theorem wpMirExecStepsSym_succ_eq
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) :
    wpMirExecStepsSym (fuel + 1) body st (stepsExecMid mid post) post =
      stepNodeStepsWP body mid post fuel (stepMirState body st) := by
  unfold wpMirExecStepsSym stepNodeStepsWP
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
  rfl

theorem wpMirExecStepsSym_halted
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (out : MirOutcome) (h : post out) :
    wpMirExecStepsSym fuel body (.halted out) (stepsExecMid mid post) post := by
  induction fuel with
  | zero => exact h
  | succ _ _ =>
    unfold wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
    dsimp only [stepMirState]
    exact h

theorem wpMirExecStepsSym_stepNodeToCfg
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel' : Nat)
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode)
    (h_cur : CurValid body nextCur)
    (h_ok : cfgOk (stepNodeToCfg true nextCur node) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStepsWP mid post (runCfgSteps body cfg' fuel') →
      wpMirExecStepsSym fuel' body st' (stepsExecMid mid post) post)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (stepNodeToCfg true nextCur node) fuel')) :
    stepNodeStepsWP body mid post fuel' node := by
  cases node with
  | ret out =>
    dsimp only [stepNodeToCfg] at h_wp
    rw [runCfgSteps_halted] at h_wp
    exact h_wp.2
  | tau st' =>
    cases st' with
    | running s' =>
      exact ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
    | halted out =>
      exact ih (.halted true out) (.halted out) rfl h_wp
    | faulted _ => nomatch h_ok
  | vis i k =>
    rcases i with f | (e | c)
    · nomatch h_ok
    · cases e
      dsimp only [stepNodeToCfg] at h_ok h_wp
      cases h_k : k PUnit.unit with
      | running s' =>
        rw [h_k] at h_wp
        have h_res := ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
        rw [← h_k] at h_res
        exact h_res
      | halted out =>
        rw [h_k] at h_wp
        have h_res := ih (.halted true out) (.halted out) rfl h_wp
        rw [← h_k] at h_res
        exact h_res
      | faulted _ =>
        rw [h_k] at h_ok
        nomatch h_ok
    · nomatch h_ok

theorem wpMirExecStepsSym_evalTerminatorCfg
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel' : Nat) (s : MachineState) (term : Terminator)
    (h_ok : cfgOk (evalTerminatorCfg body true s term) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStepsWP mid post (runCfgSteps body cfg' fuel') →
      wpMirExecStepsSym fuel' body st' (stepsExecMid mid post) post)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (evalTerminatorCfg body true s term) fuel')) :
    stepNodeStepsWP body mid post fuel' (evalTerminator s term (some body)) := by
  rcases term with ⟨kind, span⟩
  revert h_ok h_wp
  cases kind with
  | goto target =>
    intro _ h_wp
    exact ih (.running true .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      (.running { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      ⟨rfl, trivial⟩ h_wp
  | return_ =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    cases s.memory.callStack with
    | cons _ _ => rintro ⟨⟩ _
    | nil =>
      dsimp only
      cases get? s.frame.locals 0 with
      | none => rintro ⟨⟩ _
      | some slot =>
        cases slot with
        | dead => rintro ⟨⟩ _
        | uninit => rintro ⟨⟩ _
        | init retVal =>
          dsimp only
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rintro ⟨⟩ _
          | false =>
            dsimp only
            cases valueContainsUninit retVal with
            | true => rintro ⟨⟩ _
            | false =>
              intro _ h_wp
              dsimp only [stepNodeStepsWP, MirStepNode.retNormal] at h_wp ⊢
              rw [runCfgSteps_halted] at h_wp
              exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator, bodyLocalDeclsOf]
    rw [evalOperandWithBodyCastFast_eq]
    cases evalOperandWithBodyCast s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only [stepNodeStepsWP, MirStepNode.step]
        intro _ h_wp
        exact ih
          (.running true .none
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          (.running
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg, evalTerminator, bodyLocalDeclsOf]
    rw [evalOperandWithBodyCastFast_eq]
    cases evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected <;>
        · dsimp only [cfgOk, Bool.and]
          intro h_ok h_wp
          rw [h_ok] at h_wp ⊢
          dsimp only [stepNodeStepsWP, MirStepNode.step] at h_wp ⊢
          exact ih
            (.running true .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            (.running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | _ => rintro ⟨⟩ _

theorem wpMirExecStepsSym_of_runCfgSteps
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cfg : CfgExecState) (st : MirExecState),
      CfgValid body cfg st →
      cfgStepsWP mid post (runCfgSteps body cfg fuel) →
      wpMirExecStepsSym fuel body st (stepsExecMid mid post) post := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg st h_valid h_wp
    dsimp only [runCfgSteps] at h_wp
    cases cfg with
    | running ok _ s =>
      rcases h_valid with ⟨rfl, _⟩
      exact h_wp.2
    | faulted => exact False.elim h_wp
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      exact h_wp.2
  | succ fuel' ih =>
    intro cfg st h_valid h_wp
    rw [runCfgSteps_step] at h_wp
    have h_ok1 : cfgOk (stepCfgState body cfg) = true :=
      cfgOk_of_runCfgSteps_true body fuel' (stepCfgState body cfg) (cfgOk_of_cfgStepsWP h_wp)
    have h_ok0 : cfgOk cfg = true := by
      cases h_c : cfgOk cfg with
      | true => rfl
      | false =>
        rw [cfgOk_stepCfgState_false body cfg h_c] at h_ok1
        nomatch h_ok1
    cases cfg with
    | faulted => nomatch h_ok0
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      change ok = true at h_ok0
      subst h_ok0
      dsimp only [stepCfgState] at h_wp
      rw [runCfgSteps_halted] at h_wp
      exact wpMirExecStepsSym_halted body mid post (fuel' + 1) out h_wp.2
    | running ok cur s =>
      change ok = true at h_ok0
      subst h_ok0
      rcases h_valid with ⟨rfl, h_cur⟩
      dsimp only [stepCfgState] at h_ok1 h_wp
      cases h_ac : s.memory.activeCallee with
      | some _ =>
        rw [h_ac] at h_ok1
        nomatch h_ok1
      | none =>
        rw [h_ac] at h_ok1 h_wp
        dsimp only at h_ok1 h_wp
        rw [wpMirExecStepsSym_succ_eq]
        dsimp only [stepMirState, stepMirFn]
        rw [h_ac]
        dsimp only [Option.getD]
        rw [h_phase]
        dsimp only
        cases cur with
        | none =>
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false =>
            rw [h_si] at h_ok1
            nomatch h_ok1
          | true =>
            rw [h_si] at h_ok1 h_wp
            dsimp only [lookupBlock] at h_ok1 h_wp
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              rw [h_bb] at h_ok1
              nomatch h_ok1
            | some bb =>
              rw [h_bb] at h_ok1 h_wp
              rcases bb with ⟨stmts, term, isCleanup⟩
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal, length, BEq.beq,
                  instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide] at h_ok1 h_wp ⊢
                exact wpMirExecStepsSym_evalTerminatorCfg body mid post fuel' s term h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal] at h_ok1 h_wp ⊢
                rw [← evalStmtFast_eq body s stmt]
                exact wpMirExecStepsSym_stepNodeToCfg body mid post fuel'
                  (.some (s.frame.blockIdx, 1, rest, term))
                  (evalStmtFast body s stmt)
                  ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
                  h_ok1 ih h_wp
        | some tup =>
          rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
          rcases h_cur with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
          cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
          | false =>
            cases stmts <;> (dsimp only at h_ok1; rw [h_bi] at h_ok1; nomatch h_ok1)
          | true =>
            have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
            cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
            | false =>
              cases stmts <;> (dsimp only at h_ok1; rw [h_bi, h_si] at h_ok1; nomatch h_ok1)
            | true =>
              have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
              rw [h_bi_eq, h_bb, h_si_eq]
              dsimp only
              cases stmts with
              | nil =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                rw [← h_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq, if_pos rfl]
                exact wpMirExecStepsSym_evalTerminatorCfg body mid post fuel' s bb.terminator h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                rw [h_stmts, get?_append_cons]
                dsimp only
                rw [← evalStmtFast_eq body s stmt]
                exact wpMirExecStepsSym_stepNodeToCfg body mid post fuel'
                  (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator))
                  (evalStmtFast body s stmt)
                  ⟨bb, pfx ++ [stmt], h_bb, (length_append_singleton pfx stmt).symm,
                    by simp [h_stmts, List.append_assoc], rfl⟩
                  h_ok1 ih h_wp

theorem mirStepsConverges_of_cfgStepsWP
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (.running true cur s) fuel)) :
    MirStepsConverges body s mid post :=
  ⟨fuel, wpMirExecStepsSym_of_runCfgSteps body mid post h_phase fuel
    (.running true cur s) (.running s) ⟨rfl, h_cur⟩ h_wp⟩

theorem mirStepsConverges_of_cfgStepsWP_none
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (.running true .none s) fuel)) :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_cfgStepsWP body mid post h_phase fuel .none s trivial h_wp

theorem mirStepsConverges_of_runCfgSteps
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (cur' : Option (Nat × Nat × List Statement × Terminator))
    (s' : MachineState)
    (h_cur : CurValid body cur)
    (h_eq : runCfgSteps body (.running true cur s) fuel = .running true cur' s')
    (h_mid : mid s') :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_cfgStepsWP body mid post h_phase fuel cur s h_cur
    (by rw [h_eq]; exact ⟨rfl, h_mid⟩)

theorem mirStepsConverges_of_runCfgSteps_none
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (cur' : Option (Nat × Nat × List Statement × Terminator))
    (s' : MachineState)
    (h_eq : runCfgSteps body (.running true .none s) fuel = .running true cur' s')
    (h_mid : mid s') :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_runCfgSteps body mid post h_phase fuel .none s cur' s' trivial h_eq h_mid

theorem mirNoCallWpConverges_of_cfgStateWP
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true cur s) fuel)) :
    MirNoCallWpConverges body s post := by
  refine ⟨fuel + 1, ?_⟩
  rw [wpMirNoCallSym_eq_wpMirNoCallBounded]
  exact wpCoalBounded_of_runCfgSteps body post h_phase fuel
    (.running true cur s) (.running s) ⟨rfl, h_cur⟩ h_wp

theorem mirWpConverges_of_cfgStateWP
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true cur s) fuel)) :
    MirWpConverges body s post :=
  MirWpConverges.of_noCall
    (mirNoCallWpConverges_of_cfgStateWP body post h_phase fuel cur s h_cur h_wp)

theorem mirWpConverges_of_cfgStateWP_none
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true .none s) fuel)) :
    MirWpConverges body s post :=
  mirWpConverges_of_cfgStateWP body post h_phase fuel .none s trivial h_wp

theorem mirWpConverges_of_runCfgSteps
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState) (out : MirOutcome)
    (h_cur : CurValid body cur)
    (h_eq : runCfgSteps body (.running true cur s) fuel = .halted true out)
    (h_post : post out) :
    MirWpConverges body s post :=
  mirWpConverges_of_cfgStateWP body post h_phase fuel cur s h_cur
    (cfgStateWP_of_eq h_eq h_post)

theorem mirWpConverges_of_runCfgSteps_none
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState) (out : MirOutcome)
    (h_eq : runCfgSteps body (.running true .none s) fuel = .halted true out)
    (h_post : post out) :
    MirWpConverges body s post :=
  mirWpConverges_of_runCfgSteps body post h_phase fuel .none s out trivial h_eq h_post

/-! ### Running to the next block entry without a step count

`runCfgToBlock body target cfg` steps the CFG evaluator from `cfg` until it
next enters basic block `target` (a running state with no cached block at
statement 0 of `target`), halts, or faults. The first step is always taken,
so a loop header reaches itself again one iteration later. Proofs therefore
never state how many steps a loop iteration or a straight-line segment
takes; `length body.basicBlocks + 256` only bounds the recursion.

`runCfgUntilAux` checks `cfgAtBlock` before each step and returns as soon as
`target`, `.halted`, or `.faulted` is reached, so `dsimp` neither evaluates
a step past the target/halt nor unfolds the unused part of the bound.
-/

/-- Whether `cfg` is about to dispatch basic block `target` or has halted /
faulted. -/
def cfgAtBlock (target : Nat) : CfgExecState → Bool
  | .running _ .none s =>
    Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0
  | .running _ (.some _) _ => false
  | .halted _ _ => true
  | .faulted => true

/-- Step from `cfg` until `atTarget = cfgAtBlock target cfg` holds, taking
at most `budget` steps. -/
def runCfgUntilAux (body : CapturedMir) (target : Nat) :
    Nat → CfgExecState → Bool → CfgExecState
  | _, cfg, true => cfg
  | 0, cfg, false => cfg
  | budget + 1, cfg, false =>
    runCfgUntilAux body target budget (stepCfgState body cfg)
      (cfgAtBlock target (stepCfgState body cfg))

/-- Evaluate from `cfg` until the next entry into block `target`, a halt, or
a fault, taking at least one and at most `length body.basicBlocks + 256 + 1`
steps. -/
def runCfgToBlock (body : CapturedMir) (target : Nat) (cfg : CfgExecState) :
    CfgExecState :=
  runCfgUntilAux body target (Nat.add (length body.basicBlocks) 256)
    (stepCfgState body cfg) (cfgAtBlock target (stepCfgState body cfg))

theorem runCfgUntilAux_eq_runCfgSteps (body : CapturedMir) (target : Nat) :
    ∀ budget cfg atTarget, ∃ k,
      runCfgUntilAux body target budget cfg atTarget = runCfgSteps body cfg k
  | _, cfg, true => ⟨0, by cases ‹Nat› <;> rfl⟩
  | 0, cfg, false => ⟨0, rfl⟩
  | budget + 1, cfg, false => by
    obtain ⟨k, hk⟩ := runCfgUntilAux_eq_runCfgSteps body target budget
      (stepCfgState body cfg) (cfgAtBlock target (stepCfgState body cfg))
    exact ⟨k + 1, by rw [runCfgUntilAux, hk, runCfgSteps_step]⟩

/-- Every `runCfgToBlock` run is a prefix of `runCfgSteps`. -/
theorem runCfgToBlock_eq_runCfgSteps (body : CapturedMir) (target : Nat)
    (cfg : CfgExecState) :
    ∃ k, runCfgToBlock body target cfg = runCfgSteps body cfg k := by
  obtain ⟨k, hk⟩ := runCfgUntilAux_eq_runCfgSteps body target
    (Nat.add (length body.basicBlocks) 256) (stepCfgState body cfg)
    (cfgAtBlock target (stepCfgState body cfg))
  exact ⟨k + 1, by rw [runCfgToBlock, hk, runCfgSteps_step]⟩

/-- `mirStepsConverges_of_cfgStepsWP_none` without a step count: the segment
from `s` ends at the next entry into block `target`, or halts. -/
theorem mirStepsConverges_of_runCfgToBlock
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStepsWP mid post
      (runCfgToBlock body target (.running true .none s))) :
    MirStepsConverges body s mid post := by
  obtain ⟨k, hk⟩ :=
    runCfgToBlock_eq_runCfgSteps body target (.running true .none s)
  rw [hk] at h_wp
  exact mirStepsConverges_of_cfgStepsWP body mid post h_phase k .none s
    trivial h_wp

/-- `mirNoCallWpConverges_of_cfgStateWP` without a step count, for a segment
that halts before it re-enters block `target`. -/
theorem mirNoCallWpConverges_of_runCfgToBlock
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStateWP post
      (runCfgToBlock body target (.running true .none s))) :
    MirNoCallWpConverges body s post := by
  obtain ⟨k, hk⟩ :=
    runCfgToBlock_eq_runCfgSteps body target (.running true .none s)
  rw [hk] at h_wp
  exact mirNoCallWpConverges_of_cfgStateWP body post h_phase k .none s
    trivial h_wp

/-- `mirWpConverges_of_cfgStateWP_none` without a step count, for a segment
that halts before it re-enters block `target`. -/
theorem mirWpConverges_of_runCfgToBlock
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStateWP post
      (runCfgToBlock body target (.running true .none s))) :
    MirWpConverges body s post :=
  MirWpConverges.of_noCall
    (mirNoCallWpConverges_of_runCfgToBlock body post h_phase target s h_wp)


/-! #### Generic Deterministic Small-Step Machine and the Kleene Fuel Order -/

/-- Outcome of one deterministic small step. -/
inductive Step (σ α : Type) where
  /-- Continue at `next`. -/
  | cont (next : σ)
  /-- Halt returning `ret`. -/
  | done (ret : α)
  /-- Stuck / undefined behavior. -/
  | fault
  deriving DecidableEq, Repr

/-- Outcome of a bounded-fuel evaluation: running out of fuel is *not* a fault
and is never conflated with halting. -/
inductive FuelResult (α : Type) where
  | outOfFuel
  | halted (v : α)
  | faulted
  deriving DecidableEq, Repr

/-- Flat Kleene information order: `outOfFuel` is bottom; `halted v` and
`faulted` are maximal. -/
def FuelOrder {α : Type} : FuelResult α → FuelResult α → Prop
  | .outOfFuel, _ => True
  | .halted v₁, .halted v₂ => v₁ = v₂
  | .faulted, .faulted => True
  | _, _ => False

theorem FuelOrder.refl {α : Type} (r : FuelResult α) : FuelOrder r r := by
  cases r with
  | outOfFuel => exact trivial
  | halted v => exact rfl
  | faulted => exact trivial

theorem FuelOrder.trans {α : Type} {r₁ r₂ r₃ : FuelResult α}
    (h₁₂ : FuelOrder r₁ r₂) (h₂₃ : FuelOrder r₂ r₃) : FuelOrder r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [FuelOrder]

theorem FuelOrder.halted_stable {α : Type} {v : α} {r : FuelResult α}
    (h : FuelOrder (.halted v) r) : r = .halted v := by
  cases r <;> simp_all [FuelOrder]

theorem FuelOrder.faulted_stable {α : Type} {r : FuelResult α}
    (h : FuelOrder .faulted r) : r = .faulted := by
  cases r <;> simp_all [FuelOrder]

/-- Fueled evaluator by structural recursion on the fuel. -/
def evalFuel {σ α : Type} (step : σ → Step σ α) : Nat → σ → FuelResult α
  | 0, _ => .outOfFuel
  | k + 1, s =>
    match step s with
    | .cont s' => evalFuel step k s'
    | .done v => .halted v
    | .fault => .faulted

/-- **Kleene fuel monotonicity**: adding fuel preserves every terminal outcome. -/
theorem evalFuel_mono {σ α : Type} (step : σ → Step σ α) :
    ∀ {k₁ k₂ : Nat} (s : σ), k₁ ≤ k₂ →
      FuelOrder (evalFuel step k₁ s) (evalFuel step k₂ s)
  | 0, _, _, _ => trivial
  | k₁ + 1, 0, _, hle => absurd hle (Nat.not_succ_le_zero k₁)
  | k₁ + 1, k₂ + 1, s, hle => by
    unfold evalFuel
    cases step s with
    | cont s' => exact evalFuel_mono step s' (Nat.le_of_succ_le_succ hle)
    | done v => exact rfl
    | fault => exact trivial

theorem evalFuel_halted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} {v : α} (h : evalFuel step k₁ s = .halted v) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .halted v := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.halted_stable hm

theorem evalFuel_faulted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} (h : evalFuel step k₁ s = .faulted) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .faulted := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.faulted_stable hm

/-- Halting results are fuel-independent (determinism). -/
theorem evalFuel_halted_deterministic {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v₁ v₂ : α}
    (h₁ : evalFuel step k₁ s = .halted v₁) (h₂ : evalFuel step k₂ s = .halted v₂) :
    v₁ = v₂ := by
  have e₁ := evalFuel_halted_mono h₁ (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono h₂ (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  exact FuelResult.halted.inj e₂

/-- A state that faults under some fuel never halts under any fuel: faults are
never conflated with termination. -/
theorem evalFuel_faulted_ne_halted {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v : α}
    (hf : evalFuel step k₁ s = .faulted) : evalFuel step k₂ s ≠ .halted v := by
  intro hh
  have e₁ := evalFuel_faulted_mono hf (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono hh (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  cases e₂

/-- Fuel-free total-correctness predicate: some finite budget halts in `post`. -/
def WpConverges {σ α : Type} (step : σ → Step σ α) (s : σ) (post : α → Prop) : Prop :=
  ∃ k v, evalFuel step k s = .halted v ∧ post v

theorem WpConverges.of_done {σ α : Type} {step : σ → Step σ α} {s : σ} {v : α}
    {post : α → Prop} (hd : step s = .done v) (hp : post v) :
    WpConverges step s post :=
  ⟨1, v, by simp [evalFuel, hd], hp⟩

theorem WpConverges.of_cont {σ α : Type} {step : σ → Step σ α} {s s' : σ}
    {post : α → Prop} (hs : step s = .cont s') (h : WpConverges step s' post) :
    WpConverges step s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k + 1, v, by simp [evalFuel, hs, hk], hp⟩

theorem WpConverges.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {P Q : α → Prop} (himp : ∀ v, P v → Q v) (h : WpConverges step s P) :
    WpConverges step s Q := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k, v, hk, himp v hp⟩

/-- Fault soundness: a faulting state never converges. -/
theorem not_wpConverges_of_faulted {σ α : Type} {step : σ → Step σ α} {s : σ}
    {k : Nat} {post : α → Prop} (hf : evalFuel step k s = .faulted) :
    ¬ WpConverges step s post := by
  rintro ⟨k', v, hk', _⟩
  exact evalFuel_faulted_ne_halted hf hk'

/-- Converged return values are unique. -/
theorem WpConverges.deterministic {σ α : Type} {step : σ → Step σ α} {s : σ}
    {v₁ v₂ : α} (h₁ : WpConverges step s (· = v₁)) (h₂ : WpConverges step s (· = v₂)) :
    v₁ = v₂ := by
  obtain ⟨k₁, w₁, hk₁, hw₁⟩ := h₁
  obtain ⟨k₂, w₂, hk₂, hw₂⟩ := h₂
  subst hw₁ hw₂
  exact evalFuel_halted_deterministic hk₁ hk₂

/-- Multi-step segment reachability of an intermediate predicate `mid`. -/
inductive StepsTo {σ α : Type} (step : σ → Step σ α) : σ → (σ → Prop) → Prop where
  | refl {s : σ} {mid : σ → Prop} (h : mid s) : StepsTo step s mid
  | step {s s' : σ} {mid : σ → Prop}
      (hstep : step s = .cont s') (hrest : StepsTo step s' mid) : StepsTo step s mid

/-- **Sequential bind rule**: fuel budgets are synthesized existentially across
segments, so user proofs never mention fuel numerals. -/
theorem StepsTo.bind_wp {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid : σ → Prop} {post : α → Prop}
    (hseg : StepsTo step s mid)
    (hcont : ∀ s₁, mid s₁ → WpConverges step s₁ post) :
    WpConverges step s post := by
  induction hseg with
  | refl hm => exact hcont _ hm
  | step hs _ ih => exact WpConverges.of_cont hs (ih hcont)

theorem StepsTo.trans {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop}
    (h₁ : StepsTo step s mid₁) (h₂ : ∀ s₁, mid₁ s₁ → StepsTo step s₁ mid₂) :
    StepsTo step s mid₂ := by
  induction h₁ with
  | refl hm => exact h₂ _ hm
  | step hs _ ih => exact StepsTo.step hs (ih h₂)

theorem StepsTo.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop} (himp : ∀ s₁, mid₁ s₁ → mid₂ s₁)
    (h : StepsTo step s mid₁) : StepsTo step s mid₂ :=
  h.trans (fun s₁ hm => StepsTo.refl (himp s₁ hm))

/-! #### Header-Targeted Stepping (`TargetOutcome`, `FirstHitIn`, `runToTarget`) -/

/-- Outcome of a header-targeted segment run. The four outcomes are pairwise
distinct constructors: reaching the target, halting, getting stuck, and running
out of the internal step ceiling are never conflated. -/
inductive TargetOutcome (σ α : Type) where
  | reached (s : σ)
  | halted (v : α)
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr

/-- Zero-or-more-step search for the next target state. -/
def runUntilTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → TargetOutcome σ α
  | 0, s => if atTarget s then .reached s else .outOfFuel
  | bound + 1, s =>
    if atTarget s then .reached s
    else
      match step s with
      | .cont s' => runUntilTarget step atTarget bound s'
      | .done v => .halted v
      | .fault => .stuck

/-- One mandatory step (so starting *at* a loop header advances through the
body) followed by the search for the next target entry within `bound` extra
steps. -/
def runToTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool)
    (bound : Nat) (s : σ) : TargetOutcome σ α :=
  match step s with
  | .cont s' => runUntilTarget step atTarget bound s'
  | .done v => .halted v
  | .fault => .stuck

theorem runUntilTarget_reached_atTarget {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → atTarget s_hit = true
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- A `.reached` outcome always lands on a target state. -/
theorem runToTarget_reached_atTarget {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) : atTarget s_hit = true := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' => rw [hs] at h; exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem stepsTo_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → StepsTo step s (· = s_hit)
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **Target arrival soundness** (generic form). -/
theorem stepsTo_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    StepsTo step s (· = s_hit) := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem wpConverges_of_runUntilTarget_halted {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) {post : α → Prop} :
    ∀ (bound : Nat) (s : σ) (v : α),
      runUntilTarget step atTarget bound s = .halted v → post v → WpConverges step s post
  | 0, s, _, h, _ => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, v, h, hp => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact WpConverges.of_cont hs
          (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
      | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
      | fault => rw [hs] at h; cases h

/-- **Halting soundness** (generic form). -/
theorem wpConverges_of_runToTarget_halted {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {v : α} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .halted v) (hp : post v) :
    WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact WpConverges.of_cont hs (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
  | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
  | fault => rw [hs] at h; cases h

theorem faulted_of_runUntilTarget_stuck {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s : σ),
      runUntilTarget step atTarget bound s = .stuck → ∃ k, evalFuel step k s = .faulted
  | 0, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
        exact ⟨k + 1, by simp [evalFuel, hs, hk]⟩
      | done _ => rw [hs] at h; cases h
      | fault => exact ⟨1, by simp [evalFuel, hs]⟩

/-- **Stuck soundness**: a `.stuck` outcome is a genuine fault, so the state can
never converge (stuck is never conflated with halting). -/
theorem not_wpConverges_of_runToTarget_stuck {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .stuck) : ¬ WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
    exact not_wpConverges_of_faulted (k := k + 1) (by simp [evalFuel, hs, hk])
  | done _ => rw [hs] at h; cases h
  | fault => exact not_wpConverges_of_faulted (k := 1) (by simp [evalFuel, hs])

theorem runUntilTarget_mono_bound {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ {b₁ b₂ : Nat} (s : σ),
      runUntilTarget step atTarget b₁ s ≠ .outOfFuel → b₁ ≤ b₂ →
      runUntilTarget step atTarget b₂ s = runUntilTarget step atTarget b₁ s
  | 0, 0, _, _, _ => rfl
  | 0, b₂ + 1, s, hne, _ => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false => rw [ht] at hne; exact absurd rfl hne
  | _ + 1, 0, _, _, hle => absurd hle (Nat.not_succ_le_zero _)
  | b₁ + 1, b₂ + 1, s, hne, hle => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false =>
      rw [ht] at hne
      cases hs : step s with
      | cont s' =>
        rw [hs] at hne
        exact runUntilTarget_mono_bound step atTarget s' hne (Nat.le_of_succ_le_succ hle)
      | done _ => rfl
      | fault => rfl

/-- **Ceiling monotonicity**: once a run is conclusive (`≠ .outOfFuel`) under
`b₁`, every larger ceiling returns the identical outcome. -/
theorem runToTarget_mono_bound {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {b₁ b₂ : Nat} {s : σ}
    (hne : runToTarget step atTarget b₁ s ≠ .outOfFuel) (hle : b₁ ≤ b₂) :
    runToTarget step atTarget b₂ s = runToTarget step atTarget b₁ s := by
  unfold runToTarget at hne ⊢
  cases hs : step s with
  | cont s' =>
    rw [hs] at hne
    exact runUntilTarget_mono_bound step atTarget s' hne hle
  | done _ => rfl
  | fault => rfl

/-- `FirstHitIn n s s_hit`: after one mandatory step and `n` further silent
steps through non-target states, `s` reaches the target state `s_hit`, and no
earlier visited state (other than possibly `s` itself) is a target. -/
inductive FirstHitIn {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → σ → Prop where
  | here {s s' : σ} (hs : step s = .cont s') (ht : atTarget s' = true) :
      FirstHitIn step atTarget 0 s s'
  | later {n : Nat} {s s' s_hit : σ} (hs : step s = .cont s') (hnt : atTarget s' = false)
      (hrest : FirstHitIn step atTarget n s' s_hit) :
      FirstHitIn step atTarget (n + 1) s s_hit

/-- The first target re-entry is unique (and so is its step count). -/
theorem FirstHitIn.unique {σ α : Type} {step : σ → Step σ α} {atTarget : σ → Bool} :
    ∀ {n₁ n₂ : Nat} {s a b : σ},
      FirstHitIn step atTarget n₁ s a → FirstHitIn step atTarget n₂ s b → a = b ∧ n₁ = n₂
  | _, _, _, _, _, .here hs₁ ht₁, .here hs₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, .here hs₁ ht₁, .later hs₂ hnt₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₁] at hnt₂; cases hnt₂
  | _, _, _, _, _, .later hs₁ hnt₁ _, .here hs₂ ht₂ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₂] at hnt₁; cases hnt₁
  | _, _, _, _, _, .later hs₁ _ h₁, .later hs₂ _ h₂ => by
    rw [hs₁] at hs₂; cases hs₂
    obtain ⟨hab, hn⟩ := FirstHitIn.unique h₁ h₂
    exact ⟨hab, congrArg (· + 1) hn⟩

theorem firstHitIn_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s₀ s s_hit : σ), step s₀ = .cont s →
      runUntilTarget step atTarget bound s = .reached s_hit →
      ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s₀ s_hit
  | 0, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.le_refl 0, .here h0 ht⟩
    | false => rw [ht] at h; cases h
  | bound + 1, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.zero_le _, .here h0 ht⟩
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨n, hn, hfh⟩ := firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
        exact ⟨n + 1, Nat.succ_le_succ hn, .later h0 ht hfh⟩
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **No overshoot**: a `.reached s_hit` outcome is exactly the *first* target
re-entry (within the ceiling); combined with `FirstHitIn.unique`, the stepper
can never skip past a loop header, even on self-loops. -/
theorem firstHitIn_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s s_hit := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem runUntilTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} :
    ∀ {n : Nat} {s₀ s_hit : σ}, FirstHitIn step atTarget n s₀ s_hit →
      ∀ (s : σ), step s₀ = .cont s → ∀ (bound : Nat), n ≤ bound →
        runUntilTarget step atTarget bound s = .reached s_hit
  | _, _, _, .here hs ht, s, h0, bound, _ => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => unfold runUntilTarget; rw [ht]; rfl
    | succ b => unfold runUntilTarget; rw [ht]; rfl
  | _, _, _, .later (n := n) (s' := s') hs hnt hrest, s, h0, bound, hle => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => exact absurd hle (Nat.not_succ_le_zero n)
    | succ b =>
      unfold runUntilTarget
      rw [hnt]
      cases hrest with
      | here hs' ht' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.here hs' ht') _ hs' b (Nat.zero_le b)
      | later hs' hnt' hrest' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.later hs' hnt' hrest') _ hs' b
          (Nat.le_of_succ_le_succ hle)

/-- **Completeness**: the first target re-entry is found by every sufficiently
large ceiling, so the ceiling only affects completeness, never soundness. -/
theorem runToTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {n bound : Nat} {s s_hit : σ}
    (h : FirstHitIn step atTarget n s s_hit) (hle : n ≤ bound) :
    runToTarget step atTarget bound s = .reached s_hit := by
  cases h with
  | here hs ht =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.here hs ht) _ hs bound hle
  | later hs hnt hrest =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.later hs hnt hrest) _ hs bound hle

/-! #### Structural `[lo, hi)` Range Loops (`forRangeUpAux`, `PureMirExec.forRangeUp`, `wpConverges_forRangeUp`, `stepsTo_forRangeUp`) -/

/-- Structural range fold over `[i, hi)` indexed by the remaining trip count. -/
def forRangeUpAux {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    (i rem : Nat) → lo ≤ i → i + rem = hi → α → α
  | _, 0, _, _, acc => acc
  | i, rem + 1, hlo, hsum, acc =>
    forRangeUpAux lo hi step (i + 1) rem (Nat.le_succ_of_le hlo) (by omega)
      (step i hlo (by omega) acc)

/-- Structurally recursive `for i in lo..hi` fold (kernel-reducible). -/
protected def forRangeUp {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo ≤ hi then
    forRangeUpAux lo hi step lo (hi - lo) (Nat.le_refl lo) (by omega) init
  else
    init

theorem forRangeUpAux_induction {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      inv i acc →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) a, inv j a → inv (j + 1) (step j hjlo hjlt a)) →
      inv hi (forRangeUpAux lo hi step i rem hlo hsum acc)
  | i, 0, _, hsum, acc, hinv, _ => by
    have : i = hi := by omega
    subst this
    exact hinv
  | i, rem + 1, hlo, hsum, acc, hinv, hstep =>
    forRangeUpAux_induction lo hi step inv (i + 1) rem _ _ _ (hstep i hlo (by omega) acc hinv) hstep

/-- **Structural `[lo, hi)` loop induction**. -/
protected theorem forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (PureMirExec.forRangeUp lo hi init step) := by
  unfold PureMirExec.forRangeUp
  simp only [hle, ↓reduceDIte]
  exact forRangeUpAux_induction lo hi step inv lo (hi - lo) _ _ init hinit hstep

/-- Empty-range identity (`hi ≤ lo`): `PureMirExec.forRangeUp` returns `init`
immediately in both the `lo = hi` (`hi - lo = 0`) and `hi < lo` branches. -/
protected theorem forRangeUp_eq_init_of_ge {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (hge : hi ≤ lo) :
    PureMirExec.forRangeUp lo hi init step = init := by
  unfold PureMirExec.forRangeUp
  by_cases hle : lo ≤ hi
  · have heq : hi = lo := Nat.le_antisymm hge hle
    subst heq
    simp [forRangeUpAux]
  · simp [hle]

theorem forRangeUpAux_eq_live {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      forRangeUpAux lo hi step i rem hlo hsum acc =
        Anneal.MirLoops.forRangeUp i hi acc
          (fun j hj hlt a => step j (Nat.le_trans hlo hj) hlt a)
  | i, 0, _, _, _ => by
    rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]
    rfl
  | i, rem + 1, _, _, _ => by
    rw [Anneal.MirLoops.forRangeUp_step_of_lt _ _ _ _ (by omega)]
    exact forRangeUpAux_eq_live lo hi step (i + 1) rem _ _ _

/-- **Bridge to the live `Anneal.MirLoops.forRangeUp`** in `Anneal.PureMirExec`. -/
protected theorem forRangeUp_eq_live {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    PureMirExec.forRangeUp lo hi init step = Anneal.MirLoops.forRangeUp lo hi init step := by
  unfold PureMirExec.forRangeUp
  split
  · next hle => exact forRangeUpAux_eq_live lo hi step lo (hi - lo) _ _ init
  · next hgt => rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]

/-- Non-empty step-unrolling identity (`lo < hi`) for `PureMirExec.forRangeUp`. -/
protected theorem forRangeUp_step_of_lt {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (h : lo < hi) :
    PureMirExec.forRangeUp lo hi init step =
      PureMirExec.forRangeUp (lo + 1) hi (step lo (Nat.le_refl _) h init)
        (fun i h_le h_lt a => step i (Nat.le_trans (Nat.le_succ _) h_le) h_lt a) := by
  rw [PureMirExec.forRangeUp_eq_live, PureMirExec.forRangeUp_eq_live,
    Anneal.MirLoops.forRangeUp_step_of_lt lo hi init step h]

theorem stepsTo_forRangeUpAux {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ),
      inv i a s →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
        inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc))) →
      StepsTo stepOp s (inv hi (forRangeUpAux lo hi f i rem hlo hsum a))
  | i, 0, _, hsum, _, s, hinv, _ => by
    have hi_eq : i = hi := by omega
    subst hi_eq
    exact StepsTo.refl hinv
  | i, rem + 1, hlo, hsum, a, s, hinv, hiter => by
    have hlt : i < hi := by omega
    exact (hiter i hlo hlt a s hinv).trans (fun s₁ hinv₁ =>
      stepsTo_forRangeUpAux stepOp lo hi f inv (i + 1) rem _ _ (f i hlo hlt a) s₁ hinv₁ hiter)

/-- **Fuel-free range loop as a segment (`StepsTo`)**: unlike
`wpConverges_forRangeUp`, which ends the program, this rule reaches the loop
*exit state* `inv hi (forRangeUp lo hi init f)` as an intermediate segment, so a
loop can sit inside another loop's iteration (nested loops) or be followed by
further `StepsTo` segments, still with no step count or fuel numeral. -/
theorem stepsTo_forRangeUp {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (s₀ : σ) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a))) :
    StepsTo stepOp s₀ (inv hi (PureMirExec.forRangeUp lo hi init f)) := by
  unfold PureMirExec.forRangeUp
  simp only [hle, ↓reduceDIte]
  exact stepsTo_forRangeUpAux stepOp lo hi f inv lo (hi - lo) _ _ init s₀ hinit hiter

theorem wpConverges_forRangeUpAux {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (post : out → Prop)
    (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ)
    (hinv : inv i a s)
    (hiter : ∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
      inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc)))
    (hexit : ∀ s_exit, inv hi (forRangeUpAux lo hi f i rem hlo hsum a) s_exit →
      WpConverges stepOp s_exit post) :
    WpConverges stepOp s post :=
  (stepsTo_forRangeUpAux stepOp lo hi f inv i rem hlo hsum a s hinv hiter).bind_wp hexit

/-- **Fuel-free range-loop rule**: per-iteration segment reachability plus an
exit obligation imply convergence, with no step count or fuel numeral
(factored directly through `stepsTo_forRangeUp` and `StepsTo.bind_wp`). -/
theorem wpConverges_forRangeUp {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (s₀ : σ) (post : out → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (PureMirExec.forRangeUp lo hi init f) s_exit → WpConverges stepOp s_exit post) :
    WpConverges stepOp s₀ post :=
  (stepsTo_forRangeUp stepOp lo hi init f inv s₀ hle hinit hiter).bind_wp hexit

/-! #### Live `CapturedMir` Small-Step Embedding (`mirStep`) & Header-Targeted `runMirToBlock` -/

/-- Embedding of the live trusted step function `stepMirFn` into the generic
machine. Both silent `.tau` transitions and `MirObsE` observation steps
(`.vis (.inr (.inl (.emit _)))`, including `.event _` emitted by live
`.switchInt` terminators and `.silent`) continue, and root returns halt;
external calls and faults are mapped conservatively to `.fault`, matching live
`Anneal.FunctionalTranslation.runMirToBlock`. -/
def mirStep (body : CapturedMir) (s : MachineState) : Step MachineState MirOutcome :=
  match stepMirFn body s with
  | .tau (.running s') => .cont s'
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .cont s'
    | _ => .fault
  | .ret out => .done out
  | _ => .fault

theorem stepMirFn_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    (h : mirStep body s = .cont s') :
    stepMirFn body s = .tau (.running s') ∨
      ∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧ k PUnit.unit = .running s' := by
  unfold mirStep at h
  split at h
  · rename_i s'' heq
    cases h
    exact Or.inl heq
  · rename_i obs k heq
    split at h
    · rename_i s'' hk
      cases h
      exact Or.inr ⟨obs, k, heq, hk⟩
    · cases h
  · cases h
  · cases h

theorem stepMirFn_of_mirStep_done {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : mirStep body s = .done out) : stepMirFn body s = .ret out := by
  unfold mirStep at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i out' heq
    cases h
    exact heq
  · cases h

theorem mirStepsConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirStepsConverges body s' mid post) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirStepsConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.MirFuelFree.wpMirStepsSym
      Anneal.MirFuelFree.wpMirExecStepsSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTreeNoCall_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeNoCallWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.MirFuelFree.wpMirExecStepsSym fuel body (k PUnit.unit) _ post
      rw [hk]
      exact h_wp)

/-- **Bridge to the live `Anneal.MirFuelFree.MirStepsConverges`**: generic
segment reachability over `mirStep` is live fuel-free reachability (including
across all `MirObsE` observation steps). -/
theorem mirStepsConverges_of_stepsTo {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : StepsTo (mirStep body) s mid) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  induction h with
  | refl hm => exact Anneal.MirFuelFree.MirStepsConverges.refl hm
  | step hs _ ih => exact mirStepsConverges_of_mirStep_cont hs ih

theorem mirWpConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirWpConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body (k PUnit.unit) post
      rw [hk]
      exact h_wp)

theorem mirWpConverges_of_evalFuel {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ (k : Nat) (s : MachineState) (v : MirOutcome),
      evalFuel (mirStep body) k s = .halted v → post v →
      Anneal.MirFuelFree.MirWpConverges body s post
  | 0, _, _, h, _ => by cases h
  | k + 1, s, v, h, hp => by
    unfold evalFuel at h
    cases hs : mirStep body s with
    | cont s' =>
      rw [hs] at h
      exact mirWpConverges_of_mirStep_cont hs
        (mirWpConverges_of_evalFuel k s' v h hp)
    | done out =>
      rw [hs] at h
      cases h
      exact Anneal.MirFuelFree.MirWpConverges.ret_of_step (stepMirFn_of_mirStep_done hs) hp
    | fault =>
      rw [hs] at h
      cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirWpConverges`**. -/
theorem mirWpConverges_of_wpConverges {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} (h : WpConverges (mirStep body) s post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact mirWpConverges_of_evalFuel k s v hk hp

/-- Mixed composition: a generic segment followed by a live continuation
(through the live `MirWpConverges.bind`). -/
theorem mirWpConverges_of_stepsTo_bind {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : StepsTo (mirStep body) s mid)
    (h₂ : ∀ s', mid s' → Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  Anneal.MirFuelFree.MirWpConverges.bind (mirStepsConverges_of_stepsTo h₁) h₂

theorem mirNoCallWpConverges_of_mirStep_done {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (hs : mirStep body s = .done out) (hp : post out) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post := by
  have hret := stepMirFn_of_mirStep_done hs
  refine ⟨1, ?_⟩
  unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirNoCallSym
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecNoCallSym
  rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTreeNoCall_eq,
    Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
    Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeNoCallWP_eq]
  dsimp only [stepMirState]
  rw [hret]
  exact hp

theorem mirNoCallWpConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirNoCallWpConverges body s' post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  Anneal.MirFuelFree.MirNoCallWpConverges.bind
    (mirStepsConverges_of_mirStep_cont (mid := (· = s')) (post := post) hs
      (Anneal.MirFuelFree.MirStepsConverges.refl rfl))
    (fun _ heq => heq ▸ hnext)

theorem mirNoCallWpConverges_of_evalFuel {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ (k : Nat) (s : MachineState) (v : MirOutcome),
      evalFuel (mirStep body) k s = .halted v → post v →
      Anneal.MirFuelFree.MirNoCallWpConverges body s post
  | 0, _, _, h, _ => by cases h
  | k + 1, s, v, h, hp => by
    unfold evalFuel at h
    cases hs : mirStep body s with
    | cont s' =>
      rw [hs] at h
      exact mirNoCallWpConverges_of_mirStep_cont hs
        (mirNoCallWpConverges_of_evalFuel k s' v h hp)
    | done out =>
      rw [hs] at h
      cases h
      exact mirNoCallWpConverges_of_mirStep_done hs hp
    | fault =>
      rw [hs] at h
      cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirNoCallWpConverges`**. -/
theorem mirNoCallWpConverges_of_wpConverges {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} (h : WpConverges (mirStep body) s post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact mirNoCallWpConverges_of_evalFuel k s v hk hp

/-- Mixed call-free composition: a generic `StepsTo` segment followed by a live
`MirNoCallWpConverges` continuation. -/
theorem mirNoCallWpConverges_of_stepsTo_bind {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : StepsTo (mirStep body) s mid)
    (h₂ : ∀ s', mid s' → Anneal.MirFuelFree.MirNoCallWpConverges body s' post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  Anneal.MirFuelFree.MirNoCallWpConverges.bind (mirStepsConverges_of_stepsTo h₁) h₂

/-- Ceiling for live header-targeted stepping: the total number of statements
and terminators of the body (one live step each). -/
def mirSegmentBound (body : CapturedMir) : Nat :=
  body.basicBlocks.foldl (fun acc bb => acc + bb.statements.length + 1) 0

theorem mirSegmentBound_foldl_ge (l : List BasicBlockData) :
    ∀ a : Nat, a + l.length ≤ l.foldl (fun acc bb => acc + bb.statements.length + 1) a := by
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons bb rest ih =>
    intro a
    refine Nat.le_trans ?_ (ih (a + bb.statements.length + 1))
    rw [List.length_cons]
    omega

/-- The live ceiling is derived from the CFG: it is at least the number of basic
blocks (`body.basicBlocks.length`), plus one step per statement. -/
theorem basicBlocks_length_le_mirSegmentBound (body : CapturedMir) :
    body.basicBlocks.length ≤ mirSegmentBound body := by
  have h := mirSegmentBound_foldl_ge body.basicBlocks 0
  rw [Nat.zero_add] at h
  exact h

/-- Header-targeted stepping over live MIR: takes one mandatory step and stops
at the first statement of basic block `target`. -/
protected def runMirToBlock (body : CapturedMir) (target : BasicBlockIdx) (s : MachineState) :
    TargetOutcome MachineState MirOutcome :=
  runToTarget (mirStep body)
    (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) (mirSegmentBound body) s

theorem runMirToBlock_reached_block_and_stmt {body : CapturedMir}
    {target : BasicBlockIdx} {s s' : MachineState}
    (h : PureMirExec.runMirToBlock body target s = .reached s') :
    s'.frame.blockIdx = target ∧ s'.frame.stmtIdx = 0 := by
  unfold PureMirExec.runMirToBlock at h
  have ht0 := runToTarget_reached_atTarget h
  have ht := Bool.and_eq_true_iff.mp ht0
  exact ⟨beq_iff_eq.mp ht.1, beq_iff_eq.mp ht.2⟩

theorem mirStepsConverges_of_runMirToBlock_reached {body : CapturedMir}
    {target : BasicBlockIdx} {s s' : MachineState} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .reached s') :
    Anneal.MirFuelFree.MirStepsConverges body s (· = s') post :=
  mirStepsConverges_of_stepsTo (stepsTo_of_runToTarget_reached h)

theorem mirWpConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {v : MirOutcome} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .halted v) (hp : post v) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  mirWpConverges_of_wpConverges (wpConverges_of_runToTarget_halted h hp)

theorem mirNoCallWpConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {v : MirOutcome} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .halted v) (hp : post v) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  mirNoCallWpConverges_of_wpConverges (wpConverges_of_runToTarget_halted h hp)

theorem not_wpConverges_of_runMirToBlock_stuck {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .stuck) :
    ¬ WpConverges (mirStep body) s post :=
  not_wpConverges_of_runToTarget_stuck h

end Anneal.PureMirExec
end MovedPureMirExecHelpers
