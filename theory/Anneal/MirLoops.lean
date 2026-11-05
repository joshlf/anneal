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

def countTo10Body : CapturedMir :=
  mkMirBody "Anneal::MirLoops::countTo10" 0
      [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
      , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" } ]
      [ { statements := [ { kind := .assign { local_ := 1, projection := [] } (.use (constU32 0)), span := "init" } ], terminator := { kind := .goto 1, span := "goto bb1" }, isCleanup := false }
      , { statements := [], terminator := { kind := .switchInt (.copy { local_ := 1, projection := [] }) { branches := [(10, 3)], otherwise := 2 }, span := "switch" }, isCleanup := false }
      , { statements := [ { kind := .assign { local_ := 1, projection := [] } (.binaryOp .add (.copy { local_ := 1, projection := [] }) (constU32 1)), span := "add" } ], terminator := { kind := .goto 1, span := "goto bb1" }, isCleanup := false }
      , { statements := [ { kind := .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 1, projection := [] })), span := "ret_assign" } ], terminator := { kind := .return_, span := "ret" }, isCleanup := false }
      ]

def countStateMem (bb : Nat) (stmt : Nat) (i : Nat) (mem : Memory) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [ .init (.scalar ⟨0, 4⟩), .init (.scalar ⟨i, 4⟩) ] }, memory := mem }

def countStateMemRet (bb : Nat) (stmt : Nat) (i : Nat) (mem : Memory) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [ .init (.scalar ⟨i, 4⟩), .init (.scalar ⟨i, 4⟩) ] }, memory := mem }

theorem bb0_converges_mem (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) :
    MirReachState countTo10Body (countStateMem 0 0 0 mem)
      (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
  have h_step : stepMirFn countTo10Body (countStateMem 0 0 0 mem) = MirStepNode.step (countStateMem 0 1 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?]
  have h_term : stepMirFn countTo10Body (countStateMem 0 1 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) = MirStepNode.step (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length]
  apply MirReachState.step_tau h_step
  apply MirReachState.step_tau h_term
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_lt (i : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_lt : i ≠ 10) :
    MirReachState countTo10Body (countStateMem 1 0 i mem)
      (countStateMem 2 0 i mem) := by
  have h_beq : Nat.beq i 10 = false := by exact (Bool.not_eq_true _).mp (by exact h_lt ∘ Nat.eq_of_beq_eq_true)
  have h_fn : stepMirFn countTo10Body (countStateMem 1 0 i mem) = MirStepNode.emitStep (.event i) (countStateMem 2 0 i mem) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, Trusted.Sequence.length, evalOperand, readProjectedValue, lookupSwitchTarget, h_beq]
  apply MirReachState.step_emit h_fn
  apply MirStepsConverges.refl
  rfl

theorem bb2_converges_mem (i : Nat) (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) :
    MirReachState countTo10Body (countStateMem 2 0 i mem)
      (countStateMem 1 0 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
  have h_step : stepMirFn countTo10Body (countStateMem 2 0 i mem) = MirStepNode.step (countStateMem 2 1 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?]
  have h_term : stepMirFn countTo10Body (countStateMem 2 1 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) = MirStepNode.step (countStateMem 1 0 ((i + 1) % 4294967296) { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length]
  apply MirReachState.step_tau h_step
  apply MirReachState.step_tau h_term
  apply MirStepsConverges.refl
  rfl

theorem bb1_converges_eq10 (mem : Memory) (h_callee : mem.activeCallee = none) :
    MirReachState countTo10Body (countStateMem 1 0 10 mem)
      (countStateMem 3 0 10 mem) := by
  have h_fn : stepMirFn countTo10Body (countStateMem 1 0 10 mem) = MirStepNode.emitStep (.event 10) (countStateMem 3 0 10 mem) := by
      unfold stepMirFn
      dsimp [countStateMem]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, Trusted.Sequence.length, evalOperand, readProjectedValue, lookupSwitchTarget]
  apply MirReachState.step_emit h_fn
  apply MirStepsConverges.refl
  rfl

theorem bb3_converges_mem (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) (h_stack : mem.callStack = []) :
    MirWpConverges countTo10Body (countStateMem 3 0 10 mem)
      (fun out => out = Outcome.normal (Value.scalar ⟨10, 4⟩, { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none })) := by
  have h_step : stepMirFn countTo10Body (countStateMem 3 0 10 mem) = MirStepNode.step (countStateMemRet 3 1 10 { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none }) := by
      unfold stepMirFn
      dsimp [countStateMem, countStateMemRet]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalStmt, h_callee, h_prot, evalOperand, readProjectedValue, evalRvalue, advanceStmt, Trusted.Sequence.set?]
  have h_term : stepMirFn countTo10Body (countStateMemRet 3 1 10 { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none }) = MirStepNode.retNormal (Value.scalar ⟨10, 4⟩) { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none } := by
      unfold stepMirFn
      dsimp [countStateMemRet]
      simp [Option.getD, countTo10Body, mkMirBody, constU32, get?, Trusted.Sequence.get?, evalTerminator, h_callee, h_prot, Trusted.Sequence.length, h_stack]
  have h_wp_term : MirWpConverges countTo10Body (countStateMemRet 3 1 10 { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none }) (fun out => out = Outcome.normal (Value.scalar ⟨10, 4⟩, { mem with borrows := invalidateConflictingBorrows mem.borrows 0 none })) := by
      apply MirWpConverges.ret_of_step h_term
      rfl
  exact MirWpConverges.step_tau h_step h_wp_term

theorem countTo10_terminates (mem : Memory) (h_callee : mem.activeCallee = none) (h_prot : mem.activeProtectors = []) (h_stack : mem.callStack = []) :
    MirWpConverges countTo10Body (countStateMem 0 0 0 mem)
      (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨10, 4⟩, mem')) := by
  have h0 := bb0_converges_mem mem h_callee h_prot
  apply MirWpConverges.bind_reachState h0
  have h_loop : MirWpConverges countTo10Body (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none })
    (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨10, 4⟩, mem')) := by
    refine mirWpConverges_forRangeUp 0 10 () (fun _ _ _ _ => ()) countTo10Body
      (fun i _ s => i ≤ 10 ∧ ∃ m, s = countStateMem 1 0 i m ∧ m.activeCallee = none ∧ m.activeProtectors = [] ∧ m.callStack = [])
      (countStateMem 1 0 0 { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none })
      (fun out => ∃ mem', out = Outcome.normal (Value.scalar ⟨10, 4⟩, mem'))
      ?_
      ?_
      ?_
    · exact ⟨by decide, { mem with borrows := invalidateConflictingBorrows mem.borrows 1 none }, rfl, h_callee, h_prot, h_stack⟩
    · intro i h_le h_lt _ s h_inv
      rcases h_inv with ⟨h_i_le_10, m, h_eq, hm_callee, hm_prot, hm_stack⟩
      subst h_eq
      have h1 := bb1_converges_lt i m hm_callee (Nat.ne_of_lt h_lt)
      have h2 := bb2_converges_mem i m hm_callee hm_prot
      have h12 := MirReachState.trans h1 h2
      have hi_mod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hi_mod] at h12
      exact MirStepsConverges.mono (post₂ := fun _ => False) (fun s' hs' => ⟨Nat.succ_le_of_lt h_lt, { m with borrows := invalidateConflictingBorrows m.borrows 1 none }, hs', hm_callee, hm_prot, hm_stack⟩) (fun _ h => False.elim h) h12
    · intro i a s h_ge h_inv
      rcases h_inv with ⟨h_i_le_10, m, h_eq, hm_callee, hm_prot, hm_stack⟩
      subst h_eq
      have h_i_eq : i = 10 := Nat.le_antisymm h_i_le_10 h_ge
      subst h_i_eq
      have h1 := bb1_converges_eq10 m hm_callee
      have h3 := bb3_converges_mem m hm_callee hm_prot hm_stack
      apply MirWpConverges.bind_reachState h1
      exact MirWpConverges.mono (fun out h => ⟨{ m with borrows := invalidateConflictingBorrows m.borrows 0 none }, h⟩) h3
  exact h_loop

end Anneal.MirLoops
