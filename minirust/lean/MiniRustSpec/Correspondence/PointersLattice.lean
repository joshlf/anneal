/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointersCore

/-!
# Raw pointers and references in both semantics: the `PtrLocalState` lattice (MR-3.1, MR-3.2)

Second of the four modules that make up `MiniRustSpec.Correspondence.Pointers` (see its module
documentation; the split keeps every declaration, name, and proof unchanged):

* the `PtrLocalState` join-semilattice, monotonicity of the transfer functions, finite-fuel
  convergence, and the least fixed point of the flow-sensitive pointer analysis behind
  `ptrAliasingOk` (`PtrEnvOk`, `evalTargetPlace`, `evalPtrLoad`, `PtrEnvOk.foreignRead`, ...);
* the symbolic Tree Borrows state machine and protector invariants
  (`spec/mem/tree_borrows/*`).

It builds on `PointersCore`; `PointersMachine` continues with the `Machine<BM>` / `Mach`
equivalence.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence

/-! ### `PtrLocalState` join-semilattice, monotonicity, finite-fuel convergence, and least fixed point -/

theorem subsumesPtrLocalState_refl (s : PtrLocalState) :
    subsumesPtrLocalState s s = true := by
  cases s with
  | empty | disabled => rfl
  | live t ps hot writable =>
    cases hot <;> cases writable <;> cases t <;> simp [subsumesPtrLocalState]

theorem subsumesPtrLocalState_disabled_right (s : PtrLocalState) :
    subsumesPtrLocalState s .disabled = true := by
  cases s <;> rfl

theorem subsumesPtrLocalState_freeze_right (s : PtrLocalState) :
    subsumesPtrLocalState s (freezePtrState s) = true := by
  cases s with
  | empty | disabled => rfl
  | live t ps hot writable =>
    cases hot <;> cases writable <;> cases t <;> simp [freezePtrState, subsumesPtrLocalState]

theorem freezePtrState_mono {s1 s2 : PtrLocalState}
    (h : subsumesPtrLocalState s1 s2 = true) :
    subsumesPtrLocalState (freezePtrState s1) (freezePtrState s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> simp_all [freezePtrState, subsumesPtrLocalState]
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h
    | disabled => rfl
    | live t2 ps2 h2 w2 =>
      simp only [freezePtrState, subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at h ⊢
      exact ⟨⟨⟨h.1.1.1, rfl⟩, h.1.2⟩, h.2⟩

theorem subsumesPtrLocalState_trans {s1 s2 s3 : PtrLocalState}
    (h12 : subsumesPtrLocalState s1 s2 = true)
    (h23 : subsumesPtrLocalState s2 s3 = true) :
    subsumesPtrLocalState s1 s3 = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> cases s3 <;> simp_all [subsumesPtrLocalState]
  | live t1 ps1 hh1 ww1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h12
    | disabled =>
      cases s3 <;> simp_all [subsumesPtrLocalState]
    | live t2 ps2 hh2 ww2 =>
      cases s3 with
      | empty => simp [subsumesPtrLocalState] at h23
      | disabled => rfl
      | live t3 ps3 hh3 ww3 =>
        simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
          List.contains_iff_mem] at h12 h23 ⊢
        refine ⟨⟨⟨by cases hh1 <;> cases hh2 <;> cases hh3 <;> simp_all,
                  by cases ww1 <;> cases ww2 <;> cases ww3 <;> simp_all⟩, ?_⟩,
          fun r hr => h12.2 r (h23.2 r hr)⟩
        cases t3 with
        | none => trivial
        | some q3 =>
          simp only [decide_eq_true_eq] at h23 ⊢
          rw [h23.1.2] at h12
          simpa using h12.1.2

theorem joinPtrLocalState_subsumes_left (s1 s2 : PtrLocalState) :
    subsumesPtrLocalState s1 (joinPtrLocalState s1 s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled => cases s2 <;> rfl
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => exact subsumesPtrLocalState_refl _
    | disabled => rfl
    | live t2 ps2 h2 w2 =>
      simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem]
      refine ⟨⟨⟨by cases h1 <;> cases h2 <;> rfl, by cases w1 <;> cases w2 <;> rfl⟩, ?_⟩,
        fun r hr => hr.1⟩
      by_cases h : (t1 == t2) = true
      · simp only [h, ↓reduceIte]
        cases t1 <;> simp
      · simp [h]

theorem joinPtrLocalState_subsumes_right (s1 s2 : PtrLocalState) :
    subsumesPtrLocalState s2 (joinPtrLocalState s1 s2) = true := by
  cases s1 with
  | empty => exact subsumesPtrLocalState_refl _
  | disabled => cases s2 <;> rfl
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => rfl
    | disabled => rfl
    | live t2 ps2 h2 w2 =>
      simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem]
      refine ⟨⟨⟨by cases h1 <;> cases h2 <;> rfl, by cases w1 <;> cases w2 <;> rfl⟩, ?_⟩,
        fun r hr => hr.2⟩
      by_cases h : (t1 == t2) = true
      · have heq : t1 = t2 := eq_of_beq h
        subst heq
        simp only [h, ↓reduceIte]
        cases t1 <;> simp
      · simp [h]

theorem joinPtrLocalState_least {s1 s2 u : PtrLocalState}
    (h1 : subsumesPtrLocalState s1 u = true)
    (h2 : subsumesPtrLocalState s2 u = true) :
    subsumesPtrLocalState (joinPtrLocalState s1 s2) u = true := by
  cases s1 with
  | empty => exact h2
  | disabled =>
    cases s2 <;> cases u <;> simp_all [joinPtrLocalState, subsumesPtrLocalState]
  | live t1 ps1 hh1 ww1 =>
    cases s2 with
    | empty => exact h1
    | disabled =>
      cases u <;> simp_all [joinPtrLocalState, subsumesPtrLocalState]
    | live t2 ps2 hh2 ww2 =>
      cases u with
      | empty => simp [subsumesPtrLocalState] at h1
      | disabled => rfl
      | live tu psu hhu wwu =>
        simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
          List.all_eq_true, List.mem_filter, List.contains_iff_mem] at h1 h2 ⊢
        refine ⟨⟨⟨by cases hh1 <;> cases hh2 <;> cases hhu <;> simp_all,
                  by cases ww1 <;> cases ww2 <;> cases wwu <;> simp_all⟩, ?_⟩,
          fun r hr => ⟨h1.2 r hr, h2.2 r hr⟩⟩
        cases tu with
        | none => trivial
        | some qu =>
          simp only [decide_eq_true_eq] at h1 h2 ⊢
          rw [h1.1.2, h2.1.2]
          simp

theorem subsumesPtrEnv_refl (n : Nat) (e : List PtrLocalState) :
    subsumesPtrEnv n e e = true := by
  simp [subsumesPtrEnv, List.all_eq_true, subsumesPtrLocalState_refl]

theorem subsumesPtrEnv_trans {n : Nat} {e1 e2 e3 : List PtrLocalState}
    (h12 : subsumesPtrEnv n e1 e2 = true) (h23 : subsumesPtrEnv n e2 e3 = true) :
    subsumesPtrEnv n e1 e3 = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at h12 h23 ⊢
  exact fun q hq => subsumesPtrLocalState_trans (h12 q hq) (h23 q hq)

theorem subsumesPtrEnv_initPtrEnv (n : Nat) (e : List PtrLocalState) :
    subsumesPtrEnv n (initPtrEnv n) e = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [initPtrEnv, getD_map_range _ _ _ hq]
  rfl

theorem joinPtrEnv_subsumes_left (n : Nat) (e1 e2 : List PtrLocalState) :
    subsumesPtrEnv n e1 (joinPtrEnv n e1 e2) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_subsumes_left _ _

theorem joinPtrEnv_subsumes_right (n : Nat) (e1 e2 : List PtrLocalState) :
    subsumesPtrEnv n e2 (joinPtrEnv n e1 e2) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_subsumes_right _ _

theorem joinPtrEnv_least {n : Nat} {e1 e2 u : List PtrLocalState}
    (h1 : subsumesPtrEnv n e1 u = true) (h2 : subsumesPtrEnv n e2 u = true) :
    subsumesPtrEnv n (joinPtrEnv n e1 e2) u = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at h1 h2 ⊢
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_least (h1 q hq) (h2 q hq)

theorem subsumesPtrLocalState_getD_of_length {n : Nat} {e1 e2 : List PtrLocalState}
    (hlen1 : e1.length = n) (hlen2 : e2.length = n)
    (hsub : subsumesPtrEnv n e1 e2 = true) (p : Nat) :
    subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true := by
  by_cases hp : p < n
  · simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at hsub
    exact hsub p hp
  · have h1 : e1[p]? = none := List.getElem?_eq_none (by omega)
    have h2 : e2[p]? = none := List.getElem?_eq_none (by omega)
    simp [List.getD, h1, h2, subsumesPtrLocalState]

theorem removePeerFromState_mono (i : Nat) {s1 s2 : PtrLocalState}
    (h : subsumesPtrLocalState s1 s2 = true) :
    subsumesPtrLocalState (removePeerFromState i s1) (removePeerFromState i s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> simp_all [removePeerFromState, subsumesPtrLocalState]
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h
    | disabled => rfl
    | live t2 ps2 h2 w2 =>
      simp only [removePeerFromState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem] at h ⊢
      exact ⟨h.1, fun r hr => ⟨h.2 r hr.1, hr.2⟩⟩

theorem addPeerToState_mono (i : Nat) {s1 s2 : PtrLocalState}
    (h : subsumesPtrLocalState s1 s2 = true) :
    subsumesPtrLocalState (addPeerToState i s1) (addPeerToState i s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> simp_all [addPeerToState, subsumesPtrLocalState]
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h
    | disabled => rfl
    | live t2 ps2 h2 w2 =>
      simp only [addPeerToState]
      by_cases hc2 : ps2.contains i = true
      · have hc1 : ps1.contains i = true := by
          simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
            List.contains_iff_mem] at h
          exact List.contains_iff_mem.mpr (h.2 i (List.contains_iff_mem.mp hc2))
        simp only [hc1, hc2, ↓reduceIte]
        exact h
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc1 : ps1.contains i = true
        · simp only [hc1, ↓reduceIte, subsumesPtrLocalState, Bool.and_eq_true,
            List.all_eq_true, List.contains_iff_mem] at h ⊢
          refine ⟨h.1, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr2
          · exact List.contains_iff_mem.mp hc1
          · exact h.2 r hr2
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte, subsumesPtrLocalState,
            Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h ⊢
          refine ⟨h.1, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr2
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem i (h.2 r hr2)

theorem ptrStmtStep_length (decls : List LocalDecl) (env : List PtrLocalState)
    (s : MirAst.Statement) :
    (ptrStmtStep decls env s).length = decls.length := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    obtain ⟨i, projs⟩ := dst
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      split
      · cases directBorrowOf rv with
        | some bp => simp [setPtrLocal]
        | none =>
          cases reborrowParentOf rv with
          | some p => simp [stepReborrow, setPtrLocal]
          | none =>
            cases ptrCopySrcOf decls rv with
            | some p =>
              simp only [stepPtrCopy]
              split <;> simp
            | none => simp [setPtrLocal]
      · cases ptrDerefReadSrc rv <;> simp [stepForeignRead]
    | cons hd tl =>
      cases hd with
      | deref =>
        cases tl with
        | nil =>
          simp only [ptrStmtStep]
          cases ptrDerefReadSrc rv <;> (simp only [stepDerefWrite]; split <;> simp)
        | cons _ _ => simp [ptrStmtStep]
      | _ => simp [ptrStmtStep]
  | retag _ p =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      split <;> simp [stepReborrow, setPtrLocal]
    | cons _ _ => simp [ptrStmtStep]
  | storageLive i | storageDead i =>
    simp only [ptrStmtStep]
    split <;> simp [setPtrLocal]
  | deinit p =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      split <;> simp [setPtrLocal]
    | cons _ _ => simp [ptrStmtStep]
  | _ => simp [ptrStmtStep]

private theorem stepDerefWrite_mono (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (w : Nat) :
    subsumesPtrEnv n (stepDerefWrite n e1 w) (stepDerefWrite n e2 w) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  unfold stepDerefWrite
  have hw := hall w
  cases hw1 : e1.getD w .disabled with
  | empty =>
    rw [getD_map_range _ _ _ hq]
    cases hw2 : e2.getD w .disabled with
    | empty =>
      rw [getD_map_range _ _ _ hq]
      exact hall q
    | disabled =>
      rw [getD_map_range _ _ _ hq]
      exact subsumesPtrLocalState_disabled_right _
    | live wT2 wP2 _ _ =>
      rw [getD_map_range _ _ _ hq]
      have hq_sub := hall q
      cases hq2 : e2.getD q .disabled with
      | empty => rw [hq2] at hq_sub; exact hq_sub
      | disabled => exact subsumesPtrLocalState_disabled_right _
      | live qT2 qP2 qH2 qW2 =>
        rw [hq2] at hq_sub
        by_cases hc : (wP2.contains q || targetsDefinitelyDisjoint qT2 wT2) = true
        · simp only [hc, ↓reduceIte]
          refine subsumesPtrLocalState_trans hq_sub ?_
          simp only [subsumesPtrLocalState, Bool.or_true, Bool.true_and, Bool.and_eq_true,
            List.all_eq_true, List.contains_iff_mem]
          exact ⟨⟨by cases qW2 <;> rfl, by cases qT2 <;> simp⟩, fun r hr => hr⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact subsumesPtrLocalState_disabled_right _
  | disabled =>
    rw [hw1] at hw
    cases hw2 : e2.getD w .disabled with
    | empty | live _ _ _ _ => rw [hw2] at hw; simp [subsumesPtrLocalState] at hw
    | disabled =>
      rw [getD_map_range _ _ _ hq]
      rfl
  | live wT1 wP1 _ _ =>
    rw [hw1] at hw
    cases hw2 : e2.getD w .disabled with
    | empty => rw [hw2] at hw; simp [subsumesPtrLocalState] at hw
    | disabled =>
      rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
      exact subsumesPtrLocalState_disabled_right _
    | live wT2 wP2 _ _ =>
      rw [hw2] at hw
      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hw
      rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
      have hq_sub := hall q
      cases hq1 : e1.getD q .disabled with
      | empty => rfl
      | disabled =>
        rw [hq1] at hq_sub
        cases hq2 : e2.getD q .disabled with
        | empty | live _ _ _ _ => rw [hq2] at hq_sub; simp [subsumesPtrLocalState] at hq_sub
        | disabled => rfl
      | live qT1 qP1 qH1 qW1 =>
        rw [hq1] at hq_sub
        cases hq2 : e2.getD q .disabled with
        | empty => rw [hq2] at hq_sub; simp [subsumesPtrLocalState] at hq_sub
        | disabled => exact subsumesPtrLocalState_disabled_right _
        | live qT2 qP2 qH2 qW2 =>
          rw [hq2] at hq_sub
          by_cases hkeep2 : (wP2.contains q || targetsDefinitelyDisjoint qT2 wT2) = true
          · have hkeep1 : (wP1.contains q || targetsDefinitelyDisjoint qT1 wT1) = true := by
              cases hpeer : wP2.contains q with
              | true =>
                have hp1 : wP1.contains q = true :=
                  List.contains_iff_mem.mpr (hw.2 q (List.contains_iff_mem.mp hpeer))
                simp only [hp1, Bool.true_or]
              | false =>
                rw [hpeer, Bool.false_or] at hkeep2
                cases qT2 with
                | none => simp [targetsDefinitelyDisjoint] at hkeep2
                | some qp2 =>
                  cases wT2 with
                  | none => simp [targetsDefinitelyDisjoint] at hkeep2
                  | some wp2 =>
                    have hq_sub' := hq_sub
                    simp only [subsumesPtrLocalState, Bool.and_eq_true,
                      decide_eq_true_eq] at hq_sub'
                    have hw1_eq : wT1 = some wp2 := by simpa using hw.1.2
                    rw [hq_sub'.1.2, hw1_eq, hkeep2]
                    simp only [Bool.or_true]
            simp only [hkeep2, hkeep1, ↓reduceIte]
            simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
              List.contains_iff_mem] at hq_sub ⊢
            exact ⟨⟨⟨rfl, hq_sub.1.1.2⟩, hq_sub.1.2⟩, hq_sub.2⟩
          · simp only [hkeep2, Bool.false_eq_true, ↓reduceIte]
            exact subsumesPtrLocalState_disabled_right _

theorem stepForeignRead_getD {decls : List LocalDecl} {n : Nat} {env : List PtrLocalState}
    {r q : Nat} (hq : q < n) :
    (stepForeignRead decls n env r).getD q .disabled =
      if isMutPtrLocal decls q && isHotPtrState (env.getD q .disabled) && !foreignReadKeeps env r q then
        freezePtrState (env.getD q .disabled)
      else env.getD q .disabled := by
  unfold stepForeignRead
  rw [getD_map_range _ _ _ hq]

theorem stepForeignRead_getD_of_le {decls : List LocalDecl} {n : Nat} {env : List PtrLocalState}
    {r q : Nat} (hq : n ≤ q) :
    (stepForeignRead decls n env r).getD q .disabled = .disabled := by
  unfold stepForeignRead
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hq)]
  rfl

theorem stepForeignRead_length (decls : List LocalDecl) (n : Nat) (env : List PtrLocalState)
    (r : Nat) : (stepForeignRead decls n env r).length = n := by
  simp [stepForeignRead]

private theorem subsumes_live_inv {t1 : Option (Nat × List BorrowProjStep)} {ps1 : List Nat}
    {h1 w1 : Bool} {s2 : PtrLocalState}
    (h : subsumesPtrLocalState (.live t1 ps1 h1 w1) s2 = true) :
    s2 = .disabled ∨ ∃ t2 ps2 h2 w2, s2 = .live t2 ps2 h2 w2 ∧ (!h1 || h2) = true ∧
      (!w2 || w1) = true ∧ (∀ q2, t2 = some q2 → t1 = some q2) ∧ (∀ r ∈ ps2, r ∈ ps1) := by
  cases s2 with
  | empty => simp [subsumesPtrLocalState] at h
  | disabled => exact .inl rfl
  | live t2 ps2 h2 w2 =>
    right
    refine ⟨t2, ps2, h2, w2, rfl, ?_, ?_, fun q2 hq2 => ?_, fun r hr => ?_⟩
    · simp only [subsumesPtrLocalState, Bool.and_eq_true] at h
      exact h.1.1.1
    · simp only [subsumesPtrLocalState, Bool.and_eq_true] at h
      exact h.1.1.2
    · subst hq2
      simp only [subsumesPtrLocalState, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    · simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at h
      exact h.2 r hr

private theorem foreignReadKeeps_mono {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (r q : Nat) (h2 : foreignReadKeeps e2 r q = true) (h1 : foreignReadKeeps e1 r q = false) :
    e2.getD q .disabled = .disabled := by
  have hr := hall r
  have hq := hall q
  unfold foreignReadKeeps at h1 h2
  by_cases hqr : (q == r) = true
  · simp [hqr] at h1
  · simp only [hqr, Bool.false_or] at h1 h2
    generalize e1.getD r .disabled = a1 at hr h1
    generalize e1.getD q .disabled = b1 at hq h1
    generalize e2.getD r .disabled = a2 at hr h2
    generalize e2.getD q .disabled = b2 at hq h2 ⊢
    rcases a1 with _ | ⟨rT1, rP1, rH1, rW1⟩ | _ <;> rcases b1 with _ | ⟨qT1, qP1, qH1, qW1⟩ | _ <;>
      simp only [Bool.true_eq_false] at h1
    · -- a1 = live, b1 = live
      rcases subsumes_live_inv hq with hb2 | ⟨qT2, qP2, qH2, qW2, rfl, _, _, hqT, _⟩
      · exact hb2
      · exfalso
        rcases subsumes_live_inv hr with rfl | ⟨rT2, rP2, rH2, rW2, rfl, _, _, hrT, hrP⟩
        · simp at h2
        · simp only [Bool.or_eq_false_iff] at h1
          simp only [Bool.or_eq_true] at h2
          rcases h2 with hc | hd
          · have := hrP q (List.contains_iff_mem.mp hc)
            rw [List.contains_iff_mem.mpr this] at h1
            exact absurd h1.1 (by simp)
          · cases qT2 with
            | none => simp [targetsDefinitelyDisjoint] at hd
            | some qp2 =>
              cases rT2 with
              | none => simp [targetsDefinitelyDisjoint] at hd
              | some rp2 =>
                rw [hqT qp2 rfl, hrT rp2 rfl] at h1
                rw [hd] at h1
                exact absurd h1.2 (by simp)
    · -- a1 = disabled, b1 = live
      cases a2 with
      | empty => simp [subsumesPtrLocalState] at hr
      | live _ _ _ _ => simp [subsumesPtrLocalState] at hr
      | disabled =>
        rcases subsumes_live_inv hq with hb2 | ⟨qT2, qP2, qH2, qW2, rfl, _, _, _, _⟩
        · exact hb2
        · simp at h2

theorem stepForeignRead_mono (decls : List LocalDecl) (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (r : Nat) :
    ∀ p, subsumesPtrLocalState ((stepForeignRead decls n e1 r).getD p .disabled)
      ((stepForeignRead decls n e2 r).getD p .disabled) = true := by
  intro p
  by_cases hp : p < n
  · rw [stepForeignRead_getD hp, stepForeignRead_getD hp]
    by_cases hm : isMutPtrLocal decls p = true
    · by_cases hh2 : isHotPtrState (e2.getD p .disabled) = true
      · cases hk2 : foreignReadKeeps e2 r p with
        | false =>
          simp only [hm, hh2, Bool.not_false, Bool.and_self, ↓reduceIte]
          split
          · exact freezePtrState_mono (hall p)
          · exact subsumesPtrLocalState_trans (hall p) (subsumesPtrLocalState_freeze_right _)
        | true =>
          simp only [hm, hh2, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hh1 : isHotPtrState (e1.getD p .disabled) = true
          · cases hk1 : foreignReadKeeps e1 r p with
            | false =>
              have hdis2 := foreignReadKeeps_mono hall r p hk2 hk1
              rw [hdis2] at hh2
              simp [isHotPtrState] at hh2
            | true =>
              simp only [hh1, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
              exact hall p
          · simp only [Bool.not_eq_true] at hh1
            simp only [hh1, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact hall p
      · simp only [Bool.not_eq_true] at hh2
        simp only [hm, hh2, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have hsub_p := hall p
        cases he2 : e2.getD p .disabled with
        | disabled =>
          split <;> exact subsumesPtrLocalState_disabled_right _
        | empty =>
          rw [he2] at hsub_p
          cases he1 : e1.getD p .disabled with
          | empty => simp [isHotPtrState]; rfl
          | live _ _ _ _ | disabled => rw [he1] at hsub_p; simp [subsumesPtrLocalState] at hsub_p
        | live t2 ps2 b2 w2 =>
          rw [he2] at hh2 hsub_p
          simp only [isHotPtrState] at hh2
          subst hh2
          cases he1 : e1.getD p .disabled with
          | empty => simp [isHotPtrState]; rfl
          | disabled => rw [he1] at hsub_p; simp [subsumesPtrLocalState] at hsub_p
          | live t1 ps1 b1 w1 =>
            rw [he1] at hsub_p
            have hb1 : b1 = false := by
              cases b1
              · rfl
              · simp [subsumesPtrLocalState] at hsub_p
            subst hb1
            simp only [isHotPtrState, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact hsub_p
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hall p
  · rw [stepForeignRead_getD_of_le (Nat.le_of_not_lt hp),
      stepForeignRead_getD_of_le (Nat.le_of_not_lt hp)]
    rfl

theorem stepReborrowRead_mono (decls : List LocalDecl) (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (rv : Rvalue) :
    ∀ p, subsumesPtrLocalState ((stepReborrowRead decls n e1 rv).getD p .disabled)
      ((stepReborrowRead decls n e2 rv).getD p .disabled) = true := by
  unfold stepReborrowRead
  cases refReborrowParentOf rv with
  | some r => exact stepForeignRead_mono decls n hall r
  | none => exact hall

/-- `ptrStmtStep` is monotone on width-`decls.length` abstract environments. -/
theorem ptrStmtStep_mono (decls : List LocalDecl) {e1 e2 : List PtrLocalState}
    (hlen1 : e1.length = decls.length) (hlen2 : e2.length = decls.length)
    (hsub : subsumesPtrEnv decls.length e1 e2 = true) (s : MirAst.Statement) :
    subsumesPtrEnv decls.length (ptrStmtStep decls e1 s) (ptrStmtStep decls e2 s) = true := by
  have hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true :=
    subsumesPtrLocalState_getD_of_length hlen1 hlen2 hsub
  have hsetG : ∀ (E1 E2 : List PtrLocalState),
      (∀ p, subsumesPtrLocalState (E1.getD p .disabled) (E2.getD p .disabled) = true) →
      ∀ i st1 st2, subsumesPtrLocalState st1 st2 = true →
      subsumesPtrEnv decls.length (setPtrLocal decls.length E1 i st1)
        (setPtrLocal decls.length E2 i st2) = true := by
    intro E1 E2 hallE i st1 st2 hst
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [setPtrLocal, setPtrLocal, getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
    by_cases hqi : (q == i) = true
    · simp only [hqi, ↓reduceIte]; exact hst
    · simp only [hqi, Bool.false_eq_true, ↓reduceIte]
      exact removePeerFromState_mono i (hallE q)
  have hset := hsetG e1 e2 hall
  have hfr : ∀ r, subsumesPtrEnv decls.length (stepForeignRead decls decls.length e1 r)
      (stepForeignRead decls decls.length e2 r) = true := by
    intro r
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q _
    exact stepForeignRead_mono decls decls.length hall r q
  have hid : subsumesPtrEnv decls.length
      ((List.range decls.length).map (fun q => e1.getD q .disabled))
      ((List.range decls.length).map (fun q => e2.getD q .disabled)) = true := by
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
    exact hall q
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    obtain ⟨i, projs⟩ := dst
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]
        cases directBorrowOf rv with
        | some bp =>
          exact hset i _ _ (subsumesPtrLocalState_refl _)
        | none =>
          cases reborrowParentOf rv with
          | some p =>
            simp only [stepReborrow]
            have hallR := stepReborrowRead_mono decls decls.length hall rv
            apply hsetG _ _ hallR i
            have hp := hallR p
            cases h1 : (stepReborrowRead decls decls.length e1 rv).getD p .disabled with
            | empty => rfl
            | disabled =>
              rw [h1] at hp
              cases h2 : (stepReborrowRead decls decls.length e2 rv).getD p .disabled with
              | empty | live _ _ _ _ => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
              | disabled => rfl
            | live t1 ps1 h1p w1p =>
              rw [h1] at hp
              cases h2 : (stepReborrowRead decls decls.length e2 rv).getD p .disabled with
              | empty => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
              | disabled => rfl
              | live t2 ps2 h2p w2p =>
                rw [h2] at hp
                simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                  List.contains_iff_mem] at hp ⊢
                refine ⟨⟨⟨by cases borrowStartsHot rv <;> cases h1p <;> cases h2p <;> simp_all,
                          hp.1.1.2⟩, hp.1.2⟩, fun r hr => ?_⟩
                rcases List.mem_cons.mp hr with rfl | hrf
                · exact .head _
                · obtain ⟨hr2, hne⟩ := List.mem_filter.mp hrf
                  exact .tail _ (List.mem_filter.mpr ⟨hp.2 r hr2, hne⟩)
          | none =>
            cases ptrCopySrcOf decls rv with
            | some p =>
              simp only [stepPtrCopy]
              by_cases hip : (i == p) = true
              · simp only [hip, ↓reduceIte]; exact hid
              · simp only [hip, Bool.false_eq_true, ↓reduceIte,
                  subsumesPtrEnv, List.all_eq_true, List.mem_range]
                intro q hq
                rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
                by_cases hqi : (q == i) = true
                · simp only [hqi, ↓reduceIte]
                  exact addPeerToState_mono i (hall p)
                · simp only [hqi, Bool.false_eq_true, ↓reduceIte]
                  have hr := removePeerFromState_mono i (hall q)
                  cases h1 : removePeerFromState i (e1.getD q .disabled) with
                  | empty => rfl
                  | disabled =>
                    rw [h1] at hr
                    cases h2 : removePeerFromState i (e2.getD q .disabled) with
                    | empty | live _ _ _ _ => rw [h2] at hr; simp [subsumesPtrLocalState] at hr
                    | disabled => rfl
                  | live t1 ps1 qH1 qW1 =>
                    rw [h1] at hr
                    cases h2 : removePeerFromState i (e2.getD q .disabled) with
                    | empty => rw [h2] at hr; simp [subsumesPtrLocalState] at hr
                    | disabled => exact subsumesPtrLocalState_disabled_right _
                    | live t2 ps2 qH2 qW2 =>
                      rw [h2] at hr
                      have hr0 := hr
                      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                        List.contains_iff_mem] at hr
                      by_cases hc2 : ps2.contains p = true
                      · have hc1 : ps1.contains p = true :=
                          List.contains_iff_mem.mpr (hr.2 p (List.contains_iff_mem.mp hc2))
                        simp only [hc1, hc2, ↓reduceIte]
                        simpa [addPeerToState] using addPeerToState_mono i hr0
                      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
                        by_cases hc1 : ps1.contains p = true
                        · by_cases hci : ps1.contains i = true
                          · simp only [hc1, hci, ↓reduceIte]; exact hr0
                          · simp only [hc1, hci, Bool.false_eq_true, ↓reduceIte,
                              subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                              List.contains_iff_mem]
                            exact ⟨hr.1, fun r hr2 => List.mem_cons_of_mem i (hr.2 r hr2)⟩
                        · simp only [hc1, Bool.false_eq_true, ↓reduceIte]; exact hr0
            | none => exact hset i _ _ (subsumesPtrLocalState_refl _)
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]
        cases ptrDerefReadSrc rv with
        | some r => exact hfr r
        | none => exact hid
    | cons hd tl =>
      cases hd with
      | deref =>
        cases tl with
        | nil =>
          simp only [ptrStmtStep]
          cases ptrDerefReadSrc rv with
          | some r => exact stepDerefWrite_mono decls.length (stepForeignRead_mono decls decls.length hall r) i
          | none => exact stepDerefWrite_mono decls.length hall i
        | cons _ _ => exact hid
      | _ => exact hid
  | retag _ pl =>
    obtain ⟨i, projs⟩ := pl
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      by_cases hi_ref : (isDeclPtrLocal decls i && isDeclRefLocal decls i) = true
      · simp only [hi_ref, ↓reduceIte, stepReborrow]
        have hallR := stepForeignRead_mono decls decls.length hall i
        apply hsetG _ _ hallR i
        have hp := hallR i
        cases h1 : (stepForeignRead decls decls.length e1 i).getD i .disabled with
        | empty => rfl
        | disabled =>
          rw [h1] at hp
          cases h2 : (stepForeignRead decls decls.length e2 i).getD i .disabled with
          | empty | live _ _ _ _ => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
          | disabled => rfl
        | live t1 ps1 h1p w1p =>
          rw [h1] at hp
          cases h2 : (stepForeignRead decls decls.length e2 i).getD i .disabled with
          | empty => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
          | disabled => rfl
          | live t2 ps2 h2p w2p =>
            rw [h2] at hp
            simp only [subsumesPtrLocalState, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
              List.contains_iff_mem] at hp ⊢
            refine ⟨hp.1, fun r hr => ?_⟩
            rcases List.mem_cons.mp hr with rfl | hrf
            · exact .head _
            · obtain ⟨hr2, hne⟩ := List.mem_filter.mp hrf
              exact .tail _ (List.mem_filter.mpr ⟨hp.2 r hr2, hne⟩)
      · simp only [hi_ref, Bool.false_eq_true, ↓reduceIte]; exact hid
    | cons _ _ => exact hid
  | storageLive i | storageDead i =>
    simp only [ptrStmtStep]
    by_cases hi_ptr : isDeclPtrLocal decls i = true
    · simp only [hi_ptr, ↓reduceIte]; exact hset i _ _ (subsumesPtrLocalState_refl _)
    · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]; exact hid
  | deinit p =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]; exact hset i _ _ (subsumesPtrLocalState_refl _)
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]; exact hid
    | cons _ _ => exact hid
  | _ => exact hid

/-- A Tree Borrows read whose read projection cannot overlap the unranged entry
`e`'s target leaves `e` unchanged. -/
theorem updateBorrowPermOnReadAtProj_of_not_overlap {all : List BorrowEntry} {e : BorrowEntry}
    (t : Nat) (r : Option Nat) {proj : List ProjectionElem} (off len : Nat)
    (prot : List Nat := .nil) (d : Nat := 0)
    (hrl : e.rangeLen = 0)
    (hov : MirSemantics.projectionsOverlap e.targetProjection proj = false) :
    MirSemantics.updateBorrowPermOnReadAtProj all e t r proj off len prot d = e := by
  have hb : MirSemantics.borrowEntryOverlapsWrite e proj off len = false := by
    simp [MirSemantics.borrowEntryOverlapsWrite, hrl, hov]
  unfold MirSemantics.updateBorrowPermOnReadAtProj
  rw [hb]
  cases Bool.and (Nat.beq e.targetFrameDepth d) (Nat.beq e.targetLocal t) <;> rfl

/-- Soundness of the abstract transfer `stepForeignRead`: after a Tree Borrows
read through the pointer that `r` holds (tag `rv.tag`, entry `rEntry`), which
updates the borrow table by `freezeTreeBorrowsOnReadAtProj` on `rEntry`'s target
(a dereference read `freezeDerefReadBorrowsAt`, or a reference reborrow's
initial read), `PtrEnvOk` holds for `stepForeignRead … r`: every mutable
pointer/reference local that the read may freeze is `.disabled` when hot
(`isHotPtrState`; cold `.reserved`/`.frozen` entries are left unfrozen), and every
other local keeps its entry (the reader and its ancestor-or-self peers are local
to the read, disjoint targets do not overlap it, and a freeze never disables). -/
theorem PtrEnvOk.foreignRead {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hdag : BorrowDagOrdered borrows)
    (hranges : ∀ e ∈ borrows, e.rangeLen = 0)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hr_ptr : isPtrTy dr.ty = true)
    {rv : ProvenancePtr} (hvr : view[r]? = some (.init (.ptr rv 8)))
    {rEntry : BorrowEntry} (hrlk : lookupBorrow borrows rv.tag = some rEntry)
    {d : Nat} :
    PtrEnvOk body view
      (MirSemantics.freezeTreeBorrowsOnReadAtProj borrows borrows rEntry.targetLocal (some rv.tag)
        rEntry.targetProjection rEntry.rangeOffset rEntry.rangeLen [] d)
      (stepForeignRead body.localDecls body.localDecls.length env r) := by
  rw [freezeTreeBorrowsOnReadAtProj_eq_map borrows borrows rEntry.targetLocal (some rv.tag)
    rEntry.targetProjection rEntry.rangeOffset rEntry.rangeLen [] d]
  have hf := updateBorrowPermOnReadAtProj_freezeOrSelf borrows rEntry.targetLocal (some rv.tag)
    rEntry.targetProjection rEntry.rangeOffset rEntry.rangeLen d
  generalize hfdef : (fun e => MirSemantics.updateBorrowPermOnReadAtProj borrows e
    rEntry.targetLocal (some rv.tag) rEntry.targetProjection rEntry.rangeOffset
    rEntry.rangeLen [] d) = f at hf ⊢
  have hfapp : ∀ e, f e = MirSemantics.updateBorrowPermOnReadAtProj borrows e
      rEntry.targetLocal (some rv.tag) rEntry.targetProjection rEntry.rangeOffset
      rEntry.rangeLen [] d := fun e => by rw [← hfdef]
  have hr_tag : rEntry.tag = rv.tag := (lookupBorrow_mem_and_tag hrlk).2
  have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
  have hr_ok := hok r hr_lt
  intro q hq
  have hq_ok := hok q hq
  rw [stepForeignRead_getD hq]
  have hbase : ∀ qT qP qHot qWritable,
      env.getD q .disabled = .live qT qP qHot qWritable →
      PtrLocalOk body view (borrows.map f) q (.live qT qP qHot false) := by
    intro qT qP qHot qWritable hst dq pvq hdq hqptr hvq
    rw [hst] at hq_ok
    obtain ⟨⟨eq, hlkq, hndisq, _, hnactq, htgtq, hancq⟩, hpeersq⟩ := hq_ok dq pvq hdq hqptr hvq
    refine ⟨⟨f eq, by rw [hf.lookupBorrow_map, hlkq]; rfl,
      fun hdis => hndisq ((hf.perm_eq_disabled_iff eq).mp hdis),
      fun hw => Bool.noConfusion hw,
      fun hmut hqHot => by
        rw [hf.eq_of_perm_ne_active (hnactq hmut hqHot)]
        exact hnactq hmut hqHot,
      fun qq hqq => by
        rw [hf.targetLocal, hf.targetProjection]
        exact htgtq qq hqq,
      fun anc' hmem' hanc' => ?_⟩,
      fun r' hr' dr' pv_r' hdr' hptr' hvr' => by
        rw [isBorrowDescendantOrSelf_map_eq hf.tag hf.parentTag]
        exact hpeersq r' hr' dr' pv_r' hdr' hptr' hvr'⟩
    obtain ⟨anc, hanc_mem, rfl⟩ := List.mem_map.mp hmem'
    rw [hf.tag] at hanc'
    have hanc0 := (IsBorrowAncestorOrSelf.map_iff hf.tag hf.parentTag).mp hanc'
    obtain ⟨ha_ndis, _, ha_nact, ha_tgt⟩ := hancq anc hanc_mem hanc0
    refine ⟨fun hdis => ha_ndis ((hf.perm_eq_disabled_iff anc).mp hdis),
      fun hw => Bool.noConfusion hw,
      fun hmut hqHot => by
        rw [hf.eq_of_perm_ne_active (ha_nact hmut hqHot)]
        exact ha_nact hmut hqHot,
      by rw [hf.targetLocal, hf.targetProjection, hf.targetLocal, hf.targetProjection]; exact ha_tgt⟩
  split
  · cases hst : env.getD q .disabled with
    | empty => rw [hst] at hq_ok; exact hq_ok
    | disabled => trivial
    | live qT qP qHot qWritable => exact hbase qT qP qHot qWritable hst
  · rename_i hkeep
    cases hst : env.getD q .disabled with
    | empty => rw [hst] at hq_ok; exact hq_ok
    | disabled => trivial
    | live qT qP qHot qWritable =>
      cases qWritable with
      | false => exact hbase qT qP qHot false hst
      | true =>
        have hst_ok := hq_ok
        rw [hst] at hst_ok
        intro dq pvq hdq hqptr hvq
        obtain ⟨⟨eq, hlkq, hndisq, hnfq, hnactq, htgtq, hancq⟩, hpeersq⟩ := hst_ok dq pvq hdq hqptr hvq
        obtain ⟨hb0, hpeers'⟩ := hbase qT qP qHot true hst dq pvq hdq hqptr hvq
        obtain ⟨_, hlkq', hndisq', _, hnactq', htgtq', hancq'⟩ := hb0
        have hfe_anc : isMutPtrLocal body.localDecls q = true →
            ∀ anc ∈ borrows, IsBorrowAncestorOrSelf borrows pvq.tag anc.tag →
              (f anc).perm ≠ .frozen := by
          intro hmut anc hanc_mem hanc0
          obtain ⟨_, ha_nf, ha_nact, ha_tgt⟩ := hancq anc hanc_mem hanc0
          cases qHot with
          | false =>
            rw [hf.eq_of_perm_ne_active (ha_nact hmut rfl)]
            exact ha_nf rfl hmut
          | true =>
            have hk : foreignReadKeeps env r q = true := by
              revert hkeep
              rw [hst]
              cases foreignReadKeeps env r q <;> simp [hmut, isHotPtrState]
            suffices hfe : f anc = anc by rw [hfe]; exact ha_nf rfl hmut
            unfold foreignReadKeeps at hk
            rw [hst] at hk
            by_cases hqr : q = r
            · subst hqr
              rw [hvr] at hvq
              simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvq
              obtain ⟨rfl, _⟩ := hvq
              rw [hfapp]
              exact updateBorrowPermOnReadAtProj_of_descendant _ _ _ _ [] d
                (hdag.descendant_of_ancestor hrlk hanc0)
            · have hqr' : (q == r) = false := beq_false_of_ne hqr
              simp only [hqr', Bool.false_or] at hk
              cases hrst : env.getD r .disabled with
              | empty =>
                rw [hrst] at hr_ok
                exact absurd hvr (hr_ok dr rv hdr hr_ptr)
              | disabled =>
                rw [hrst] at hk
                simp at hk
              | live rT rP rHot rWritable =>
                rw [hrst] at hk hr_ok
                obtain ⟨⟨eR, hlkR, _, _, _, htgtR, _⟩, hpeersR⟩ := hr_ok dr rv hdr hr_ptr hvr
                rw [hrlk] at hlkR
                injection hlkR with h
                subst h
                simp only [Bool.or_eq_true] at hk
                rcases hk with hpeer | hdisj
                · have hdesc := hpeersR q (List.contains_iff_mem.mp hpeer) dq pvq hdq hqptr hvq
                  have hanc_r := (IsBorrowAncestorOrSelf.of_descendant hdesc).trans hanc0
                  rw [hfapp]
                  exact updateBorrowPermOnReadAtProj_of_descendant _ _ _ _ [] d
                    (hdag.descendant_of_ancestor hrlk hanc_r)
                · cases qT with
                  | none => simp [targetsDefinitelyDisjoint] at hdisj
                  | some qp =>
                    cases rT with
                    | none => simp [targetsDefinitelyDisjoint] at hdisj
                    | some rp =>
                      have h1 : (anc.targetLocal, borrowProjSteps anc.targetProjection) = qp :=
                        ha_tgt.trans (htgtq qp rfl)
                      have h2 := htgtR rp rfl
                      obtain ⟨k1, p1⟩ := qp
                      obtain ⟨k2, p2⟩ := rp
                      simp only [Prod.mk.injEq] at h1 h2
                      obtain ⟨hk1, hp1⟩ := h1
                      obtain ⟨hk2, hp2⟩ := h2
                      rw [hfapp]
                      by_cases hloc : anc.targetLocal = rEntry.targetLocal
                      · have hov : borrowProjOverlap p1 p2 = false := by
                          have hk12 : k1 = k2 := by rw [← hk1, ← hk2, hloc]
                          simpa [targetsDefinitelyDisjoint, hk12] using hdisj
                        rw [← hp1, ← hp2] at hov
                        exact updateBorrowPermOnReadAtProj_of_not_overlap _ _ _ _ [] d
                          (hranges anc hanc_mem)
                          (borrowProjOverlap_borrowProjSteps hov)
                      · exact updateBorrowPermOnReadAtProj_of_targetLocal_ne _ _ _ _ [] d hloc
        obtain ⟨heq_mem, heq_tag⟩ := lookupBorrow_mem_and_tag hlkq
        refine ⟨⟨f eq, by rw [hf.lookupBorrow_map, hlkq]; rfl,
          fun hdis => hndisq ((hf.perm_eq_disabled_iff eq).mp hdis),
          fun _ hmut => hfe_anc hmut eq heq_mem (IsBorrowAncestorOrSelf.of_eq heq_tag.symm),
          fun hmut hqHot => by
            rw [hf.eq_of_perm_ne_active (hnactq hmut hqHot)]
            exact hnactq hmut hqHot,
          fun qq hqq => by
            rw [hf.targetLocal, hf.targetProjection]
            exact htgtq qq hqq,
          fun anc' hmem' hanc' => ?_⟩, hpeers'⟩
        obtain ⟨ha_ndis, _, ha_nact, _⟩ := hancq' anc' hmem' hanc'
        obtain ⟨anc, hanc_mem, rfl⟩ := List.mem_map.mp hmem'
        rw [hf.tag] at hanc'
        have hanc0 := (IsBorrowAncestorOrSelf.map_iff hf.tag hf.parentTag).mp hanc'
        obtain ⟨_, _, _, ha_tgt0⟩ := hancq anc hanc_mem hanc0
        exact ⟨ha_ndis, fun _ hmut => hfe_anc hmut anc hanc_mem hanc0, ha_nact,
          by rw [hf.targetLocal, hf.targetProjection, hf.targetLocal, hf.targetProjection]; exact ha_tgt0⟩

/-- `PtrEnvOk.foreignRead` for a dereference read `*_r` (`freezeDerefReadBorrowsAt`,
`evalRvalue_derefRead_freeze` with an empty post-dereference projection). -/
theorem PtrEnvOk.derefRead {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hdag : BorrowDagOrdered borrows)
    (hranges : ∀ e ∈ borrows, e.rangeLen = 0)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hr_ptr : isPtrTy dr.ty = true)
    {rv : ProvenancePtr} (hvr : view[r]? = some (.init (.ptr rv 8))) :
    PtrEnvOk body view (MirSemantics.freezeDerefReadBorrowsAt view r [] borrows)
      (stepForeignRead body.localDecls body.localDecls.length env r) := by
  unfold MirSemantics.freezeDerefReadBorrowsAt
  simp only [get?, hvr]
  cases hlk : lookupBorrow borrows rv.tag with
  | none =>
    refine PtrEnvOk.of_subsumes ?_ hok
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [stepForeignRead_getD hq]
    split
    · exact subsumesPtrLocalState_freeze_right _
    · exact subsumesPtrLocalState_refl _
  | some rEntry =>
    simp only [appendProjections_nil_right]
    exact hok.foreignRead hdag hranges hdr hr_ptr hvr hlk

/-- Well-formedness of a `PtrLocalState` at width `n`: peer lists have no
duplicates and contain only local indices `< n`. -/
def PtrStateWf (n : Nat) : PtrLocalState → Prop
  | .empty => True
  | .live _ ps _ _ => ps.Nodup ∧ ∀ r ∈ ps, r < n
  | .disabled => True

/-- Strictly decreasing height rank on `PtrLocalState` at width `n`, bounded by
`n + 5` (`Translate.lean`: `ptrEnvAtEntry`). -/
def ptrStateRank (n : Nat) : PtrLocalState → Nat
  | .empty => n + 5
  | .live (some _) ps hot writable =>
    ps.length + 2 + (if hot then 0 else 1) + (if writable then 1 else 0)
  | .live none ps hot writable =>
    ps.length + 1 + (if hot then 0 else 1) + (if writable then 1 else 0)
  | .disabled => 0

def ptrEnvRank (n : Nat) (env : List PtrLocalState) : Nat :=
  ((List.range n).map (fun q => ptrStateRank n (env.getD q .disabled))).sum

def ptrEntriesRank (b n : Nat) (entries : List (List PtrLocalState)) : Nat :=
  ((List.range b).map (fun dst => ptrEnvRank n (entries.getD dst (initPtrEnv n)))).sum

private theorem nodup_length_le_of_subset {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨hx_not, hrest_nd⟩ := List.nodup_cons.mp hnd
    have hx_in : x ∈ ys := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
      intro y hy
      have hy_ne : y ≠ x := fun h => hx_not (h ▸ hy)
      exact (List.mem_erase_of_ne hy_ne).mpr (hsub y (List.mem_cons_of_mem x hy))
    have hlen := ih hrest_nd hsub'
    have herase := List.length_erase_of_mem hx_in
    have hpos : 0 < ys.length := List.length_pos_of_mem hx_in
    simp only [List.length_cons]
    omega

private theorem ptrStateWf_peers_length_le {n : Nat} {t : Option (Nat × List BorrowProjStep)}
    {ps : List Nat} {hot writable : Bool} (hwf : PtrStateWf n (.live t ps hot writable)) :
    ps.length ≤ n := by
  simpa using nodup_length_le_of_subset hwf.1 (fun r hr => List.mem_range.mpr (hwf.2 r hr))

private theorem filter_eq_or_length_lt {α : Type} (p : α → Bool) (xs : List α) :
    xs.filter p = xs ∨ (xs.filter p).length < xs.length := by
  induction xs with
  | nil => exact .inl rfl
  | cons x rest ih =>
    cases hp : p x with
    | false =>
      right
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le p rest)
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.cons.injEq, true_and, List.length_cons]
      rcases ih with heq | hlt
      · exact .inl heq
      · exact .inr (Nat.succ_lt_succ hlt)

theorem joinPtrLocalState_wf {n : Nat} {s1 s2 : PtrLocalState}
    (h1 : PtrStateWf n s1) (h2 : PtrStateWf n s2) :
    PtrStateWf n (joinPtrLocalState s1 s2) := by
  cases s1 with
  | empty => exact h2
  | disabled => cases s2 <;> trivial
  | live t1 ps1 _ _ =>
    cases s2 with
    | empty => exact h1
    | disabled => trivial
    | live t2 ps2 _ _ =>
      exact ⟨h1.1.sublist List.filter_sublist,
        fun r hr => h1.2 r (List.mem_filter.mp hr).1⟩

theorem joinPtrLocalState_eq_or_rank_lt {n : Nat} {s1 s2 : PtrLocalState}
    (h2 : PtrStateWf n s2) :
    joinPtrLocalState s1 s2 = s1 ∨
      ptrStateRank n (joinPtrLocalState s1 s2) < ptrStateRank n s1 := by
  cases s1 with
  | empty =>
    cases s2 with
    | empty => exact .inl rfl
    | disabled => right; simp [joinPtrLocalState, ptrStateRank]
    | live t2 ps2 h2b w2b =>
      right
      have hlen := ptrStateWf_peers_length_le h2
      cases t2 <;> cases h2b <;> cases w2b <;>
        simp only [joinPtrLocalState, ptrStateRank, Bool.false_eq_true, ↓reduceIte] <;> omega
  | disabled =>
    left
    cases s2 <;> rfl
  | live t1 ps1 h1b w1b =>
    cases s2 with
    | empty => exact .inl rfl
    | disabled =>
      right
      cases t1 <;> cases h1b <;> cases w1b <;>
        simp only [joinPtrLocalState, ptrStateRank, Bool.false_eq_true, ↓reduceIte] <;> omega
    | live t2 ps2 h2b w2b =>
      simp only [joinPtrLocalState]
      have hflt := filter_eq_or_length_lt (fun r => ps2.contains r) ps1
      have hle : (ps1.filter (fun r => ps2.contains r)).length ≤ ps1.length :=
        List.length_filter_le _ ps1
      cases t1 with
      | none =>
        have hif : (if (none == t2) then none else none) =
            (none : Option (Nat × List BorrowProjStep)) := by
          by_cases hb : (none == t2) = true <;> simp [hb]
        rw [hif]
        rcases hflt with heq | hlt
        · rw [heq]
          cases h1b <;> cases h2b <;> cases w1b <;> cases w2b <;>
            first
            | exact .inl rfl
            | (right; simp only [ptrStateRank, Bool.or, Bool.and, Bool.false_eq_true, ↓reduceIte]; omega)
        · right
          cases h1b <;> cases h2b <;> cases w1b <;> cases w2b <;>
            simp only [ptrStateRank, Bool.or, Bool.and, Bool.false_eq_true, ↓reduceIte] <;> omega
      | some x =>
        by_cases hbeq : (some x == t2) = true
        · simp only [hbeq, ↓reduceIte]
          rcases hflt with heq | hlt
          · rw [heq]
            cases h1b <;> cases h2b <;> cases w1b <;> cases w2b <;>
              first
              | exact .inl rfl
              | (right; simp only [ptrStateRank, Bool.or, Bool.and, Bool.false_eq_true, ↓reduceIte]; omega)
          · right
            cases h1b <;> cases h2b <;> cases w1b <;> cases w2b <;>
              simp only [ptrStateRank, Bool.or, Bool.and, Bool.false_eq_true, ↓reduceIte] <;> omega
        · right
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          cases h1b <;> cases h2b <;> cases w1b <;> cases w2b <;>
            simp only [ptrStateRank, Bool.or, Bool.and, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem ptrStateWf_removePeer {n : Nat} (i : Nat) {s : PtrLocalState}
    (h : PtrStateWf n s) : PtrStateWf n (removePeerFromState i s) := by
  cases s with
  | empty | disabled => trivial
  | live t ps _ _ =>
    exact ⟨h.1.sublist List.filter_sublist, fun r hr => h.2 r (List.mem_filter.mp hr).1⟩

private theorem ptrStateWf_addPeer {n i : Nat} (hi : i < n) {s : PtrLocalState}
    (h : PtrStateWf n s) : PtrStateWf n (addPeerToState i s) := by
  cases s with
  | empty | disabled => trivial
  | live t ps _ _ =>
    simp only [addPeerToState]
    by_cases hc : ps.contains i = true
    · simp only [hc, ↓reduceIte]; exact h
    · have hni : i ∉ ps := by simpa [List.contains_iff_mem] using hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨List.nodup_cons.mpr ⟨hni, h.1⟩, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hrm
      · exact hi
      · exact h.2 r hrm

private theorem ptrStateWf_singleton {n i : Nat} (hi : i < n)
    (t : Option (Nat × List BorrowProjStep)) (hot writable : Bool) :
    PtrStateWf n (.live t [i] hot writable) :=
  ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩,
    fun r hr => by rcases List.mem_cons.mp hr with rfl | hnil; exact hi; cases hnil⟩

private theorem stepDerefWrite_wf {n : Nat} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (w p : Nat) (hp : p < n) :
    PtrStateWf n ((stepDerefWrite n env w).getD p .disabled) := by
  unfold stepDerefWrite
  cases hw : env.getD w .disabled with
  | empty => rw [getD_map_range _ _ _ hp]; exact hwf p
  | disabled => rw [getD_map_range _ _ _ hp]; trivial
  | live wT wP _ _ =>
    rw [getD_map_range _ _ _ hp]
    have hp_wf := hwf p
    cases hp_eq : env.getD p .disabled with
    | empty => trivial
    | disabled => trivial
    | live qT qP _ _ =>
      rw [hp_eq] at hp_wf
      by_cases hc : (wP.contains p || targetsDefinitelyDisjoint qT wT) = true
      · simp only [hc, ↓reduceIte]; exact ⟨hp_wf.1, hp_wf.2⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]; trivial

theorem stepForeignRead_wf {n : Nat} {decls : List LocalDecl} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (r : Nat) :
    ∀ p, PtrStateWf n ((stepForeignRead decls n env r).getD p .disabled) := by
  intro p
  by_cases hp : p < n
  · rw [stepForeignRead_getD hp]
    split
    · have hp_wf := hwf p
      cases h : env.getD p .disabled <;> rw [h] at hp_wf <;> exact hp_wf
    · exact hwf p
  · rw [stepForeignRead_getD_of_le (Nat.le_of_not_lt hp)]
    simp [PtrStateWf]

theorem stepReborrowRead_wf {n : Nat} {decls : List LocalDecl} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (rv : Rvalue) :
    ∀ p, PtrStateWf n ((stepReborrowRead decls n env rv).getD p .disabled) := by
  unfold stepReborrowRead
  cases refReborrowParentOf rv with
  | some r => exact stepForeignRead_wf hwf r
  | none => exact hwf

theorem ptrStmtStep_wf (decls : List LocalDecl) (env : List PtrLocalState)
    (hwf : ∀ p, PtrStateWf decls.length (env.getD p .disabled))
    (s : MirAst.Statement) (p : Nat) :
    PtrStateWf decls.length ((ptrStmtStep decls env s).getD p .disabled) := by
  by_cases hp : p < decls.length
  · have hset : ∀ i st, PtrStateWf decls.length st →
        PtrStateWf decls.length ((setPtrLocal decls.length env i st).getD p .disabled) := by
      intro i st hst
      rw [setPtrLocal, getD_map_range _ _ _ hp]
      by_cases hpi : (p == i) = true
      · simp only [hpi, ↓reduceIte]; exact hst
      · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
        exact ptrStateWf_removePeer i (hwf p)
    obtain ⟨kind, span⟩ := s
    cases kind with
    | assign dst rv =>
      obtain ⟨i, projs⟩ := dst
      cases projs with
      | nil =>
        simp only [ptrStmtStep]
        by_cases hi_ptr : isDeclPtrLocal decls i = true
        · simp only [hi_ptr, ↓reduceIte]
          have hi_lt : i < decls.length := by
            unfold isDeclPtrLocal at hi_ptr
            cases hd : decls[i]? with
            | none => simp [hd] at hi_ptr
            | some _ => exact (List.getElem?_eq_some_iff.mp hd).1
          cases directBorrowOf rv with
          | some bp =>
            exact hset i _ (ptrStateWf_singleton hi_lt _ _ _)
          | none =>
            cases reborrowParentOf rv with
            | some par =>
              simp only [stepReborrow]
              rw [setPtrLocal, getD_map_range _ _ _ hp]
              by_cases hpi : (p == i) = true
              · simp only [hpi, ↓reduceIte]
                cases hpar : (stepReborrowRead decls decls.length env rv).getD par .disabled with
                | empty => trivial
                | disabled => trivial
                | live t pPs _ _ =>
                  have hp_wf : PtrStateWf decls.length
                      (removePeerFromState i
                        ((stepReborrowRead decls decls.length env rv).getD par .disabled)) :=
                    ptrStateWf_removePeer i (stepReborrowRead_wf hwf rv par)
                  rw [hpar] at hp_wf
                  dsimp only [removePeerFromState] at hp_wf
                  have hni : i ∉ pPs.filter (· != i) := by
                    simp [List.mem_filter]
                  refine ⟨List.nodup_cons.mpr ⟨hni, hp_wf.1⟩, fun r hr => ?_⟩
                  rcases List.mem_cons.mp hr with rfl | hrm
                  · exact hi_lt
                  · exact hp_wf.2 r hrm
              · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
                exact ptrStateWf_removePeer i (stepReborrowRead_wf hwf rv p)
            | none =>
              cases ptrCopySrcOf decls rv with
              | some src =>
                simp only [stepPtrCopy]
                by_cases his : (i == src) = true
                · simp only [his, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
                · simp only [his, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]
                  by_cases hpi : (p == i) = true
                  · simp only [hpi, ↓reduceIte]
                    exact ptrStateWf_addPeer hi_lt (hwf src)
                  · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
                    have hr_wf := ptrStateWf_removePeer i (hwf p)
                    cases hr_eq : removePeerFromState i (env.getD p .disabled) with
                    | empty => trivial
                    | disabled => trivial
                    | live t ps qHot qWritable =>
                      rw [hr_eq] at hr_wf
                      by_cases hcs : ps.contains src = true
                      · simp only [hcs, ↓reduceIte]
                        change PtrStateWf decls.length (addPeerToState i (.live t ps qHot qWritable))
                        exact ptrStateWf_addPeer hi_lt hr_wf
                      · simp only [hcs, Bool.false_eq_true, ↓reduceIte]
                        exact hr_wf
              | none => exact hset i _ trivial
        · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]
          cases ptrDerefReadSrc rv with
          | some r => exact stepForeignRead_wf hwf r p
          | none => rw [getD_map_range _ _ _ hp]; exact hwf p
      | cons hd tl =>
        cases hd with
        | deref =>
          cases tl with
          | nil =>
            simp only [ptrStmtStep]
            cases ptrDerefReadSrc rv with
            | some r => exact stepDerefWrite_wf (stepForeignRead_wf hwf r) i p hp
            | none => exact stepDerefWrite_wf hwf i p hp
          | cons _ _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
        | _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
    | retag _ pl =>
      obtain ⟨i, projs⟩ := pl
      cases projs with
      | nil =>
        simp only [ptrStmtStep]
        by_cases hi_ref : (isDeclPtrLocal decls i && isDeclRefLocal decls i) = true
        · simp only [hi_ref, ↓reduceIte, stepReborrow]
          have hi_lt : i < decls.length := by
            simp only [Bool.and_eq_true, isDeclPtrLocal] at hi_ref
            cases hd : decls[i]? with
            | none => simp [hd] at hi_ref
            | some _ => exact (List.getElem?_eq_some_iff.mp hd).1
          rw [setPtrLocal, getD_map_range _ _ _ hp]
          by_cases hpi : (p == i) = true
          · simp only [hpi, ↓reduceIte]
            cases hpar : (stepForeignRead decls decls.length env i).getD i .disabled with
            | empty => trivial
            | disabled => trivial
            | live t pPs _ _ =>
              have hp_wf : PtrStateWf decls.length
                  (removePeerFromState i
                    ((stepForeignRead decls decls.length env i).getD i .disabled)) :=
                ptrStateWf_removePeer i (stepForeignRead_wf hwf i i)
              rw [hpar] at hp_wf
              dsimp only [removePeerFromState] at hp_wf
              have hni : i ∉ pPs.filter (· != i) := by
                simp [List.mem_filter]
              refine ⟨List.nodup_cons.mpr ⟨hni, hp_wf.1⟩, fun r hr => ?_⟩
              rcases List.mem_cons.mp hr with rfl | hrm
              · exact hi_lt
              · exact hp_wf.2 r hrm
          · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
            exact ptrStateWf_removePeer i (stepForeignRead_wf hwf i p)
        · simp only [hi_ref, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
      | cons _ _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
    | storageLive i | storageDead i =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]; exact hset i _ trivial
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
    | deinit pl =>
      obtain ⟨i, projs⟩ := pl
      cases projs with
      | nil =>
        simp only [ptrStmtStep]
        by_cases hi_ptr : isDeclPtrLocal decls i = true
        · simp only [hi_ptr, ↓reduceIte]; exact hset i _ trivial
        · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
      | cons _ _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
    | _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
  · have hlen := ptrStmtStep_length decls env s
    have hnone : (ptrStmtStep decls env s)[p]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD, hnone, Option.getD_none]
    trivial

private def PtrEntriesShape (b n : Nat) (entries : List (List PtrLocalState)) : Prop :=
  entries.length = b ∧
  ∀ dst < b, (entries.getD dst (initPtrEnv n)).length = n ∧
    ∀ p, PtrStateWf n ((entries.getD dst (initPtrEnv n)).getD p .disabled)

private theorem initPtrEntries_shape (b n : Nat) :
    PtrEntriesShape b n (initPtrEntries b n) := by
  refine ⟨by simp [initPtrEntries], fun dst hdst => ?_⟩
  rw [initPtrEntries, getD_map_range _ _ _ hdst]
  refine ⟨by simp [initPtrEnv], fun p => ?_⟩
  by_cases hp : p < n
  · rw [initPtrEnv, getD_map_range _ _ _ hp]; trivial
  · have hnone : (initPtrEnv n)[p]? = none := List.getElem?_eq_none (by simp [initPtrEnv]; omega)
    simp only [List.getD, hnone, Option.getD_none]; trivial

private theorem sum_map_le {α : Type} {xs : List α} {f g : α → Nat}
    (hle : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := hle x (List.mem_cons_self ..)
    have hr := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

private theorem sum_map_le_and_lt_of_ne {α : Type} {xs : List α} {f g : α → Nat}
    (hle : ∀ x ∈ xs, f x ≤ g x)
    {x0 : α} (hx0 : x0 ∈ xs) (hlt : f x0 < g x0) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at hx0
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest_le : (rest.map f).sum ≤ (rest.map g).sum :=
      sum_map_le (fun z hz => hle z (List.mem_cons_of_mem x hz))
    rcases List.mem_cons.mp hx0 with rfl | hmem
    · omega
    · have hx := hle x (List.mem_cons_self ..)
      have hlt_rest := ih (fun z hz => hle z (List.mem_cons_of_mem x hz)) hmem
      omega

private theorem stepPtrAliasEntries_step (decls : List LocalDecl) (bbs : List BasicBlockData)
    {entries : List (List PtrLocalState)}
    (hsh : PtrEntriesShape bbs.length decls.length entries) :
    PtrEntriesShape bbs.length decls.length (stepPtrAliasEntries decls bbs entries) ∧
    (∀ dst < bbs.length, ∀ q < decls.length,
      ((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled =
        (entries.getD dst (initPtrEnv decls.length)).getD q .disabled ∨
      ptrStateRank decls.length
        (((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled) <
      ptrStateRank decls.length
        ((entries.getD dst (initPtrEnv decls.length)).getD q .disabled)) := by
  let b := bbs.length
  let n := decls.length
  have hfold_wf : ∀ (ss : List MirAst.Statement) (env : List PtrLocalState),
      (∀ p, PtrStateWf n (env.getD p .disabled)) →
      ∀ p, PtrStateWf n ((ss.foldl (ptrStmtStep decls) env).getD p .disabled) := by
    intro ss
    induction ss with
    | nil => intro env hwf p; exact hwf p
    | cons s rest ih =>
      intro env hwf p
      exact ih _ (ptrStmtStep_wf decls env hwf s) p
  have hin_wf : ∀ src, ∀ p, PtrStateWf n ((entries.getD src (initPtrEnv n)).getD p .disabled) := by
    intro src p
    by_cases hs : src < b
    · exact (hsh.2 src hs).2 p
    · have hnone : entries[src]? = none := List.getElem?_eq_none (by rw [hsh.1]; omega)
      have hget_none : entries.getD src (initPtrEnv n) = initPtrEnv n := by
        simp only [List.getD, hnone, Option.getD_none]
      rw [hget_none]
      by_cases hp : p < n
      · rw [initPtrEnv, getD_map_range _ _ _ hp]; trivial
      · have hpnone : (initPtrEnv n)[p]? = none := List.getElem?_eq_none (by simp [initPtrEnv]; omega)
        simp only [List.getD, hpnone, Option.getD_none]; trivial
  have hrow : ∀ dst < b,
      let row' := (stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv n)
      let row := entries.getD dst (initPtrEnv n)
      row'.length = n ∧
      (∀ p, PtrStateWf n (row'.getD p .disabled)) ∧
      (∀ q < n, row'.getD q .disabled = row.getD q .disabled ∨
        ptrStateRank n (row'.getD q .disabled) < ptrStateRank n (row.getD q .disabled)) := by
    intro dst hdst
    let stepFn (acc : List PtrLocalState) (src : Nat) : List PtrLocalState :=
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          joinPtrEnv n acc (bb.statements.foldl (ptrStmtStep decls) (entries.getD src (initPtrEnv n)))
        else acc
      | none => acc
    have hget : (stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv n) =
        (List.range b).foldl stepFn (entries.getD dst (initPtrEnv n)) := by
      simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
        List.getElem?_range hdst, Option.map_some, Option.getD_some]
      rfl
    dsimp only []
    rw [hget]
    suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
        acc.length = n →
        (∀ p, PtrStateWf n (acc.getD p .disabled)) →
        let res := srcs.foldl stepFn acc
        res.length = n ∧
        (∀ p, PtrStateWf n (res.getD p .disabled)) ∧
        (∀ q < n, res.getD q .disabled = acc.getD q .disabled ∨
          ptrStateRank n (res.getD q .disabled) < ptrStateRank n (acc.getD q .disabled)) from
      this (List.range b) (entries.getD dst (initPtrEnv n)) (hsh.2 dst hdst).1 (hsh.2 dst hdst).2
    intro srcs
    induction srcs with
    | nil =>
      intro acc hlen hwf
      exact ⟨hlen, hwf, fun _ _ => .inl rfl⟩
    | cons src rest ih =>
      intro acc hlen hwf
      have h1 : (stepFn acc src).length = n ∧
          (∀ p, PtrStateWf n ((stepFn acc src).getD p .disabled)) ∧
          (∀ q < n, (stepFn acc src).getD q .disabled = acc.getD q .disabled ∨
            ptrStateRank n ((stepFn acc src).getD q .disabled) <
              ptrStateRank n (acc.getD q .disabled)) := by
        dsimp only [stepFn]
        cases bbs[src]? with
        | none => exact ⟨hlen, hwf, fun _ _ => .inl rfl⟩
        | some bb =>
          by_cases hcont : (termTargets bb.terminator).contains dst = true
          · simp only [hcont, ↓reduceIte]
            refine ⟨by simp [joinPtrEnv, n], fun p => ?_, fun q hq => ?_⟩
            · by_cases hp : p < n
              · rw [joinPtrEnv, getD_map_range _ _ _ hp]
                exact joinPtrLocalState_wf (hwf p)
                  (hfold_wf bb.statements _ (hin_wf src) p)
              · let joined := joinPtrEnv n acc
                  (bb.statements.foldl (ptrStmtStep decls) (entries.getD src (initPtrEnv n)))
                have hnone : joined[p]? = none :=
                  List.getElem?_eq_none (by simp [joined, joinPtrEnv, n]; omega)
                change PtrStateWf n (joined[p]?.getD .disabled)
                rw [hnone]
                trivial
            · rw [joinPtrEnv, getD_map_range _ _ _ hq]
              exact joinPtrLocalState_eq_or_rank_lt (hfold_wf bb.statements _ (hin_wf src) q)
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            refine ⟨hlen, hwf, fun _ _ => ?_⟩
            simp
      obtain ⟨hlen2, hwf2, hrk2⟩ := ih (stepFn acc src) h1.1 h1.2.1
      dsimp only [List.foldl_cons]
      refine ⟨hlen2, hwf2, fun q hq => ?_⟩
      rcases h1.2.2 q hq with heq1 | hlt1 <;> rcases hrk2 q hq with heq2 | hlt2
      · left; exact heq2.trans heq1
      · right; rw [← heq1]; exact hlt2
      · right; rw [heq2]; exact hlt1
      · right; exact Nat.lt_trans hlt2 hlt1
  refine ⟨⟨by simp [stepPtrAliasEntries], fun dst hdst => ⟨(hrow dst hdst).1, (hrow dst hdst).2.1⟩⟩,
    fun dst hdst q hq => (hrow dst hdst).2.2 q hq⟩

private theorem sum_replicate_nat (k m : Nat) :
    (List.replicate k m).sum = k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.sum_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

private theorem getElem_eq_getD {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) (d : α) :
    xs[i] = xs.getD i d := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private theorem ptrEntriesRank_init (b n : Nat) :
    ptrEntriesRank b n (initPtrEntries b n) = b * n * (n + 5) := by
  have henv : ptrEnvRank n (initPtrEnv n) = n * (n + 5) := by
    unfold ptrEnvRank
    have hmap : (List.range n).map (fun q => ptrStateRank n ((initPtrEnv n).getD q .disabled)) =
        List.replicate n (n + 5) := by
      apply List.ext_getElem (by simp)
      intro q hq1 hq2
      have hq : q < n := by simpa using hq1
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [initPtrEnv, getD_map_range _ _ _ hq]
      rfl
    rw [hmap, sum_replicate_nat]
  unfold ptrEntriesRank
  have hmap2 : (List.range b).map
      (fun dst => ptrEnvRank n ((initPtrEntries b n).getD dst (initPtrEnv n))) =
      List.replicate b (n * (n + 5)) := by
    apply List.ext_getElem (by simp)
    intro dst hd1 hd2
    have hdst : dst < b := by simpa using hd1
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    rw [initPtrEntries, getD_map_range _ _ _ hdst, henv]
  rw [hmap2, sum_replicate_nat, Nat.mul_assoc]

/-- Unconditional finite-fuel convergence of `iterPtrAliasEntries` (proving the
`B * n * (n + 5) + 1` height bound stated on `ptrEnvAtEntry` in `Translate.lean`):
on any `decls` and any CFG `bbs`, `iterPtrAliasEntries` reaches an exact fixed
point of `stepPtrAliasEntries decls bbs`. -/
theorem iterPtrAliasEntries_stabilizes (decls : List LocalDecl) (bbs : List BasicBlockData) :
    let n := decls.length
    let b := bbs.length
    let fuel := b * n * (n + 5) + 1
    let init := initPtrEntries b n
    stepPtrAliasEntries decls bbs (iterPtrAliasEntries fuel decls bbs init) =
      iterPtrAliasEntries fuel decls bbs init := by
  dsimp only
  suffices ∀ (fuel : Nat) (entries : List (List PtrLocalState)),
      PtrEntriesShape bbs.length decls.length entries →
      ptrEntriesRank bbs.length decls.length entries < fuel →
      stepPtrAliasEntries decls bbs (iterPtrAliasEntries fuel decls bbs entries) =
        iterPtrAliasEntries fuel decls bbs entries by
    apply this (bbs.length * decls.length * (decls.length + 5) + 1)
      (initPtrEntries bbs.length decls.length) (initPtrEntries_shape bbs.length decls.length)
    rw [ptrEntriesRank_init]
    omega
  intro fuel
  induction fuel with
  | zero => intro _ _ hlt; omega
  | succ k ih =>
    intro entries hsh hlt
    simp only [iterPtrAliasEntries]
    by_cases hbeq : (stepPtrAliasEntries decls bbs entries == entries) = true
    · simp only [hbeq, ↓reduceIte]
      exact beq_iff_eq.mp hbeq
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hne : stepPtrAliasEntries decls bbs entries ≠ entries :=
        fun h => hbeq (beq_iff_eq.mpr h)
      obtain ⟨hsh', hstep⟩ := stepPtrAliasEntries_step decls bbs hsh
      have hdiff : ∃ dst < bbs.length, ∃ q < decls.length,
          ((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled ≠
            (entries.getD dst (initPtrEnv decls.length)).getD q .disabled := by
        apply Classical.byContradiction
        intro hall_eq
        apply hne
        apply List.ext_getElem (hsh'.1.trans hsh.1.symm)
        intro dst hd1 hd2
        have hdst : dst < bbs.length := by rw [← hsh'.1]; exact hd1
        rw [getElem_eq_getD _ _ hd1 (initPtrEnv decls.length),
            getElem_eq_getD _ _ hd2 (initPtrEnv decls.length)]
        apply List.ext_getElem ((hsh'.2 dst hdst).1.trans (hsh.2 dst hdst).1.symm)
        intro q hq1 hq2
        have hq : q < decls.length := by rw [← (hsh'.2 dst hdst).1]; exact hq1
        rw [getElem_eq_getD _ _ hq1 .disabled, getElem_eq_getD _ _ hq2 .disabled]
        exact Classical.byContradiction fun hneq => hall_eq ⟨dst, hdst, q, hq, hneq⟩
      obtain ⟨dst0, hdst0, q0, hq0, hneq0⟩ := hdiff
      have hrk_lt : ptrEntriesRank bbs.length decls.length (stepPtrAliasEntries decls bbs entries) <
          ptrEntriesRank bbs.length decls.length entries := by
        unfold ptrEntriesRank
        apply sum_map_le_and_lt_of_ne (x0 := dst0)
        · intro dst hdst_mem
          have hdst : dst < bbs.length := List.mem_range.mp hdst_mem
          unfold ptrEnvRank
          apply sum_map_le
          intro q hq_mem
          have hq : q < decls.length := List.mem_range.mp hq_mem
          rcases hstep dst hdst q hq with heq | hlt_q
          · rw [heq]; exact Nat.le_refl _
          · omega
        · exact List.mem_range.mpr hdst0
        · unfold ptrEnvRank
          apply sum_map_le_and_lt_of_ne (x0 := q0)
          · intro q hq_mem
            have hq : q < decls.length := List.mem_range.mp hq_mem
            rcases hstep dst0 hdst0 q hq with heq | hlt_q
            · rw [heq]; exact Nat.le_refl _
            · omega
          · exact List.mem_range.mpr hq0
          · rcases hstep dst0 hdst0 q0 hq0 with heq | hlt_q
            · exact False.elim (hneq0 heq)
            · exact hlt_q
      exact ih _ hsh' (by omega)

/-- Outgoing CFG edge closure of `ptrEnvAtEntry` holds unconditionally on any
CFG (`iterPtrAliasEntries_stabilizes`). -/
theorem ptrEnvAtEntry_fixed (body : CapturedMir) {src dst : Nat} {bb : BasicBlockData}
    (hbb : body.basicBlocks[src]? = some bb) (hdst : dst < body.basicBlocks.length)
    (htgt : dst ∈ termTargets bb.terminator) :
    subsumesPtrEnv body.localDecls.length
      (bb.statements.foldl (ptrStmtStep body.localDecls) (ptrEnvAtEntry body src))
      (ptrEnvAtEntry body dst) = true := by
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  let fuel := b * n * (n + 5) + 1
  let entries := iterPtrAliasEntries fuel body.localDecls body.basicBlocks (initPtrEntries b n)
  have hfix : stepPtrAliasEntries body.localDecls body.basicBlocks entries = entries :=
    iterPtrAliasEntries_stabilizes body.localDecls body.basicBlocks
  have hsrc : src < b := (List.getElem?_eq_some_iff.mp hbb).1
  change subsumesPtrEnv n
    (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
    (entries.getD dst (initPtrEnv n)) = true
  have hdst_fix : entries.getD dst (initPtrEnv n) =
      (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD dst (initPtrEnv n) := by
    rw [hfix]
  let stepFn (acc : List PtrLocalState) (s : Nat) : List PtrLocalState :=
    match body.basicBlocks[s]? with
    | some bb' =>
      if (termTargets bb'.terminator).contains dst then
        joinPtrEnv n acc (bb'.statements.foldl (ptrStmtStep body.localDecls) (entries.getD s (initPtrEnv n)))
      else acc
    | none => acc
  have hget : (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD dst (initPtrEnv n) =
      (List.range b).foldl stepFn (entries.getD dst (initPtrEnv n)) := by
    simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
      List.getElem?_range hdst, Option.map_some, Option.getD_some]
    rfl
  rw [hdst_fix, hget]
  have hfold_mono : ∀ (srcs : List Nat) (acc : List PtrLocalState),
      subsumesPtrEnv n acc (srcs.foldl stepFn acc) = true := by
    intro srcs
    induction srcs with
    | nil => intro acc; exact subsumesPtrEnv_refl n acc
    | cons s rest ih =>
      intro acc
      have h1 : subsumesPtrEnv n acc (stepFn acc s) = true := by
        dsimp only [stepFn]
        cases body.basicBlocks[s]? with
        | none => exact subsumesPtrEnv_refl n acc
        | some bb' =>
          by_cases hcont : (termTargets bb'.terminator).contains dst = true
          · simp only [hcont, ↓reduceIte]
            exact joinPtrEnv_subsumes_left n acc _
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            exact subsumesPtrEnv_refl n acc
      exact subsumesPtrEnv_trans h1 (ih (stepFn acc s))
  suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
      src ∈ srcs →
      subsumesPtrEnv n
        (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
        (srcs.foldl stepFn acc) = true from
    this (List.range b) (entries.getD dst (initPtrEnv n)) (List.mem_range.mpr hsrc)
  intro srcs
  induction srcs with
  | nil => intro _ hmem; simp at hmem
  | cons s rest ih =>
    intro acc hmem
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have h1 : subsumesPtrEnv n
          (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
          (stepFn acc src) = true := by
        dsimp only [stepFn]
        rw [hbb]
        simp only [List.contains_iff_mem.mpr htgt, ↓reduceIte]
        exact joinPtrEnv_subsumes_right n acc _
      exact subsumesPtrEnv_trans h1 (hfold_mono rest (stepFn acc src))
    · exact ih (stepFn acc s) hrest

theorem terminatorOk_termTargets_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {term : MirAst.Terminator}
    (ht : terminatorOk layouts decls nblocks term = true)
    {dst : Nat} (hdst : dst ∈ termTargets term) :
    dst < nblocks := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | goto target =>
    simp only [termTargets, List.mem_singleton] at hdst
    subst hdst
    simpa [terminatorOk] using ht
  | switchInt discr targets =>
    simp only [terminatorOk] at ht
    cases hit : switchIntType layouts decls (copyOp discr) with
    | none => simp [hit] at ht
    | some it =>
      simp only [hit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
      simp only [termTargets, List.mem_cons, List.mem_map] at hdst
      rcases hdst with rfl | ⟨p, hp, rfl⟩
      · exact ht.2
      · exact (ht.1.1.2 p hp).2
  | call _ _ _ _ _ => simp [terminatorOk] at ht
  | _ => simp [termTargets] at hdst

/-- On any CFG whose terminators satisfy `terminatorOk`, `iterPtrAliasEntries`
stabilizes (`iterPtrAliasEntries_stabilizes`), so `ptrAliasingOk body = true`
holds iff directly-borrowed locals are preserved parameters and every block
satisfies `blockPtrAliasOk` at `ptrEnvAtEntry body blk` (initial-entry and
outgoing-edge subsumption are automatic). -/
theorem ptrAliasingOk_iff_blockPtrAliasOk {body : CapturedMir}
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
    ptrAliasingOk body = true ↔
      ptrDeclLayoutsOk body = true ∧
      (∀ k ∈ bodyAddrTakenLocals body, 1 ≤ k ∧ k ≤ body.argCount) ∧
      (∀ bb ∈ body.basicBlocks,
        (∀ s ∈ bb.statements, stmtPreservesAddrTaken (bodyAddrTakenLocals body) s = true) ∧
        termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator = true) ∧
      (∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
        blockPtrAliasOk body.localDecls (ptrEnvAtEntry body blk) bb.statements = true) := by
  constructor
  · intro hpa
    obtain ⟨hargs, hpres, _, hblks⟩ := ptrAliasingOk_spec hpa
    exact ⟨ptrDeclLayoutsOk_of_ptrAliasingOk hpa, hargs, hpres, fun blk bb hbb =>
      (hblks blk (List.getElem?_eq_some_iff.mp hbb).1 bb hbb).1⟩
  · rintro ⟨hdlo, hargs, hpres, hblk⟩
    simp only [ptrAliasingOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨hdlo, hargs⟩, hpres⟩, subsumesPtrEnv_initPtrEnv _ _⟩, fun blk hblk_lt => ?_⟩
    cases hbb : body.basicBlocks[blk]? with
    | none => trivial
    | some bb =>
      simp only [Bool.and_eq_true, List.all_eq_true]
      refine ⟨hblk blk bb hbb, fun dst hdst => ?_⟩
      have hdst_lt : dst < body.basicBlocks.length :=
        terminatorOk_termTargets_lt (hterm bb (List.mem_of_getElem? hbb)) hdst
      exact ptrEnvAtEntry_fixed body hbb hdst_lt hdst

/-- Least fixed-point optimality of `ptrEnvAtEntry`: for any width-`n` pre-fixed
point `entries'` of `body`'s forward pointer-aliasing equations, `ptrEnvAtEntry`
is subsumed by `entries'` at every block `dst < body.basicBlocks.length`. -/
theorem ptrEnvAtEntry_least {body : CapturedMir} {entries' : List (List PtrLocalState)}
    (hlen' : ∀ blk < body.basicBlocks.length,
      (entries'.getD blk (initPtrEnv body.localDecls.length)).length = body.localDecls.length)
    (hpre : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      subsumesPtrEnv body.localDecls.length
        (bb.statements.foldl (ptrStmtStep body.localDecls)
          (entries'.getD src (initPtrEnv body.localDecls.length)))
        (entries'.getD dst (initPtrEnv body.localDecls.length)) = true)
    {dst : Nat} (hdst : dst < body.basicBlocks.length) :
    subsumesPtrEnv body.localDecls.length
      (ptrEnvAtEntry body dst)
      (entries'.getD dst (initPtrEnv body.localDecls.length)) = true := by
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  have hfold_ss : ∀ (ss : List MirAst.Statement) {e1 e2 : List PtrLocalState},
      e1.length = n → e2.length = n → subsumesPtrEnv n e1 e2 = true →
      subsumesPtrEnv n
        (ss.foldl (ptrStmtStep body.localDecls) e1)
        (ss.foldl (ptrStmtStep body.localDecls) e2) = true := by
    intro ss
    induction ss with
    | nil => intro _ _ _ _ h; exact h
    | cons s rest ih =>
      intro e1 e2 hl1 hl2 h
      exact ih (ptrStmtStep_length body.localDecls e1 s)
        (ptrStmtStep_length body.localDecls e2 s)
        (ptrStmtStep_mono body.localDecls hl1 hl2 h s)
  suffices ∀ (fuel : Nat) (entries : List (List PtrLocalState)),
      PtrEntriesShape b n entries →
      (∀ blk < b,
        subsumesPtrEnv n (entries.getD blk (initPtrEnv n))
          (entries'.getD blk (initPtrEnv n)) = true) →
      ∀ d < b,
        subsumesPtrEnv n
          ((iterPtrAliasEntries fuel body.localDecls body.basicBlocks entries).getD d (initPtrEnv n))
          (entries'.getD d (initPtrEnv n)) = true from
    this (b * n * (n + 5) + 1) (initPtrEntries b n) (initPtrEntries_shape b n)
      (fun blk hblk => by
        rw [initPtrEntries, getD_map_range _ _ _ hblk]
        exact subsumesPtrEnv_initPtrEnv n _)
      dst hdst
  intro fuel
  induction fuel with
  | zero => intro entries _ hsub d hd; exact hsub d hd
  | succ k ih =>
    intro entries hsh hsub d hd
    simp only [iterPtrAliasEntries]
    split
    · exact hsub d hd
    · apply ih (stepPtrAliasEntries body.localDecls body.basicBlocks entries)
        (stepPtrAliasEntries_step body.localDecls body.basicBlocks hsh).1 _ d hd
      intro blk hblk
      let stepFn (acc : List PtrLocalState) (src : Nat) : List PtrLocalState :=
        match body.basicBlocks[src]? with
        | some bb =>
          if (termTargets bb.terminator).contains blk then
            joinPtrEnv n acc
              (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
          else acc
        | none => acc
      have hget : (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD blk (initPtrEnv n) =
          (List.range b).foldl stepFn (entries.getD blk (initPtrEnv n)) := by
        simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
          List.getElem?_range hblk, Option.map_some, Option.getD_some]
        rfl
      rw [hget]
      suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
          subsumesPtrEnv n acc (entries'.getD blk (initPtrEnv n)) = true →
          subsumesPtrEnv n (srcs.foldl stepFn acc) (entries'.getD blk (initPtrEnv n)) = true from
        this (List.range b) (entries.getD blk (initPtrEnv n)) (hsub blk hblk)
      intro srcs
      induction srcs with
      | nil => intro acc hacc; exact hacc
      | cons src rest ihr =>
        intro acc hacc
        apply ihr (stepFn acc src)
        dsimp only [stepFn]
        cases hbb : body.basicBlocks[src]? with
        | none => exact hacc
        | some bb =>
          by_cases hcont : (termTargets bb.terminator).contains blk = true
          · simp only [hcont, ↓reduceIte]
            have hsrc_lt : src < b := (List.getElem?_eq_some_iff.mp hbb).1
            have htgt : blk ∈ termTargets bb.terminator := List.contains_iff_mem.mp hcont
            have hout_sub := hfold_ss bb.statements (hsh.2 src hsrc_lt).1 (hlen' src hsrc_lt)
              (hsub src hsrc_lt)
            exact joinPtrEnv_least hacc
              (subsumesPtrEnv_trans hout_sub (hpre src blk bb hbb hblk htgt))
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            exact hacc

/-- Mapping from Anneal borrow tags to MiniRust target `(addr, prov)` pairs for
initial-argument target places. -/
def borrowTargets (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry) (tag : Nat) :
    Option (Nat × Option Prov) := do
  let e ← lookupBorrow borrows tag
  let (_, relOff) ← ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩
  let baseAddr := ctx.addrs.getD e.targetLocal 0
  pure ((baseAddr + (relOff : Int)).toNat,
        some (⟨((ctx.base.length + e.targetLocal : Nat) : Int)⟩, ()))

/-- `ctx` enriched with `borrowTargets` for `borrows`. -/
def ctxWithBorrows (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry) : Ctx :=
  { ctx with ptrTargets := borrowTargets body ctx borrows }

@[simp] theorem borrowTargets_nil (body : CapturedMir) (ctx : Ctx) :
    borrowTargets body ctx [] = fun _ => none := by
  funext tag
  rfl

@[simp] theorem ctxWithBorrows_nil (body : CapturedMir) (ctx : Ctx) :
    ctxWithBorrows body ctx [] = { ctx with ptrTargets := fun _ => none } := by
  simp [ctxWithBorrows]

theorem borrowTargets_map_eq (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry)
    (f : BorrowEntry → BorrowEntry)
    (hf : ∀ e, (f e).tag = e.tag ∧ (f e).targetLocal = e.targetLocal ∧
      (f e).targetProjection = e.targetProjection) :
    borrowTargets body ctx (borrows.map f) = borrowTargets body ctx borrows := by
  funext tag
  unfold borrowTargets
  rw [lookupBorrow_map_eq (fun e => (hf e).1) tag]
  cases lookupBorrow borrows tag with
  | none => rfl
  | some e =>
    obtain ⟨_, hloc, hproj⟩ := hf e
    simp [hloc, hproj]

theorem ctxWithBorrows_invalidateDerefWriteBorrows (body : CapturedMir) (ctx : Ctx)
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hfull : MirSemantics.resolveDerefWriteFullProj locals locals (.ptr ptrVal 8) entry [] =
      entry.targetProjection) :
    ctxWithBorrows body ctx (invalidateDerefWriteBorrows locals borrows ⟨p, [.deref]⟩ []) =
      ctxWithBorrows body ctx borrows := by
  simp only [ctxWithBorrows,
    invalidateDerefWriteBorrows_eq_map locals borrows p ptrVal entry hp he hrlen hroff hfull]
  congr 1
  apply borrowTargets_map_eq
  intro e
  have hf := updateBorrowPermTreeAtProj_fields borrows e entry.targetLocal (some ptrVal.tag)
    entry.targetProjection 0 0 entry.targetFrameDepth
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

theorem LocalStorage.extend_ptrTargets {ctx1 ctx2 : Ctx} {A : List Gen.Allocation}
    {d : LocalDecl} {slot : LocalSlot} {p : Ptr} {layouts : Layout.LayoutTable}
    (hbaseEq : ctx1.base = ctx2.base)
    (h : LocalStorage ctx1 A d slot p layouts)
    (hext : isPtrTy d.ty = true → ∀ pv a pr, slot = .init (.ptr pv 8) →
      ctx2.ptrTargets pv.allocId = some (a, pr) → ctx1.ptrTargets pv.allocId = some (a, pr)) :
    LocalStorage ctx2 A d slot p layouts := by
  obtain ⟨id, hpid, hbase, haddr, haddrMax, hcls, hA⟩ := h
  refine ⟨id, hpid, hbaseEq ▸ hbase, haddr, haddrMax, hcls, ?_⟩
  cases hp_ty : isPtrTy d.ty with
  | false =>
    simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA ⊢
    exact hA
  | true =>
    simp only [hp_ty, ↓reduceIte] at hA ⊢
    cases slot with
    | dead => exact hA
    | uninit => exact hA
    | init v =>
      cases v with
      | ptr pv sz =>
        cases Nat.decEq sz 8 with
        | isFalse hne =>
          split at hA
          · next _ heq => injection heq with hv; injection hv with _ hsz; exact absurd hsz hne
          · exact hA
        | isTrue heq =>
          subst heq
          obtain ⟨tAddr, tProv, htlt, htgt, hAk⟩ := hA
          exact ⟨tAddr, tProv, htlt, fun a pr h2 => htgt a pr (hext hp_ty pv a pr rfl h2), hAk⟩
      | _ => exact hA

theorem LocalsOkA.extend_ptrTargets {body : CapturedMir} {ctx1 ctx2 : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hbaseEq : ctx1.base = ctx2.base)
    (hlo : LocalsOkA body ctx1 al locals lm A)
    (hext : ∀ (i : Nat) d pv a pr, body.localDecls[i]? = some d → isPtrTy d.ty = true →
      locals[i]? = some (.init (.ptr pv 8)) →
      ctx2.ptrTargets pv.allocId = some (a, pr) → ctx1.ptrTargets pv.allocId = some (a, pr)) :
    LocalsOkA body ctx2 al locals lm A :=
  { nlocals := hlo.nlocals
    slots := hlo.slots
    base := hbaseEq ▸ hlo.base
    keysNodup := hlo.keysNodup
    keysLocal := hlo.keysLocal
    live := hlo.live
    storage := fun i d slot p hd hs hp =>
      (hlo.storage i d slot p hd hs hp).extend_ptrTargets hbaseEq
        (fun hp_ty pv a pr hslot h2 => hext i d pv a pr hd hp_ty (hslot ▸ hs) h2)
    inj := hlo.inj
    owned := fun id a ha hlive hb => hlo.owned id a ha hlive (hbaseEq ▸ hb) }

/-- Synchronized borrow-table and flow-sensitive pointer/reference local
invariant for `StateRelN`. -/
structure BorrowsOk (body : CapturedMir) (ctx : Ctx) (view : List LocalSlot)
    (s : MachineState) (lm : Map Gen.LocalName Ptr) : Prop where
  nextTag_pos : (∃ d ∈ body.localDecls, isPtrTy d.ty = true) → 0 < s.memory.nextTag
  tags_pos : ∀ e ∈ s.memory.borrows, 0 < e.tag
  tags_lt : ∀ e ∈ s.memory.borrows, e.tag < s.memory.nextTag
  tags_nodup : (s.memory.borrows.map (·.tag)).Nodup
  dag_ordered : BorrowDagOrdered s.memory.borrows
  entries_ok : ∀ e ∈ s.memory.borrows,
    ∃ (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) (relOff : Nat),
      (e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
              parentTag := e.parentTag } ∨
       (mutbl = .mut ∧
         e = { rawPtrEntry e.tag .mut ⟨e.targetLocal, e.targetProjection⟩ with
               perm := .reserved, parentTag := e.parentTag }) ∨
       e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
             perm := .disabled, parentTag := e.parentTag }) ∧
      e.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩ =
        some (pointeeIt, relOff)
  entries_place : ∀ e ∈ s.memory.borrows,
    ⟨e.targetLocal, e.targetProjection⟩ ∈ bodyDirectBorrowPlaces body
  target_init : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
    ∃ v, view[k]? = some (.init v)
  target_ptrs : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
    view[k]? ≠ some .dead ∧
    mapGet lm (localName k) = some (localPtr ctx k) ∧
    (∀ d, body.localDecls[k]? = some d →
      isPtrTy d.ty = false ∧
      AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
      ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
  alias_ok : PtrEnvOk body view s.memory.borrows
    (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx)
  ptr_slots : ∀ (p : Nat) (dp : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
      (ptrVal : ProvenancePtr),
    body.localDecls[p]? = some dp →
    ptrPointeeOf dp.ty = some (mutbl, pointeeIt) →
    view[p]? = some (.init (.ptr ptrVal 8)) →
    ∃ (entry : BorrowEntry) (relOff : Nat),
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (pointeeIt, relOff)

theorem BorrowsOk.entry_perm_cases {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) {e : BorrowEntry} (he : e ∈ s.memory.borrows) :
    e.perm = .active ∨ e.perm = .reserved ∨ e.perm = .frozen ∨ e.perm = .disabled := by
  obtain ⟨mutbl, _, _, hform, _, _⟩ := hb.entries_ok e he
  rcases hform with h | ⟨_, h⟩ | h <;> rw [h]
  · cases mutbl <;> simp [rawPtrEntry, rawPtrPerm]
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inr rfl))

theorem BorrowsOk.target_ne_of_not_addrTaken {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) {i : Nat} (hi : i ∉ bodyAddrTakenLocals body) :
    ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i := by
  intro e he heq
  obtain ⟨_, _, _, _, hmem, _⟩ := hb.entries_ok e he
  exact hi (heq ▸ hmem)

/-- Any initialized pointer or reference local `p` whose static `ptrEnvBefore`
entry is not `.disabled` resolves to a live (non-`.disabled`) `BorrowEntry` in
`s.memory.borrows`, and to `.active` or `.reserved` whenever `p` is writable
(`isWritablePtrState`) and has mutable pointer/reference type (`mutbl = .mut`). -/
theorem BorrowsOk.usable_of_not_disabled {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {srcIt : Gen.IntType}
    {ptrVal : ProvenancePtr} {entry : BorrowEntry}
    (hndis_env : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠ .disabled)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hvp : view[p]? = some (.init (.ptr ptrVal 8)))
    (hlk : lookupBorrow s.memory.borrows ptrVal.tag = some entry) :
    entry.perm ≠ .disabled ∧
      (isWritablePtrState ((ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled) = true →
        srcMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  have hp_ok := hb.alias_ok p hp_lt
  cases hst : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    exact False.elim (hp_ok dp ptrVal hdp hisPtr hvp)
  | disabled =>
    exact False.elim (hndis_env hst)
  | live target peers hot writable =>
    rw [hst] at hp_ok
    obtain ⟨⟨entry', hlk', hndis', hnf', _, _, _⟩, _⟩ := hp_ok dp ptrVal hdp hisPtr hvp
    rw [hlk] at hlk'
    injection hlk' with heq
    subst heq
    refine ⟨hndis', fun hw hm => ?_⟩
    dsimp only [isWritablePtrState] at hw
    have hmut : isMutPtrLocal body.localDecls p = true := by
      subst hm
      simp [isMutPtrLocal, hdp, hp_ty]
    have hnf := hnf' hw hmut
    rcases hb.entry_perm_cases (lookupBorrow_mem_and_tag hlk).1 with hpe | hpe | hpe | hpe
    · exact .inl hpe
    · exact .inr hpe
    · exact absurd hpe hnf
    · exact absurd hpe hndis'

theorem BorrowsOk.ancestors_not_disabled {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {p : Nat} {dp : LocalDecl} {ptrVal : ProvenancePtr}
    (hndis_env : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠ .disabled)
    (hdp : body.localDecls[p]? = some dp) (hisPtr : isPtrTy dp.ty = true)
    (hvp : view[p]? = some (.init (.ptr ptrVal 8))) :
    ∀ anc ∈ s.memory.borrows,
      MirSemantics.isBorrowDescendantOrSelf s.memory.borrows ptrVal.tag anc.tag = true →
      anc.perm ≠ .disabled := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hp_ok := hb.alias_ok p hp_lt
  cases hst : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    exact False.elim (hp_ok dp ptrVal hdp hisPtr hvp)
  | disabled => exact False.elim (hndis_env hst)
  | live target peers hot writable =>
    rw [hst] at hp_ok
    obtain ⟨⟨_, _, _, _, _, _, hanc⟩, _⟩ := hp_ok dp ptrVal hdp hisPtr hvp
    intro anc hmem hdesc
    exact (hanc anc hmem (IsBorrowAncestorOrSelf.of_descendant hdesc)).1

theorem BorrowsOk.ancestors_writable {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {p : Nat} {dp : LocalDecl} {srcIt : Gen.IntType} {ptrVal : ProvenancePtr}
    (hw_env : isWritablePtrState ((ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled) = true)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (.mut, srcIt))
    (hvp : view[p]? = some (.init (.ptr ptrVal 8))) :
    ∀ anc ∈ s.memory.borrows, IsBorrowAncestorOrSelf s.memory.borrows ptrVal.tag anc.tag →
      anc.perm ≠ .disabled ∧ anc.perm ≠ .frozen := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  have hmut : isMutPtrLocal body.localDecls p = true := by simp [isMutPtrLocal, hdp, hp_ty]
  have hp_ok := hb.alias_ok p hp_lt
  cases hst : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    exact False.elim (hp_ok dp ptrVal hdp hisPtr hvp)
  | disabled => rw [hst] at hw_env; cases hw_env
  | live target peers hot writable =>
    rw [hst] at hp_ok hw_env
    dsimp only [isWritablePtrState] at hw_env
    obtain ⟨⟨_, _, _, _, _, _, hanc⟩, _⟩ := hp_ok dp ptrVal hdp hisPtr hvp
    intro anc hmem ha
    obtain ⟨hnd, hnf, _, _⟩ := hanc anc hmem ha
    exact ⟨hnd, hnf hw_env hmut⟩

theorem lookupBorrow_split_of_nodup {borrows : List BorrowEntry} {tag : Nat} {entry : BorrowEntry}
    (hnd : (borrows.map (·.tag)).Nodup)
    (hlk : lookupBorrow borrows tag = some entry) :
    ∃ pre suf,
      borrows = pre ++ entry :: suf ∧
      entry.tag = tag ∧
      (∀ b ∈ pre, b.tag ≠ tag) ∧
      (∀ b ∈ suf, b.tag ≠ tag) := by
  induction borrows with
  | nil => simp [lookupBorrow] at hlk
  | cons e rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot_mem, hnd_rest⟩ := hnd
    unfold lookupBorrow at hlk
    cases hb : Nat.beq e.tag tag with
    | true =>
      rw [hb] at hlk
      simp only [Option.some.injEq] at hlk
      subst hlk
      have htag : e.tag = tag := Nat.beq_eq.mp hb
      refine ⟨[], rest, rfl, htag, (fun _ hm => by cases hm), fun b hb_mem hbt => ?_⟩
      apply hnot_mem
      rw [htag, ← hbt]
      exact List.mem_map_of_mem hb_mem
    | false =>
      rw [hb] at hlk
      have hne : e.tag ≠ tag := fun h => by rw [Nat.beq_eq.mpr h] at hb; cases hb
      obtain ⟨pre, suf, rfl, htag, hpre, hsuf⟩ := ih hnd_rest hlk
      refine ⟨e :: pre, suf, rfl, htag, ?_, hsuf⟩
      intro b hb_mem
      rcases List.mem_cons.mp hb_mem with rfl | hb_pre
      · exact hne
      · exact hpre b hb_pre

theorem BorrowsOk.lookupBorrow_tag_ne_zero {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) {tag : Nat} {entry : BorrowEntry}
    (hlk : lookupBorrow s.memory.borrows tag = some entry) :
    tag ≠ 0 ∧ 0 < entry.tag ∧ entry.tag = tag := by
  obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlk
  have hpos := hb.tags_pos entry hmem
  exact ⟨by omega, hpos, htag⟩

theorem BorrowsOk.start {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hbor : s.memory.borrows = [])
    (hnext : (∃ d ∈ body.localDecls, isPtrTy d.ty = true) → 0 < s.memory.nextTag)
    (hinit : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
      ∃ v, view[k]? = some (.init v))
    (htgt : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
      view[k]? ≠ some .dead ∧
      mapGet lm (localName k) = some (localPtr ctx k) ∧
      (∀ d, body.localDecls[k]? = some d →
        isPtrTy d.ty = false ∧
        AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
        ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64))
    (hnoPtr : ∀ (p : Nat) dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? ≠ some (.init (.ptr pv 8))) :
    BorrowsOk body ctx view s lm where
  nextTag_pos := hnext
  tags_pos e he := by simp [hbor] at he
  tags_lt e he := by simp [hbor] at he
  tags_nodup := by simp [hbor]
  dag_ordered := by rw [hbor]; trivial
  entries_ok e he := by simp [hbor] at he
  entries_place e he := by simp [hbor] at he
  target_init := hinit
  target_ptrs := htgt
  alias_ok p _ := (PtrLocalOk.of_empty (fun dp pv hdp hpty => hnoPtr p dp pv hdp hpty)) _
  ptr_slots p dp mutbl pointeeIt ptrVal hdp hp hv := by
    have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hp]
    exact False.elim (hnoPtr p dp ptrVal hdp hp_ty hv)

theorem BorrowsOk.advance_keep {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hstep :
      let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
      ptrStmtStep body.localDecls env st =
        (List.range body.localDecls.length).map (fun q => env.getD q .disabled)) :
    BorrowsOk body ctx view (advanceStmt s locals' s.memory) lm where
  nextTag_pos := hb.nextTag_pos
  tags_pos := hb.tags_pos
  tags_lt := hb.tags_lt
  tags_nodup := hb.tags_nodup
  dag_ordered := hb.dag_ordered
  entries_ok := hb.entries_ok
  entries_place := hb.entries_place
  target_init := hb.target_init
  target_ptrs := hb.target_ptrs
  alias_ok := by
    simp only [advanceStmt]
    rw [Nat.add_eq, ptrEnvBefore_succ hbb hst, hstep]
    exact hb.alias_ok.of_map_range
  ptr_slots := hb.ptr_slots

theorem PtrEnvOk.set_nonptr {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (i : Nat) (slot' : LocalSlot)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    PtrEnvOk body (view.set i slot') borrows env := by
  have hv_eq : ∀ (q : Nat) (dq : LocalDecl) (pv : ProvenancePtr),
      body.localDecls[q]? = some dq → isPtrTy dq.ty = true →
      (view.set i slot')[q]? = some (LocalSlot.init (.ptr pv 8)) →
      view[q]? = some (LocalSlot.init (.ptr pv 8)) := by
    intro q dq pv hdq hpty hv
    by_cases hiq : i = q
    · subst hiq
      by_cases hlt : i < view.length
      · rw [List.getElem?_set_self hlt] at hv
        injection hv with hs
        exact False.elim (hnp dq pv hdq hpty hs)
      · rw [List.getElem?_eq_none (by simp; omega)] at hv
        cases hv
    · rwa [List.getElem?_set_ne hiq] at hv
  intro p hp
  have hp_ok := hok p hp
  cases hst : env.getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    intro dp pv hdp hpty hv
    exact hp_ok dp pv hdp hpty (hv_eq p dp pv hdp hpty hv)
  | disabled => trivial
  | live target peers hot writable =>
    rw [hst] at hp_ok
    intro dp pv hdp hpty hv
    obtain ⟨hent, hpeers⟩ := hp_ok dp pv hdp hpty (hv_eq p dp pv hdp hpty hv)
    exact ⟨hent, fun r hr dr pv_r hdr hptr hvr =>
      hpeers r hr dr pv_r hdr hptr (hv_eq r dr pv_r hdr hptr hvr)⟩

theorem BorrowsOk.advance_set_nonptr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm' : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm')
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hstep :
      let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
      ptrStmtStep body.localDecls env st =
        (List.range body.localDecls.length).map (fun q => env.getD q .disabled))
    (i : Nat) (slot' : LocalSlot)
    (hinit_addr : i ∈ bodyAddrTakenLocals body → ∃ v, slot' = .init v)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    BorrowsOk body ctx (view.set i slot') (advanceStmt s locals' s.memory) lm' := by
  have hb' := hb.advance_keep (locals' := locals') hbb hst hstep
  refine {
    nextTag_pos := hb'.nextTag_pos
    tags_pos := hb'.tags_pos
    tags_lt := hb'.tags_lt
    tags_nodup := hb'.tags_nodup
    dag_ordered := hb'.dag_ordered
    entries_ok := hb'.entries_ok
    entries_place := hb'.entries_place
    target_init := fun hfrag k hk => by
      obtain ⟨v0, hv0⟩ := hb'.target_init hfrag k hk
      by_cases hik : i = k
      · subst hik
        obtain ⟨v', rfl⟩ := hinit_addr hk
        have hlt : i < view.length := (List.getElem?_eq_some_iff.mp hv0).1
        exact ⟨v', List.getElem?_set_self hlt⟩
      · rw [List.getElem?_set_ne hik]
        exact ⟨v0, hv0⟩
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlm, hd⟩ := hb'.target_ptrs hfrag k hk
      refine ⟨?_, hlm, hd⟩
      by_cases hik : i = k
      · subst hik
        obtain ⟨v', rfl⟩ := hinit_addr hk
        by_cases hlt : i < view.length
        · rw [List.getElem?_set_self hlt]; simp
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
      · rw [List.getElem?_set_ne hik]
        exact hnd
    alias_ok := hb'.alias_ok.set_nonptr i slot' hnp
    ptr_slots := ?_ }
  intro p dp mutbl pointeeIt ptrVal hdp hp hv
  by_cases hip : i = p
  · subst hip
    have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hp]
    by_cases hlt : i < view.length
    · rw [List.getElem?_set_self hlt] at hv
      injection hv with hslot
      exact False.elim (hnp dp ptrVal hdp hp_ty hslot)
    · rw [List.getElem?_eq_none (by simp; omega)] at hv
      cases hv
  · rw [List.getElem?_set_ne hip] at hv
    exact hb'.ptr_slots p dp mutbl pointeeIt ptrVal hdp hp hv

theorem BorrowsOk.with_lm {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm lm' : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    (hlm : ∀ k ∈ bodyAddrTakenLocals body, mapGet lm' (localName k) = mapGet lm (localName k)) :
    BorrowsOk body ctx view s lm' :=
  { hb with
    target_ptrs := fun hfrag k hk => by
      obtain ⟨h0, h1, h2⟩ := hb.target_ptrs hfrag k hk
      exact ⟨h0, (hlm k hk).trans h1, h2⟩ }

/-- Anneal's state after jumping to block `t` with slots `locals`. -/
def jumpState (s : MachineState) (t : Nat) (locals : List LocalSlot) : MachineState :=
  { s with frame := { blockIdx := t, stmtIdx := 0, locals := locals } }

/-- Anneal's state after jumping to block `t` with unchanged locals. -/
def gotoState (s : MachineState) (t : Nat) : MachineState :=
  jumpState s t s.frame.locals

theorem BorrowsOk.jump {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    (hpa : ptrAliasingOk body = true)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstmt : bb.statements.length ≤ s.frame.stmtIdx)
    (target : Nat) (htgt : target ∈ termTargets bb.terminator)
    (locals' : List LocalSlot) :
    BorrowsOk body ctx view (jumpState s target locals') lm :=
  { nextTag_pos := hb.nextTag_pos
    tags_pos := hb.tags_pos
    tags_lt := hb.tags_lt
    tags_nodup := hb.tags_nodup
    dag_ordered := hb.dag_ordered
    entries_ok := hb.entries_ok
    entries_place := hb.entries_place
    target_init := hb.target_init
    target_ptrs := hb.target_ptrs
    alias_ok :=
      hb.alias_ok.of_subsumes (ptrEnvBefore_jump_subsumes hpa hbb hstmt htgt)
    ptr_slots := hb.ptr_slots }

theorem statementOk_rawPtr_false_of_scalar {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {dst : Place} {mutbl : MirAst.Mutability} {q : Place}
    {span : String}
    (hall : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    statementOk decls ⟨.assign dst (.rawPtr mutbl q), span⟩ layouts = false := by
  rcases dst with ⟨i, projs⟩
  cases projs with
  | nil =>
    simp only [statementOk, copyRv]
    cases hd : decls[i]? with
    | none => rfl
    | some d =>
      have hsc := hall d (List.mem_of_getElem? hd)
      cases hb : isBoolTy d.ty with
      | true => simp [hb, rvalueOkB]
      | false =>
        cases ho : isOrderingTy d.ty with
        | true => simp [hb, ho, rvalueOkO]
        | false =>
          cases htup : intBoolTupleOf d.ty with
          | some it => simp [hb, ho, htup, rvalueOkTuple]
          | none =>
            cases hit : intTypeOf d.ty with
            | some it => simp [hb, ho, htup, hit, rvalueOk, ptrDerefReadOk]
            | none => simp [scalarTypeOf, hb, ho, htup, hit] at hsc
  | cons p1 prest =>
    cases p1 with
    | field idx fieldTy =>
      simp only [statementOk]
      cases (decls[i]? >>= (tupleTypeOf layouts ·.ty)).isSome
      · rfl
      · simp only [Bool.true_and]
        cases placeIntType layouts decls ⟨i, .field idx fieldTy :: prest⟩ with
        | some it => simp [rvalueOk]
        | none =>
          cases tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            cases placeMirTy decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            simp [tupleRvalueOk]
    | deref =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decide (i < decls.length)
        · rfl
        · cases decls[i]? >>= (ptrPointeeOf ·.ty) with
          | none => rfl
          | some pair =>
            obtain ⟨m, pt⟩ := pair
            cases m <;> simp [copyRv, rvalueOk, ptrDerefReadOk]
      | cons _ _ => rfl
    | _ =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decls[i]? >>= (arrayTypeOf ·.ty) with
        | none => rfl
        | some pair => simp [rvalueOk]
      | cons _ _ => rfl

theorem statementOk_ref_false_of_scalar {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {dst : Place} {bkind : BorrowKind} {q : Place}
    {span : String}
    (hall : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    statementOk decls ⟨.assign dst (.ref bkind q), span⟩ layouts = false := by
  rcases dst with ⟨i, projs⟩
  cases projs with
  | nil =>
    simp only [statementOk, copyRv]
    cases hd : decls[i]? with
    | none => rfl
    | some d =>
      have hsc := hall d (List.mem_of_getElem? hd)
      cases hb : isBoolTy d.ty with
      | true => simp [hb, rvalueOkB]
      | false =>
        cases ho : isOrderingTy d.ty with
        | true => simp [hb, ho, rvalueOkO]
        | false =>
          cases htup : intBoolTupleOf d.ty with
          | some it => simp [hb, ho, htup, rvalueOkTuple]
          | none =>
            cases hit : intTypeOf d.ty with
            | some it => simp [hb, ho, htup, hit, rvalueOk, ptrDerefReadOk]
            | none => simp [scalarTypeOf, hb, ho, htup, hit] at hsc
  | cons p1 prest =>
    cases p1 with
    | field idx fieldTy =>
      simp only [statementOk]
      cases (decls[i]? >>= (tupleTypeOf layouts ·.ty)).isSome
      · rfl
      · simp only [Bool.true_and]
        cases placeIntType layouts decls ⟨i, .field idx fieldTy :: prest⟩ with
        | some it => simp [rvalueOk]
        | none =>
          cases tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            cases placeMirTy decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            simp [tupleRvalueOk]
    | deref =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decide (i < decls.length)
        · rfl
        · cases decls[i]? >>= (ptrPointeeOf ·.ty) with
          | none => rfl
          | some pair =>
            obtain ⟨m, pt⟩ := pair
            cases m <;> simp [copyRv, rvalueOk, ptrDerefReadOk]
      | cons _ _ => rfl
    | _ =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decls[i]? >>= (arrayTypeOf ·.ty) with
        | none => rfl
        | some pair => simp [rvalueOk]
      | cons _ _ => rfl

theorem bodyAddrTakenLocals_nil_of_allScalar {body : CapturedMir}
    (hfrag : inFragment body = true)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true) :
    ∀ k, k ∉ bodyAddrTakenLocals body := by
  intro k hk
  unfold inFragment at hfrag
  simp only [Bool.and_eq_true, List.all_eq_true] at hfrag
  have hbbs := hfrag.1.1.1.1.1.2
  unfold bodyAddrTakenLocals at hk
  rw [List.mem_flatMap] at hk
  obtain ⟨bb, hbb, hst_mem⟩ := hk
  rw [List.mem_filterMap] at hst_mem
  obtain ⟨st, hst, hkind⟩ := hst_mem
  have hstOk := (hbbs bb hbb).1.2 st hst
  obtain ⟨stKind, span⟩ := st
  cases stKind with
  | assign dst rv =>
    cases rv with
    | rawPtr mutbl q =>
      have hfalse := statementOk_rawPtr_false_of_scalar (layouts := body.layouts)
        (List.all_eq_true.mp hall) (dst := dst) (mutbl := mutbl) (q := q) (span := span)
      rw [hfalse] at hstOk
      cases hstOk
    | ref bkind q =>
      have hfalse := statementOk_ref_false_of_scalar (layouts := body.layouts)
        (List.all_eq_true.mp hall) (dst := dst) (bkind := bkind) (q := q) (span := span)
      rw [hfalse] at hstOk
      cases hstOk
    | _ => simp [directBorrowOf] at hkind
  | _ => simp at hkind

theorem derefPointeeTy_of_ptrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : ptrPointeeOf t = some (mutbl, it)) :
    derefPointeeTy t = some (.Int it) := by
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    simp [derefPointeeTy, translatePointeeRigidTy, translatePointeeRigidTyAux, hk, hb]
  | ref m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    simp [derefPointeeTy, translatePointeeRigidTy, translatePointeeRigidTyAux, hk, hb]
  | _ => simp [hk] at h

theorem evalOperand_copy_deref_uninit (locals : List LocalSlot) (p : Nat)
    (rest : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm ≠ .disabled)
    (hu : locals[entry.targetLocal]? = some .uninit) :
    evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals = .ub := by
  cases htp : entry.targetProjection with
  | nil =>
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, hu] <;> split <;> rfl
  | cons _ _ =>
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, hu] <;> split <;> rfl

theorem align_dvd_is_aligned {a b : Nat} {base : Int} {off : Nat}
    (_hapos : 0 < a) (hab : a ∣ b) (haoff : a ∣ off) (hbase : base % (b : Int) = 0) :
    Align.is_aligned ⟨a⟩ (base + (off : Int)) = true := by
  have hab' : (a : Int) ∣ (b : Int) := Int.ofNat_dvd.mpr hab
  have haoff' : (a : Int) ∣ (off : Int) := Int.ofNat_dvd.mpr haoff
  have hbdvd : (a : Int) ∣ base := Int.dvd_trans hab' (Int.dvd_of_emod_eq_zero hbase)
  have hsum : (a : Int) ∣ base + (off : Int) := Int.dvd_add hbdvd haoff'
  simp [Align.is_aligned, Int.emod_eq_zero_of_dvd hsum]

theorem noIndexProj_of_resolveFieldPath {layouts : Layout.LayoutTable}
    {spec leafSpec : TupleSpec} {projs : List ProjectionElem} {roff : Nat}
    (h : resolveFieldPath layouts spec projs = some (roff, leafSpec)) :
    noIndexProj projs = true := by
  induction projs generalizing spec roff leafSpec with
  | nil => rfl
  | cons p tl ih =>
    cases p with
    | field idx fty =>
      cases spec with
      | scalar _ => simp [resolveFieldPath] at h
      | tuple fs sz al =>
        simp only [resolveFieldPath] at h
        cases h1 : fs[idx]? with
        | none => simp [h1] at h
        | some fp =>
          cases h2 : specOfRigidTy layouts fty.kind fty.layoutIdx with
          | none => simp [h1, h2] at h
          | some es =>
            simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at h
            split at h
            · cases hr : resolveFieldPath layouts fp.2 tl with
              | none => simp [hr] at h
              | some rp => exact ih hr
            · simp at h
    | _ =>
      cases spec <;> simp [resolveFieldPath] at h

theorem ptrTargetSpec_bound {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff)) :
    ∃ d, decls[q.local_]? = some d ∧
      relOff + pointeeIt.size.bytes ≤ tyBytes (tyOf d layouts) := by
  rcases q with ⟨k, projs⟩
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · cases hdk : decls[k]? with
      | none => simp [hdk] at hspec
      | some d =>
        simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
        obtain ⟨it, hit, heq⟩ := hspec
        injection heq with hit_eq hrel0
        cases hit_eq.symm; cases hrel0.symm
        obtain ⟨hTd, _⟩ := tyOf_int (layouts := layouts) hit
        refine ⟨d, rfl, ?_⟩
        rw [hTd]
        simp [tyBytes]
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · cases hdk : decls[k]? with
          | none => simp [hdk] at hspec
          | some d =>
            simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at hspec
            | some apair =>
              obtain ⟨elemIt, count⟩ := apair
              simp only [ha] at hspec
              by_cases hc_bounds : minLen ≤ count ∧
                  (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · simp [hc_bounds] at hspec
                obtain ⟨he1, he2⟩ := hspec
                subst elemIt; subst relOff
                obtain ⟨hTd, _⟩ := tyOf_array (layouts := layouts) ha
                refine ⟨d, rfl, ?_⟩
                rw [hTd]
                simp only [tyBytes]
                have hc_eq : (Int.ofNat count).toNat = count := rfl
                rw [hc_eq]
                let idx := if fromEnd then count - offset else offset
                have hidx_lt : idx < count := by
                  dsimp only [idx]
                  cases fromEnd <;> simp_all <;> omega
                have hle : (idx + 1) * pointeeIt.size.bytes ≤ count * pointeeIt.size.bytes :=
                  Nat.mul_le_mul_right pointeeIt.size.bytes hidx_lt
                rw [Nat.add_mul, Nat.one_mul] at hle
                exact hle
              · simp [hc_bounds] at hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · cases hdk : decls[k]? with
        | none => simp [hdk] at hspec
        | some d =>
          simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hspec
          | some tpair =>
            obtain ⟨fields, size, align⟩ := tpair
            simp only [ht, Option.bind_some] at hspec
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at hspec
            | some rpair =>
              obtain ⟨relOff', leafSpec⟩ := rpair
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at hspec
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨he1, he2⟩ := hspec
                cases he1.symm; cases he2.symm
                obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
                have hwf : (TupleSpec.tuple fields size align).wf = true := by
                  simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf ht,
                    arrayTypeOf_none_of_tupleTypeOf ht, ht, isPtrTy_false_of_tupleTypeOf ht] using
                    hdeclsOk d (List.mem_of_getElem? hdk)
                obtain ⟨_, hrelBound⟩ := resolveFieldPath_wf hwf hres
                refine ⟨d, rfl, ?_⟩
                rw [hTd]
                simpa [TupleSpec.toMiniRustTy, tyBytes, TupleSpec.size] using hrelBound
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

theorem evalTargetPlace_deref {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hfrag : inFragment body = true)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body) :
    0 < (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat ∧
    CM.dereferenceable m.mem (offsetPtr (localPtr ctx q.local_) relOff) pointeeIt.size = .ok () := by
  obtain ⟨d, hdk, hbound⟩ := ptrTargetSpec_bound h.declsOk hspec
  obtain ⟨_, hlm_k, hd_k⟩ := hb.target_ptrs hfrag q.local_ hk_addr
  obtain ⟨_, haddrOk, _⟩ := hd_k d hdk
  have hpos : 0 < ctx.addrs.getD q.local_ 0 := haddrOk.2.1
  have hk_lt : q.local_ < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdk).1
  obtain ⟨_, slotk, hdk', hsk⟩ := h.slot_exists q.local_ hk_lt
  rw [hdk] at hdk'; cases hdk'
  obtain ⟨allocId, data, hpk, _, _, _, _, hlen, hAk⟩ :=
    h.locs.storage_any hdk hsk hlm_k (h.declsOk d (List.mem_of_getElem? hdk))
  refine ⟨by omega, ?_⟩
  exact cm_dereferenceable_offsetPtr h.shape (localPtr ctx q.local_) allocId hpk
    (itOf d body.layouts) data hAk relOff pointeeIt.size (by omega)

theorem evalTargetPlace {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body) :
    noIndexProj q.projection = true ∧
    (∀ rest, q.projection ≠ .deref :: rest) ∧
    GoodSize pointeeIt.size.bytes ∧
    (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat < 2 ^ 64 ∧
    ({ addr := ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat : Int),
       provenance := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()) } : Ptr) =
      offsetPtr (localPtr ctx q.local_) relOff ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (offsetPtr (localPtr ctx q.local_) relOff).addr = true ∧
    (∀ targetPe, translatePlace body.localDecls q = some targetPe →
      evalPlace m targetPe =
        .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx q.local_) relOff, metadata := none },
                 aligned := true }, .Int pointeeIt), m)) := by
  obtain ⟨hnd_k, hlm_k, hd_k⟩ := hb.target_ptrs hfrag q.local_ hk_addr
  rcases q with ⟨k, projs⟩
  simp only [] at hk_addr hnd_k hlm_k hd_k ⊢
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · next hrange =>
      cases hdk : body.localDecls[k]? with
      | none => simp [hdk] at hspec
      | some d =>
        simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
        obtain ⟨it, hit, heq⟩ := hspec
        injection heq with hit_eq hrel0
        cases hit_eq.symm; cases hrel0.symm
        have hgood := intTypeOf_good hit
        have hpos := hgood.pos
        obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
        obtain ⟨hTd, hitd⟩ := tyOf_int (layouts := body.layouts) hit
        rw [hitd] at haddrOk
        rw [hTd] at haddrMax
        simp only [tyBytes] at haddrMax
        have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
        have htlt : (ctx.addrs.getD k 0 + (0 : Int)).toNat < 2 ^ 64 := by
          have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
          omega
        have hptrEq :
            ({ addr := ((ctx.addrs.getD k 0 + (0 : Int)).toNat : Int),
               provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
            offsetPtr (localPtr ctx k) 0 := by
          simp only [offsetPtr, localPtr]
          rw [Int.toNat_of_nonneg (by omega)]
          rfl
        have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (offsetPtr (localPtr ctx k) 0).addr = true := by
          simpa [offsetPtr, localPtr] using
            align_dvd_is_aligned hpos (Nat.dvd_refl _) (Nat.dvd_zero _) haddrOk.1
        refine ⟨rfl, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        have hloc := (h.hf.2 k d hdk).2
        rw [hTd] at hloc
        have hev := evalPlace_local_some h.shape k (.Int pointeeIt) hloc (localPtr ctx k) hlm_k
        simpa [offsetPtr] using hev
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · next hrange =>
          cases hdk : body.localDecls[k]? with
          | none => simp [hdk] at hspec
          | some d =>
            simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at hspec
            | some apair =>
              obtain ⟨elemIt, count⟩ := apair
              simp only [ha] at hspec
              by_cases hc_bounds : minLen ≤ count ∧
                  (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · simp [hc_bounds] at hspec
                obtain ⟨he1, he2⟩ := hspec
                subst elemIt; subst relOff
                have hgood := arrayTypeOf_good ha
                have hpos := hgood.pos
                obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
                obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) ha
                rw [hitd] at haddrOk
                rw [hTd] at haddrMax
                simp only [tyBytes] at haddrMax
                have hc_eq : (Int.ofNat count).toNat = count := rfl
                rw [hc_eq] at haddrMax
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
                let idx := if fromEnd then count - offset else offset
                have hidx_lt : idx < count := by
                  dsimp only [idx]
                  cases fromEnd <;> simp_all <;> omega
                have hoff_lt : idx * pointeeIt.size.bytes < count * pointeeIt.size.bytes :=
                  Nat.mul_lt_mul_of_pos_right hidx_lt hpos
                have hoff_int : ((idx * pointeeIt.size.bytes : Nat) : Int) <
                    (count : Int) * (pointeeIt.size.bytes : Int) := by
                  rw [← Int.natCast_mul]
                  exact Int.ofNat_lt.mpr hoff_lt
                have htlt : (ctx.addrs.getD k 0 + ((idx * pointeeIt.size.bytes : Nat) : Int)).toNat < 2 ^ 64 := by
                  have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
                  omega
                have hptrEq :
                    ({ addr := ((ctx.addrs.getD k 0 + ((idx * pointeeIt.size.bytes : Nat) : Int)).toNat : Int),
                       provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
                    offsetPtr (localPtr ctx k) (idx * pointeeIt.size.bytes) := by
                  simp only [offsetPtr, localPtr]
                  rw [Int.toNat_of_nonneg (by omega)]
                have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩
                    (offsetPtr (localPtr ctx k) (idx * pointeeIt.size.bytes)).addr = true := by
                  have hdvd : pointeeIt.size.bytes ∣ idx * pointeeIt.size.bytes :=
                    ⟨idx, Nat.mul_comm _ _⟩
                  simpa [offsetPtr, localPtr] using
                    align_dvd_is_aligned hpos (Nat.dvd_refl _) hdvd haddrOk.1
                refine ⟨rfl, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
                have hbound := h.array_bound k d pointeeIt count hdk ha
                have hcnt_lt : count < 2 ^ 63 := by
                  have h1 : count * 1 ≤ count * pointeeIt.size.bytes :=
                    Nat.mul_le_mul_left count hpos
                  omega
                have hoff_263 : offset < 2 ^ 63 := by
                  cases fromEnd <;> simp_all <;> omega
                have hprojOk : projOk body.localDecls count (.constantIndex offset minLen fromEnd) = true := by
                  cases fromEnd <;> simp_all [projOk]
                have hprojIdx : projIdx view count (.constantIndex offset minLen fromEnd) = some idx := by
                  have hnot_lt : ¬ (count < minLen) := by omega
                  simp [projIdx, hnot_lt, idx, hidx_lt]
                exact evalPlace_constantIndex_same h k d hdk pointeeIt count ha (localPtr ctx k) hlm_k
                  offset minLen fromEnd hprojOk targetPe hpe idx hprojIdx
              · simp [hc_bounds] at hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · next hrange =>
        cases hdk : body.localDecls[k]? with
        | none => simp [hdk] at hspec
        | some d =>
          simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ht : tupleTypeOf body.layouts d.ty with
          | none => simp [ht] at hspec
          | some tpair =>
            obtain ⟨fields, size, align⟩ := tpair
            simp only [ht, Option.bind_some] at hspec
            cases hres : resolveFieldPath body.layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at hspec
            | some rpair =>
              obtain ⟨relOff', leafSpec⟩ := rpair
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at hspec
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨he1, he2⟩ := hspec
                cases he1.symm; cases he2.symm
                obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
                obtain ⟨hTd, hitd⟩ := tyOf_tupleSpec ht
                rw [hitd] at haddrOk
                rw [hTd] at haddrMax
                simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
                obtain ⟨_, slotk, hdk', hsk⟩ := h.slot_exists k hrange.2
                rw [hdk] at hdk'; cases hdk'
                obtain ⟨rootVal, rfl⟩ :=
                  (hns k d slotk hdk hsk (scalarTypeOf_none_of_tupleTypeOf ht) hnotPtr).1
                have hslotOk := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp
                  (h.slots k d (.init rootVal) hdk hsk)
                have hrootWf := hslotOk.1
                obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
                have hgood : GoodSize pointeeIt.size.bytes :=
                  (goodAlignBytes_iff pointeeIt.size.bytes).mp hleafWf
                have hpos := hgood.pos
                have hrel_lt : relOff < size := by simp [TupleSpec.size] at hrelBound; omega
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
                have htlt : (ctx.addrs.getD k 0 + (relOff : Int)).toNat < 2 ^ 64 := by
                  have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
                  omega
                have hptrEq :
                    ({ addr := ((ctx.addrs.getD k 0 + (relOff : Int)).toNat : Int),
                       provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
                    offsetPtr (localPtr ctx k) relOff := by
                  simp only [offsetPtr, localPtr]
                  rw [Int.toNat_of_nonneg (by omega)]
                obtain ⟨halignDvd, hoffDvd⟩ := resolveFieldPath_align hrootWf hres
                have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩
                    (offsetPtr (localPtr ctx k) relOff).addr = true := by
                  simpa [offsetPtr, localPtr] using
                    align_dvd_is_aligned hpos halignDvd hoffDvd haddrOk.1
                have hnoIdx : noIndexProj (.field idx fieldTy :: prest) = true :=
                  noIndexProj_of_resolveFieldPath hres
                refine ⟨hnoIdx, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
                have hloc := (h.hf.2 k d hdk).2
                rw [hTd] at hloc
                obtain ⟨allocId, hpk, _, _, _, _, hAk⟩ :=
                  h.locs.storage_nonptr k d (.init rootVal) (localPtr ctx k) hdk hsk hlm_k hnotPtr
                rw [declSlotData_of_tupleSpec ht] at hAk
                have hdlen : ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size :=
                  TupleSpec.encodeVal_length (.tuple fields size align) rootVal hrootWf
                have hbound : size < 2 ^ 63 := by
                  simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
                  exact hrootWf.1.2
                have hrootEval : evalPlace m (.Local (localName k)) =
                    .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx k) 0, metadata := none },
                             aligned := true },
                           (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
                  simpa [offsetPtr] using evalPlace_local_some h.shape k _ hloc (localPtr ctx k) hlm_k
                have hpeEval := evalPlace_ptr_fieldPath h.shape (localPtr ctx k) allocId hpk
                  (itOf d body.layouts) ((TupleSpec.tuple fields size align).encodeVal rootVal) hAk
                  (by rw [hdlen]; exact hbound) hbase0 (by rw [hdlen]; exact haddrMax)
                  (.Local (localName k)) 0 (.tuple fields size align) hrootEval hrootWf
                  (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: prest) targetPe hpe
                  relOff (.scalar pointeeIt) hres
                simpa [TupleSpec.toMiniRustTy] using hpeEval
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

theorem evalPtrLoad {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (p : Nat) (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (srcIt : Gen.IntType)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt)) :
    (∃ (ptrVal : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) (m1 : Mach),
      view[p]? = some (.init (.ptr ptrVal 8)) ∧
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      evalValue m (.Load (.Local (localName p))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              declPtrTy dp.ty), m1) ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      ∃ msg, evalValue m (.Load (.Local (localName p))) = .error (.ub msg)) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  obtain ⟨hTdp, hitdp⟩ := tyOf_isPtrTy (layouts := body.layouts) hisPtr
  have hloc := (h.hf.2 p dp hdp).2
  rw [hTdp] at hloc
  obtain ⟨_, slotp, hdp', hsp⟩ := h.slot_exists p hp_lt
  rw [hdp] at hdp'; cases hdp'
  have hslotOk := h.slots p dp slotp hdp hsp
  cases slotp with
  | dead =>
    right
    refine ⟨.inr hsp, ?_⟩
    cases hlm_p : mapGet lm (localName p) with
    | none =>
      exact ⟨"access to a dead local",
        by simp [evalValue, evalPlace_local_none h.shape p (declPtrTy dp.ty) hloc hlm_p]⟩
    | some ptr_p =>
      obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .dead ptr_p hdp hsp hlm_p
      simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
      obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
      exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hmsg]⟩
  | uninit =>
    right
    refine ⟨.inl hsp, ?_⟩
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .uninit ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
    exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
      placeLoad, hmsg]⟩
  | init v =>
    left
    obtain ⟨ptrVal, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtr (.init v)).mp hslotOk
    obtain ⟨entry, relOff, hoff0, hlookup, htspec⟩ :=
      hb.ptr_slots p dp srcMutbl srcIt ptrVal hdp hp_ty hsp
    obtain ⟨hentry_mem, _⟩ := lookupBorrow_mem_and_tag hlookup
    obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry hentry_mem
    obtain ⟨_, _, hgood, htlt, hptrEq, hal, _⟩ :=
      evalTargetPlace h hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨htpos, htderef⟩ :=
      evalTargetPlace_deref h hb hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ :=
      h.locs.storage p dp (.init (.ptr ptrVal 8)) ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, hitdp] at hAp
    obtain ⟨tAddr, tProv, htlt0, htgt, hAk⟩ := hAp
    have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId =
        some ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat,
              some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ())) := by
      simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
      simp [hlookup, htspec]
    obtain ⟨rfl, rfl⟩ := htgt _ _ hbt
    have htal : Align.is_aligned ⟨srcIt.size.bytes⟩
        (((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int)) = true := by
      rw [← hptrEq] at hal
      exact hal
    have htderef' : CM.dereferenceable m.mem
        { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
          provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) }
        srcIt.size = .ok () := by
      rw [← hptrEq] at htderef
      exact htderef
    obtain ⟨m1, hm1, hs1⟩ := typedLoad_ptr_declPtrTy h.shape ptr_p id hpid dp.ty srcMutbl srcIt
      hp_ty hgood _ htpos htlt0 _ htal htderef' hAk
    rw [hptrEq] at hm1
    refine ⟨ptrVal, entry, relOff, m1, hsp, hoff0, hlookup, hk_addr, htspec,
      by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hm1],
      FrameOk.mk' h.hf hs1 h.locs h.declsOk h.nonScalar⟩

/-! ## Symbolic Tree Borrows state-machine & protector invariants (`spec/mem/tree_borrows/*`) -/

/-- Unprotected foreign writes always succeed without UB
(`spec/mem/tree_borrows/state_machine_unprotected.md`). -/
theorem PermissionUnprot.foreign_write_ok (p : Gen.PermissionUnprot) :
    ∃ p', PermissionUnprot.foreign_write p = .ok p' := by
  cases p <;> exact ⟨_, rfl⟩

/-- `PermissionProt::prevents_deallocation` holds if and only if
`PermissionProt::foreign_write` raises UB, discharging the inline invariant note
in `spec/mem/tree_borrows/state_machine_protected.md`. -/
theorem PermissionProt.prevents_deallocation_iff_foreign_write_err (p : Gen.PermissionProt) :
    PermissionProt.prevents_deallocation p = true ↔
      ∃ msg, PermissionProt.foreign_write p = .error (.ub msg) := by
  cases p with
  | Reserved hl hf =>
    cases hl <;> simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]
  | Frozen hl =>
    cases hl <;> simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]
  | Unique | Disabled | Cell =>
    simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]

/-- Combined `Permission::prevents_deallocation` holds if and only if a foreign
write transition (`Permission::transition p .Write .Foreign`) raises UB
(`spec/mem/tree_borrows/state_machine.md`). -/
theorem Permission.prevents_deallocation_iff_foreign_write_err (p : Gen.Permission) :
    Permission.prevents_deallocation p = true ↔
      ∃ msg, Permission.transition p .Write .Foreign = .error (.ub msg) := by
  cases p with
  | Unprot u =>
    obtain ⟨u', hu'⟩ := PermissionUnprot.foreign_write_ok u
    simp [Permission.prevents_deallocation, PermissionUnprot.prevents_deallocation,
      Permission.transition, PermissionUnprot.transition, hu', pure, Except.pure, bind, Except.bind]
  | Prot pr =>
    simp only [Permission.prevents_deallocation, Permission.transition, PermissionProt.transition,
      PermissionProt.prevents_deallocation_iff_foreign_write_err]
    constructor
    · rintro ⟨msg, h⟩
      exact ⟨msg, by simp [h, bind, Except.bind]⟩
    · rintro ⟨msg, h⟩
      cases hfw : PermissionProt.foreign_write pr with
      | ok pr' => simp [hfw, pure, Except.pure, bind, Except.bind] at h
      | error e =>
        simp [hfw, bind, Except.bind] at h
        subst h
        exact ⟨msg, rfl⟩

/-- `Permission::transition` preserves `Permission::matches_protector` across all
access kinds and node relations (`spec/mem/tree_borrows/state_machine.md`). -/
theorem Permission.transition_preserves_matches_protector
    {p p' : Gen.Permission} {prot : Gen.Protected} {kind : Gen.AccessKind} {rel : Gen.NodeRelation}
    (hm : Permission.matches_protector p prot = true)
    (ht : Permission.transition p kind rel = .ok p') :
    Permission.matches_protector p' prot = true := by
  cases p with
  | Unprot u =>
    cases hp : PermissionUnprot.transition u kind rel with
    | error e => simp [Permission.transition, hp, bind, Except.bind] at ht
    | ok u' =>
      simp [Permission.transition, hp, pure, Except.pure, bind, Except.bind] at ht
      subst ht
      simpa [Permission.matches_protector] using hm
  | Prot pr =>
    cases hp : PermissionProt.transition pr kind rel with
    | error e => simp [Permission.transition, hp, bind, Except.bind] at ht
    | ok pr' =>
      simp [Permission.transition, hp, pure, Except.pure, bind, Except.bind] at ht
      subst ht
      simpa [Permission.matches_protector] using hm

/-- Every permission returned by `ReborrowSettings::perm` satisfies
`Permission::matches_protector` for the target `Protected` mode
(`spec/mem/tree_borrows/reborrow_settings.md`). -/
theorem ReborrowSettings.perm_matches_protector
    {ptrTy : Gen.PtrType} {prot : Gen.Protected} {iw inside frozen : Bool} {p : Gen.Permission}
    (hp : ReborrowSettings.perm ptrTy prot iw inside frozen = .ok p) :
    Permission.matches_protector p prot = true := by
  unfold ReborrowSettings.perm at hp
  cases ptrTy with
  | Ref mutbl pointee =>
    cases mutbl with
    | Immutable =>
      cases frozen <;> cases hprot : Protected.yes prot <;>
        simp [hprot, pure, Except.pure] at hp <;> subst hp <;>
        simp [Permission.matches_protector, hprot]
    | Mutable =>
      cases hiw : (iw && inside) with
      | true =>
        cases hprot : Protected.yes prot <;>
          simp [hiw, hprot, pure, Except.pure, specPanic] at hp
        subst hp
        simp [Permission.matches_protector, hprot]
      | false =>
        cases frozen <;> cases hprot : Protected.yes prot <;>
          simp [hiw, hprot, pure, Except.pure] at hp <;> subst hp <;>
          simp [Permission.matches_protector, hprot]
  | Box pointee =>
    cases hiw : (iw && inside) with
    | true =>
      cases hprot : Protected.yes prot <;>
        simp [hiw, hprot, pure, Except.pure, specPanic] at hp
      subst hp
      simp [Permission.matches_protector, hprot]
    | false =>
      cases frozen <;> cases hprot : Protected.yes prot <;>
        simp [hiw, hprot, pure, Except.pure] at hp <;> subst hp <;>
        simp [Permission.matches_protector, hprot]
  | Raw _ | FnPtr | VTablePtr _ =>
    simp [specPanic] at hp

private theorem mapM_loop_forall {α β : Type} {f : α → Interp β} {P : β → Prop}
    (hf : ∀ a b, f a = .ok b → P b) :
    ∀ (xs : List α) (acc : List β),
      (∀ y ∈ acc, P y) →
      ∀ ys, List.mapM.loop f xs acc = .ok ys → ∀ y ∈ ys, P y
  | [], acc, hacc, ys, h => by
    simp [List.mapM.loop, pure, Except.pure] at h
    subst h
    intro y hy
    exact hacc y (List.mem_reverse.mp hy)
  | x :: xs, acc, hacc, ys, h => by
    simp only [List.mapM.loop] at h
    cases hx : f x with
    | error _ => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      dsimp only [bind, Except.bind] at h
      refine mapM_loop_forall hf xs (b :: acc) ?_ ys h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact hf x y hx
      · exact hacc y hmem

/-- Whenever `ReborrowSettings::new` returns `Some(s)`, both `s.outside` and
every byte permission in `s.inside` match `s.protected`, guaranteeing that
`TreeBorrowsMemory::reborrow`'s `matches_protector` assertion never panics
(`spec/mem/tree_borrows/{reborrow_settings,memory}.md`). -/
theorem ReborrowSettings.new_matches_protector {Provenance : Type}
    {lookup : Gen.ThinPointer Provenance → Interp Gen.VTable}
    {ptr : Gen.Pointer Provenance} {ptrTy : Gen.PtrType}
    {fnEntry : Bool} {params : Gen.TreeBorrowsParams} {fnIw : Bool}
    {s : Gen.ReborrowSettings}
    (hnew : ReborrowSettings.new lookup ptr ptrTy fnEntry params fnIw = .ok (some s)) :
    Permission.matches_protector s.outside s.«protected» = true ∧
      ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
  unfold ReborrowSettings.new at hnew
  have hunpin_body :
      ∀ info : Gen.PointeeInfo,
        PtrType.safe_pointee ptrTy = some info →
        (do
          let prot : Gen.Protected :=
            if fnEntry then match ptrTy with | .Box _ => .Weak | _ => .Strong else .No
          let iw : Bool := Protected.yes prot && params.implicit_writes && fnIw
          let freezeMask ←
            UnsafeCellStrategy.freeze_mask lookup info.unsafe_cells info.layout ptr.metadata
          let inside ← freezeMask.mapM (fun freeze =>
            ReborrowSettings.perm ptrTy prot iw true freeze)
          let outside ← ReborrowSettings.perm ptrTy prot iw false info.freeze
          pure (some { inside := inside, outside := outside, «protected» := prot } :
            Option Gen.ReborrowSettings)) = .ok (some s) →
        Permission.matches_protector s.outside s.«protected» = true ∧
          ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
    intro info _ hh
    cases hmask : UnsafeCellStrategy.freeze_mask lookup info.unsafe_cells info.layout ptr.metadata with
    | error _ => rw [hmask] at hh; cases hh
    | ok mask =>
      rw [hmask] at hh
      dsimp only [bind, Except.bind] at hh
      generalize hin : List.mapM (m := Interp) _ mask = inRes at hh
      cases inRes with
      | error _ => cases hh
      | ok inside =>
        dsimp only at hh
        generalize hout : ReborrowSettings.perm ptrTy _ _ false info.freeze = outRes at hh
        cases outRes with
        | error _ => cases hh
        | ok outside =>
          dsimp only [pure, Except.pure] at hh
          injection hh with hsome
          injection hsome with hs
          rw [← hs]
          refine ⟨ReborrowSettings.perm_matches_protector hout, ?_⟩
          exact mapM_loop_forall (fun _ _ hp => ReborrowSettings.perm_matches_protector hp)
            mask [] (by intro _ h; cases h) inside hin
  cases ptrTy with
  | Raw _ | FnPtr | VTablePtr _ => cases hnew
  | Ref mutbl info =>
    cases mutbl with
    | Immutable => exact hunpin_body info rfl hnew
    | Mutable =>
      dsimp only [PtrType.safe_pointee] at hnew
      cases hu : info.unpin <;> simp only [hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnew
      · cases hnew
      · exact hunpin_body info rfl hnew
  | Box info =>
    dsimp only [PtrType.safe_pointee] at hnew
    cases hu : info.unpin <;> simp only [hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnew
    · cases hnew
    · exact hunpin_body info rfl hnew

/-- On any permission matching a live (`Protected.yes prot = true`) protector,
`Permission::unprotect` succeeds without panicking and yields an unprotected
permission matching `Protected::No`, guaranteeing `TreeBorrowsMemory::release_protector`'s
`Permission::unprotect` step never panics (`spec/mem/tree_borrows/{state_machine,memory}.md`). -/
theorem Permission.unprotect_matches_no
    {p : Gen.Permission} {prot : Gen.Protected}
    (hm : Permission.matches_protector p prot = true)
    (hyes : Protected.yes prot = true) :
    ∃ p' acc, Permission.unprotect p = .ok (p', acc) ∧
      Permission.matches_protector p' .No = true := by
  cases p with
  | Unprot _ => simp [Permission.matches_protector, hyes] at hm
  | Prot pr =>
    refine ⟨.Unprot (PermissionProt.unprotect pr).1, (PermissionProt.unprotect pr).2, rfl, ?_⟩
    simp [Permission.matches_protector, Protected.yes]

end MiniRustSpec.Correspondence
