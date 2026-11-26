import Anneal.Rustc.V2026_06_01.SymbolicEval.SymTableGvnAndCanonState

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Compositional join-point cuts, first-order MIR CFG syntax and concrete semantics, join-point
pruning refinement, and compositional diamond joins (sections 3-3.4).
-/

/-!
## Section 3 — Compositional Join-Point Cut (`mergeJoinStates`, `wpJoinBlock_sound`, `wpCfgSymGvn_sound`)
-/

/-- Evaluate a symbolic `Slot SymId` to a concrete `Slot Nat` under `tbl` and `env`. -/
def evalSymSlot (tbl : SymTable) (env : SymEnv) : Slot SymId → Slot Nat
  | .dead g => .dead g
  | .uninit g => .uninit g
  | .live symId g borrowed loan => .live (evalSymId tbl env symId) g borrowed loan

/-- Evaluate a symbolic `CanonState SymId` to a concrete `CanonState Nat`. -/
def evalSymCanonState (tbl : SymTable) (env : SymEnv) (st : CanonState SymId) : CanonState Nat :=
  { slots := st.slots.map (evalSymSlot tbl env) }

theorem getSlotAt_map_evalSymSlot (tbl : SymTable) (env : SymEnv) :
    ∀ (slots : List (Slot SymId)) (loc : LocalId),
      getSlotAt (slots.map (evalSymSlot tbl env)) loc =
        evalSymSlot tbl env (getSlotAt slots loc)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, loc + 1 => getSlotAt_map_evalSymSlot tbl env xs loc

theorem evalSymCanonState_getSlot (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) (loc : LocalId) :
    (evalSymCanonState tbl env st).getSlot loc =
      evalSymSlot tbl env (st.getSlot loc) :=
  getSlotAt_map_evalSymSlot tbl env st.slots loc

/-- Well-formedness of a symbolic `Slot SymId` at `SymTable` bound `bound`. -/
def ValidSymSlot (bound : Nat) : Slot SymId → Prop
  | .dead _ => True
  | .uninit _ => True
  | .live symId _ _ _ => symId < bound

theorem ValidSymSlot.mono {b₁ b₂ : Nat} {s : Slot SymId}
    (h : ValidSymSlot b₁ s) (hle : b₁ ≤ b₂) : ValidSymSlot b₂ s := by
  cases s with
  | dead _ => trivial
  | uninit _ => trivial
  | live symId _ _ _ => exact Nat.lt_of_lt_of_le h hle

theorem evalSymSlot_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {s : Slot SymId}
    (hSlot : ValidSymSlot tbl₁.nodes.length s) :
    evalSymSlot tbl₁ env s = evalSymSlot tbl₂ env s := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live symId g b loan =>
    dsimp [evalSymSlot]
    rw [evalSymId_mono hValid hExt env hSlot]

/-- Merge two canonical symbolic slots `(sT, sF)` under branch condition `condId` in `tbl`.
    Returns `some (mergedSlot, tbl')` when the slot shapes/generations/loans agree at the
    join point (the canonical live-pruned invariant), interning `.ite condId idT idF`
    (which automatically folds `ite condId id id ↦ id` without allocating a node when
    both branches hold the same `SymId`). -/
def mergeJoinSlot (tbl : SymTable) (condId : Nat) (sT sF : Slot SymId) :
    Option (Slot SymId × SymTable) :=
  match sT, sF with
  | .dead gT, .dead gF =>
    if gT == gF then some (.dead gT, tbl) else none
  | .uninit gT, .uninit gF =>
    if gT == gF then some (.uninit gT, tbl) else none
  | .live idT gT bT loanT, .live idF gF bF loanF =>
    if gT == gF && bT == bF && decide (loanT = loanF) then
      let (mergedId, tbl') := internNode tbl (.ite condId idT idF)
      some (.live mergedId gT bT loanT, tbl')
    else
      none
  | _, _ => none

theorem mergeJoinSlot_spec {tbl : SymTable} {condId : Nat} {sT sF sM : Slot SymId}
    {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hCond : condId < tbl.nodes.length)
    (hValidT : ValidSymSlot tbl.nodes.length sT)
    (hValidF : ValidSymSlot tbl.nodes.length sF)
    (hMerge : mergeJoinSlot tbl condId sT sF = some (sM, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymSlot tbl'.nodes.length sM ∧
      ∀ env : SymEnv,
        evalSymSlot tbl' env sM =
          (if evalSymId tbl env condId != 0 then
            evalSymSlot tbl env sT
          else
            evalSymSlot tbl env sF) := by
  cases sT with
  | dead gT =>
    cases sF with
    | dead gF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEq
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hg : gT = gF := of_decide_eq_true hEq
        subst hg
        refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
        intro env
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge
    | uninit _ => cases hMerge
    | live _ _ _ _ => cases hMerge
  | uninit gT =>
    cases sF with
    | dead _ => cases hMerge
    | uninit gF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEq
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hg : gT = gF := of_decide_eq_true hEq
        subst hg
        refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
        intro env
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge
    | live _ _ _ _ => cases hMerge
  | live idT gT bT loanT =>
    cases sF with
    | dead _ => cases hMerge
    | uninit _ => cases hMerge
    | live idF gF bF loanF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEqAll
        simp [Bool.and_eq_true] at hEqAll
        rcases hEqAll with ⟨⟨hg, hb⟩, hloan⟩
        subst hg hb hloan
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hIteValid : ValidNode tbl.nodes.length (.ite condId idT idF) :=
          ⟨hCond, hValidT, hValidF⟩
        have hIntValid := internNode_valid hValid hIteValid
        have hIntExt := internNode_extends tbl (.ite condId idT idF)
        refine ⟨hIntValid.1, hIntExt, hIntValid.2, ?_⟩
        intro env
        dsimp [evalSymSlot]
        have hIntEval := internNode_eval hValid hIteValid env
        rw [hIntEval]
        dsimp [evalSymNodeWith]
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge

/-- Merge two lists of canonical symbolic slots pointwise in `tbl`. -/
def mergeJoinSlots (tbl : SymTable) (condId : Nat) :
    List (Slot SymId) → List (Slot SymId) → Option (List (Slot SymId) × SymTable)
  | [], [] => some ([], tbl)
  | sT :: restT, sF :: restF =>
    match mergeJoinSlot tbl condId sT sF with
    | none => none
    | some (sM, tbl₁) =>
      match mergeJoinSlots tbl₁ condId restT restF with
      | none => none
      | some (restM, tbl₂) => some (sM :: restM, tbl₂)
  | _, _ => none

/-- Merge two canonical symbolic states `(stT, stF)` under branch condition `condId`
    and apply CPS spine forcing (`forceCanonState`) to the merged state. -/
def mergeJoinStates (tbl : SymTable) (condId : Nat)
    (stT stF : CanonState SymId) : Option (CanonState SymId × SymTable) :=
  match mergeJoinSlots tbl condId stT.slots stF.slots with
  | none => none
  | some (slotsM, tbl') =>
    forceCanonState { slots := slotsM } (fun forced => some (forced, tbl'))

/-- Pointwise validity of a list of symbolic slots at `SymTable` bound `bound`. -/
def ValidSymSlots (bound : Nat) : List (Slot SymId) → Prop
  | [] => True
  | s :: rest => ValidSymSlot bound s ∧ ValidSymSlots bound rest

theorem ValidSymSlots.mono {b₁ b₂ : Nat} :
    ∀ {slots : List (Slot SymId)}, ValidSymSlots b₁ slots → b₁ ≤ b₂ → ValidSymSlots b₂ slots
  | [], _, _ => trivial
  | _ :: _, ⟨hHead, hTail⟩, hle =>
    ⟨hHead.mono hle, ValidSymSlots.mono hTail hle⟩

theorem map_evalSymSlot_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) :
    ∀ {slots : List (Slot SymId)},
      ValidSymSlots tbl₁.nodes.length slots →
      slots.map (evalSymSlot tbl₁ env) = slots.map (evalSymSlot tbl₂ env)
  | [], _ => rfl
  | s :: rest, ⟨hHead, hTail⟩ => by
    simp only [List.map_cons]
    rw [evalSymSlot_mono hValid hExt env hHead]
    rw [map_evalSymSlot_mono hValid hExt env hTail]

/-- Well-formedness of a symbolic `CanonState SymId` at `SymTable` bound `bound`. -/
def ValidSymCanonState (bound : Nat) (st : CanonState SymId) : Prop :=
  ValidSymSlots bound st.slots

theorem evalSymCanonState_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {st : CanonState SymId}
    (hSt : ValidSymCanonState tbl₁.nodes.length st) :
    evalSymCanonState tbl₁ env st = evalSymCanonState tbl₂ env st := by
  dsimp [evalSymCanonState]
  rw [map_evalSymSlot_mono hValid hExt env hSt]

theorem mergeJoinSlots_spec {condId : Nat} :
    ∀ (slotsT slotsF : List (Slot SymId)) (tbl : SymTable)
      (slotsM : List (Slot SymId)) (tbl' : SymTable),
      ValidTable tbl →
      condId < tbl.nodes.length →
      ValidSymSlots tbl.nodes.length slotsT →
      ValidSymSlots tbl.nodes.length slotsF →
      mergeJoinSlots tbl condId slotsT slotsF = some (slotsM, tbl') →
      ValidTable tbl' ∧
        tbl.Extends tbl' ∧
        ValidSymSlots tbl'.nodes.length slotsM ∧
        ∀ env : SymEnv,
          slotsM.map (evalSymSlot tbl' env) =
            (if evalSymId tbl env condId != 0 then
              slotsT.map (evalSymSlot tbl env)
            else
              slotsF.map (evalSymSlot tbl env))
  | [], [], tbl, slotsM, tbl', hValid, _, _, _, hMerge => by
    injection hMerge with hPair
    injection hPair with hS hT
    subst hS hT
    refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
    intro env
    cases (evalSymId tbl env condId != 0) <;> rfl
  | [], _ :: _, _, _, _, _, _, _, _, hMerge => by cases hMerge
  | _ :: _, [], _, _, _, _, _, _, _, hMerge => by cases hMerge
  | sT :: restT, sF :: restF, tbl, slotsM, tbl', hValid, hCond,
    ⟨hHeadT, hTailT⟩, ⟨hHeadF, hTailF⟩, hMerge => by
    dsimp [mergeJoinSlots] at hMerge
    cases hStep₁ : mergeJoinSlot tbl condId sT sF with
    | none =>
      rw [hStep₁] at hMerge
      cases hMerge
    | some pair₁ =>
      rcases pair₁ with ⟨sM, tbl₁⟩
      rw [hStep₁] at hMerge
      dsimp at hMerge
      have hSpec₁ := mergeJoinSlot_spec hValid hCond hHeadT hHeadF hStep₁
      rcases hSpec₁ with ⟨hValid₁, hExt₁, hValidSM, hEvalSM⟩
      have hLenLe₁ : tbl.nodes.length ≤ tbl₁.nodes.length := hExt₁.length_le
      have hCond₁ : condId < tbl₁.nodes.length := Nat.lt_of_lt_of_le hCond hLenLe₁
      have hTailT₁ : ValidSymSlots tbl₁.nodes.length restT := hTailT.mono hLenLe₁
      have hTailF₁ : ValidSymSlots tbl₁.nodes.length restF := hTailF.mono hLenLe₁
      cases hStep₂ : mergeJoinSlots tbl₁ condId restT restF with
      | none =>
        rw [hStep₂] at hMerge
        cases hMerge
      | some pair₂ =>
        rcases pair₂ with ⟨restM, tbl₂⟩
        rw [hStep₂] at hMerge
        dsimp at hMerge
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hSpec₂ := mergeJoinSlots_spec restT restF tbl₁ restM tbl₂
          hValid₁ hCond₁ hTailT₁ hTailF₁ hStep₂
        rcases hSpec₂ with ⟨hValid₂, hExt₂, hValidRestM, hEvalRestM⟩
        have hLenLe₂ : tbl₁.nodes.length ≤ tbl₂.nodes.length := hExt₂.length_le
        refine ⟨hValid₂, hExt₁.trans hExt₂, ⟨hValidSM.mono hLenLe₂, hValidRestM⟩, ?_⟩
        intro env
        simp only [List.map_cons]
        rw [← evalSymSlot_mono hValid₁ hExt₂ env hValidSM]
        rw [hEvalSM env, hEvalRestM env]
        rw [← evalSymId_mono hValid hExt₁ env hCond]
        rw [← map_evalSymSlot_mono hValid hExt₁ env hTailT]
        rw [← map_evalSymSlot_mono hValid hExt₁ env hTailF]
        cases (evalSymId tbl env condId != 0) <;> rfl

/-- **Compositional Join-Point Merge Theorem (`mergeJoinStates_eval`)**:
    When two canonical symbolic post-states `(stT, stF)` merge under branch condition
    `condId` in `tbl` via `mergeJoinStates tbl condId stT stF = some (stM, tbl')`,
    `tbl'` is a valid monotone extension of `tbl` and evaluating the single merged
    state `stM` in `tbl'` under any concrete `env` equals `evalSymCanonState tbl env stT`
    when `evalSymId tbl env condId != 0` and `evalSymCanonState tbl env stF` otherwise! -/
theorem mergeJoinStates_eval {tbl : SymTable} {condId : Nat}
    {stT stF stM : CanonState SymId} {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hCond : condId < tbl.nodes.length)
    (hValidT : ValidSymCanonState tbl.nodes.length stT)
    (hValidF : ValidSymCanonState tbl.nodes.length stF)
    (hMerge : mergeJoinStates tbl condId stT stF = some (stM, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length stM ∧
      ∀ env : SymEnv,
        evalSymCanonState tbl' env stM =
          (if evalSymId tbl env condId != 0 then
            evalSymCanonState tbl env stT
          else
            evalSymCanonState tbl env stF) := by
  dsimp [mergeJoinStates] at hMerge
  cases hSlots : mergeJoinSlots tbl condId stT.slots stF.slots with
  | none =>
    rw [hSlots] at hMerge
    cases hMerge
  | some pair =>
    rcases pair with ⟨slotsM, tbl₁⟩
    rw [hSlots] at hMerge
    change forceCanonState { slots := slotsM } (fun forced => some (forced, tbl₁)) =
      some (stM, tbl') at hMerge
    rw [forceCanonState_eq] at hMerge
    injection hMerge with hPair
    injection hPair with hStM hTbl
    subst hStM hTbl
    have hSpec := mergeJoinSlots_spec stT.slots stF.slots tbl slotsM tbl₁
      hValid hCond hValidT hValidF hSlots
    rcases hSpec with ⟨hValid₁, hExt₁, hValidM, hEvalM⟩
    refine ⟨hValid₁, hExt₁, hValidM, ?_⟩
    intro env
    dsimp [evalSymCanonState]
    rw [hEvalM env]
    cases (evalSymId tbl env condId != 0) <;> rfl

/-- Identical slots merge to themselves without allocating any node (for any condition). -/
theorem mergeJoinSlot_self (tbl : SymTable) (condId : Nat) (s : Slot SymId) :
    mergeJoinSlot tbl condId s s = some (s, tbl) := by
  have hNat : ∀ n : Nat, (n == n) = true := fun n => decide_eq_true rfl
  cases s with
  | dead g =>
    dsimp only [mergeJoinSlot]
    rw [hNat g]
    rfl
  | uninit g =>
    dsimp only [mergeJoinSlot]
    rw [hNat g]
    rfl
  | live id g b loan =>
    dsimp only [mergeJoinSlot]
    have hb : (b == b) = true := decide_eq_true rfl
    have hl : decide (loan = loan) = true := decide_eq_true rfl
    rw [hNat g, hb, hl]
    dsimp only [internNode]
    rw [hNat id]
    rfl

theorem mergeJoinSlots_self (tbl : SymTable) (condId : Nat) :
    ∀ (ss : List (Slot SymId)), mergeJoinSlots tbl condId ss ss = some (ss, tbl)
  | [] => rfl
  | s :: rest => by
    dsimp only [mergeJoinSlots]
    rw [mergeJoinSlot_self]
    dsimp only
    rw [mergeJoinSlots_self tbl condId rest]

/-- **Join Sharing (`mergeJoinSlots_shared`)**: every slot position on which the two branch
    states agree is returned *unchanged* by the merge — the very same `SymId`, with no `ite`
    node allocated for it. -/
theorem mergeJoinSlots_shared {condId : Nat} :
    ∀ (slotsT slotsF : List (Slot SymId)) (tbl : SymTable) (slotsM : List (Slot SymId))
      (tbl' : SymTable),
      mergeJoinSlots tbl condId slotsT slotsF = some (slotsM, tbl') →
      ∀ i, getSlotAt slotsT i = getSlotAt slotsF i → getSlotAt slotsM i = getSlotAt slotsT i
  | [], [], tbl, slotsM, tbl', hMerge, i, _ => by
    injection hMerge with hPair
    injection hPair with hS _
    subst hS
    rfl
  | [], _ :: _, _, _, _, hMerge, _, _ => by cases hMerge
  | _ :: _, [], _, _, _, hMerge, _, _ => by cases hMerge
  | sT :: restT, sF :: restF, tbl, slotsM, tbl', hMerge, i, hEq => by
    dsimp only [mergeJoinSlots] at hMerge
    cases hStep₁ : mergeJoinSlot tbl condId sT sF with
    | none => rw [hStep₁] at hMerge; cases hMerge
    | some pair₁ =>
      rcases pair₁ with ⟨sM, tbl₁⟩
      rw [hStep₁] at hMerge
      dsimp only at hMerge
      cases hStep₂ : mergeJoinSlots tbl₁ condId restT restF with
      | none => rw [hStep₂] at hMerge; cases hMerge
      | some pair₂ =>
        rcases pair₂ with ⟨restM, tbl₂⟩
        rw [hStep₂] at hMerge
        dsimp only at hMerge
        injection hMerge with hPair
        injection hPair with hS _
        subst hS
        cases i with
        | zero =>
          have hEq' : sT = sF := hEq
          subst hEq'
          rw [mergeJoinSlot_self] at hStep₁
          injection hStep₁ with h
          injection h with h1 _
          subst h1
          rfl
        | succ j =>
          exact mergeJoinSlots_shared restT restF tbl₁ restM tbl₂ hStep₂ j hEq

/-- State-level join sharing: locals identical in both branch states stay shared verbatim. -/
theorem mergeJoinStates_shared {tbl : SymTable} {condId : Nat} {stT stF stM : CanonState SymId}
    {tbl' : SymTable} (hMerge : mergeJoinStates tbl condId stT stF = some (stM, tbl'))
    (loc : LocalId) (hEq : stT.getSlot loc = stF.getSlot loc) :
    stM.getSlot loc = stT.getSlot loc := by
  dsimp only [mergeJoinStates] at hMerge
  cases hSlots : mergeJoinSlots tbl condId stT.slots stF.slots with
  | none => rw [hSlots] at hMerge; cases hMerge
  | some pair =>
    rcases pair with ⟨slotsM, tbl₁⟩
    rw [hSlots] at hMerge
    dsimp only at hMerge
    rw [forceCanonState_eq] at hMerge
    injection hMerge with hPair
    injection hPair with hStM _
    subst hStM
    exact mergeJoinSlots_shared stT.slots stF.slots tbl slotsM tbl₁ hSlots loc hEq

/-- Merging a state with itself is the identity and allocates nothing. -/
theorem mergeJoinStates_self (tbl : SymTable) (condId : Nat) (st : CanonState SymId) :
    mergeJoinStates tbl condId st st = some (st, tbl) := by
  dsimp only [mergeJoinStates]
  rw [mergeJoinSlots_self]
  dsimp only
  rw [forceCanonState_eq]

/-!
### 3.2 First-Order MIR CFG Syntax & Mask-Free Concrete Semantics (`execCfg`)

**Trust boundary.** The concrete operational semantics `execCfg` below is the plain
multi-block MIR semantics (`goto` / `switchInt` / `ret` / `unreachable`) over the *unpruned*
dense local state: it never consults liveness masks or join points. Join-point liveness masks
are *untrusted hints* (`JoinHints`) consumed only by the symbolic evaluator `symEvalCfgGvn`;
every soundness theorem below quantifies over **all** hints, so a wrong (too-aggressive) mask
can only make symbolic verification *fail*, never make it unsound.
-/

/-- Basic block identifier in a MIR CFG. -/
abbrev BlockId := Nat

/-- First-order MIR right-hand-side expression (`MirRvalue`). -/
inductive MirRvalue where
  | const (val : Nat)
  | use (src : LocalId)
  | op1 (op : SymOp1) (src : LocalId)
  | op2 (op : SymOp2) (lhs rhs : LocalId)
  | derefRef (ptr : LocalId)

/-- First-order MIR statement (`MirStmt`) covering scalar assignment, storage lifecycle
    (`storageLive` / `storageDead`), assertions (`assert`), borrow creation (`retagBorrow`,
    which marks `target` as `borrowed = true` and records `(target, gen)` in `dst`'s
    `loanTarget`), and indirect write-through-reference (`storeRef ptr rv`, i.e., `*ptr := rv`,
    which checks temporal borrow-generation validity `curGen == expGen` and updates the
    aliased referent `target` in place; the write bumps the referent's generation, which
    invalidates every *other* outstanding loan, and re-validates the writer's own loan). -/
inductive MirStmt where
  | assign (dst : LocalId) (rv : MirRvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | assert (cond : LocalId)
  | retagBorrow (dst target : LocalId)
  | storeRef (ptr : LocalId) (rv : MirRvalue)

/-- First-order MIR block terminator (`MirTerm`). A *diamond* is an ordinary
    `switchInt discr thenBb elseBb` whose two arm blocks both end in `goto joinBb`;
    `switchTable discr cases otherwiseBb` is an N-way `SwitchInt` jump table matching
    `discr` against `(caseVal, targetBb)` pairs with fallback `otherwiseBb`. -/
inductive MirTerm where
  | goto (target : BlockId)
  | switchInt (discr : LocalId) (thenBb elseBb : BlockId)
  | switchTable (discr : LocalId) (cases : List (Nat × BlockId)) (otherwiseBb : BlockId)
  | ret (retLoc : LocalId)
  | unreachable

/-- A basic block in the MIR CFG. -/
structure MirBlock where
  stmts : List MirStmt := []
  term : MirTerm := .unreachable

/-- A MIR Control-Flow Graph indexed by `BlockId`. -/
structure MirCfg where
  blocks : List MirBlock := []

/-- Untrusted join-point liveness hints: `hints j = some mask` asks the symbolic evaluator to
    merge diamonds joining at block `j` after pruning every local `i` with `mask[i] = false`
    (`hints j = none` makes it path-split instead). The concrete semantics never reads hints. -/
abbrev JoinHints := BlockId → Option (List Bool)

/-- Concrete execution outcome of a MIR CFG:
    - `.ret val`: normal return with concrete `u64` value `val`.
    - `.fault`: UB / assertion failure / read of a dead-or-uninitialized local / write to a
      dead (`StorageDead`) or undeclared local / dangling-borrow generation mismatch /
      `unreachable` / missing block.
    - `.outOfFuel`: step fuel exhausted. -/
inductive ExecOutcome where
  | ret (val : Nat)
  | fault
  | outOfFuel
  deriving DecidableEq

/-- Read a live concrete scalar from `st` at `loc`, returning `none` if the slot is dead,
    uninitialized, **or holds a loan**: a reference is not a scalar, and in this untyped slot model
    a pointer slot's value is only the snapshot of its referent taken at borrow time, so reading
    it as a scalar (`use`, `op1`/`op2`, `assert`, `switchInt`, `ret`) would expose stale data.
    References are consumed only through `derefRef` / `storeRef`. -/
def readConcreteScalar (st : CanonState Nat) (loc : LocalId) : Option Nat :=
  match st.getSlot loc with
  | .live v _ _ none => some v
  | _ => none

/-- Concrete evaluation of a `MirRvalue` in `st : CanonState Nat` (constants are reduced to
    `u64` words). `.derefRef ptr` checks that `ptr` holds an active `loanTarget = some (target,
    expGen)` AND that `target` is currently a scalar slot `.live targetVal curGen true none` with
    `curGen == expGen` (temporal borrow-generation check; dereferencing a reference-to-reference
    is rejected so an inner reference slot's borrow-time snapshot is never read as a scalar). -/
def evalConcreteRvalue (st : CanonState Nat) : MirRvalue → Option Nat
  | .const v => some (wrap64 v)
  | .use src => readConcreteScalar st src
  | .op1 op src =>
    match readConcreteScalar st src with
    | some v => some (evalSymOp1 op v)
    | none => none
  | .op2 op lhs rhs =>
    match readConcreteScalar st lhs, readConcreteScalar st rhs with
    | some a, some b => some (evalSymOp2 op a b)
    | _, _ => none
  | .derefRef ptr =>
    match st.getSlot ptr with
    | .live _ _ _ (some (target, expGen)) =>
      match st.getSlot target with
      | .live targetVal curGen true none =>
        if curGen == expGen then some targetVal else none
      | _ => none
    | _ => none

/-- Faulting slot write: assigning into a **dead** slot (`StorageDead`, never `StorageLive`d,
    or an undeclared / out-of-range local) is MIR UB and returns `none`; writing an `uninit`
    slot initializes it (`borrowed := false`). Overwriting an *unborrowed* `live` slot keeps its
    generation; overwriting a **borrowed** `live` slot through its owner invalidates every
    outstanding loan (Stacked Borrows pops, and Tree Borrows disables, all references derived
    from a parent that is written) by bumping the generation and clearing `borrowed`. -/
def Slot.writeVal? {Val : Type} (s : Slot Val) (v : Val)
    (loanTarget : Option (LocalId × Nat)) : Option (Slot Val) :=
  match s with
  | .dead _ => none
  | .uninit g => some (.live v g false loanTarget)
  | .live _ g false _ => some (.live v g false loanTarget)
  | .live _ g true _ => some (.live v (g + 1) false loanTarget)

/-- Owner-read transition on a slot: reading a local directly through its owner succeeds and
    preserves its value and `loanTarget`, but if the slot was currently borrowed (`borrowed =
    true`), the owner read invalidates outstanding loans to this slot by bumping its
    generation to `g + 1` and clearing `borrowed := false`. On unborrowed slots this is the
    identity.

    Aliasing discipline: every loan is treated as a **unique** (`&mut`) loan, as in Stacked
    Borrows, where a read through the parent pops all `Unique` items above it. This is stricter
    than Tree Borrows, where a foreign read merely *freezes* an `Active` loan (later reads through
    it stay legal) and leaves a `Reserved` one usable; the model is therefore sound but
    incomplete for programs that keep reading through a loan after an owner read, and for shared
    (`&`) borrows in general. Applied to every direct read of a local in `assign`, `storeRef`,
    `assert`, and the `switchInt` discriminant (a `ret` read ends execution, so it needs none). -/
def Slot.ownerRead {Val : Type} : Slot Val → Slot Val
  | .live v g true loan => .live v (g + 1) false loan
  | s => s

/-- Apply `Slot.ownerRead` to `loc` in `st`. -/
def CanonState.ownerReadLoc {Val : Type} (st : CanonState Val) (loc : LocalId) : CanonState Val :=
  st.setSlot loc (st.getSlot loc).ownerRead

/-- Apply `CanonState.ownerReadLoc` to all locals directly read by `rv`. -/
def CanonState.ownerReadRvalue {Val : Type} (st : CanonState Val) : MirRvalue → CanonState Val
  | .const _ => st
  | .use src => st.ownerReadLoc src
  | .op1 _ src => st.ownerReadLoc src
  | .op2 _ lhs rhs => (st.ownerReadLoc lhs).ownerReadLoc rhs
  | .derefRef ptr => st.ownerReadLoc ptr

/-- Re-validate the loan held by a pointer slot at generation `g` (used after a write through
    that pointer bumps its target's generation). Non-`live` slots are left unchanged. -/
def Slot.retarget {Val : Type} (target g : Nat) : Slot Val → Slot Val
  | .live pv pg pb _ => .live pv pg pb (some (target, g))
  | s => s

/-- Write-through-reference effect on the state: perform an owner read on `ptr` (invalidating
    any loan to the pointer variable `ptr` itself), set the referent `target` to its new value at
    the bumped generation `g`, then re-validate the writer `ptr`'s own loan at `g`. -/
def CanonState.storeThrough {Val : Type} (st : CanonState Val) (ptr target : LocalId)
    (v : Val) (g : Nat) (targetLoan : Option (LocalId × Nat)) : CanonState Val :=
  let st₁ := (st.ownerReadLoc ptr).setSlot target (.live v g true targetLoan)
  st₁.setSlot ptr ((st₁.getSlot ptr).retarget target g)

/-- Concrete execution of a single `MirStmt`. Returns `none` on any fault, including writes
    to dead locals, storage statements on undeclared locals, and uses of loans invalidated by
    earlier owner reads, owner writes, re-borrows of the same target, writes through another
    loan, or `StorageDead`. -/
def execStmt (st : CanonState Nat) : MirStmt → Option (CanonState Nat)
  | .assign dst rv =>
    match evalConcreteRvalue st rv with
    | none => none
    | some v =>
      let st₀ := st.ownerReadRvalue rv
      match (st₀.getSlot dst).writeVal? v none with
      | none => none
      | some s' => some (st₀.setSlot dst s')
  | .storageLive loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).reborn) else none
  | .storageDead loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).kill) else none
  | .assert cond =>
    match readConcreteScalar st cond with
    | some v => if v != 0 then some (st.ownerReadLoc cond) else none
    | none => none
  | .retagBorrow dst target =>
    match st.getSlot target with
    | .live targetVal g b targetLoan =>
      -- Unique-loan (Stacked Borrows `&mut`) discipline: re-borrowing an already-borrowed
      -- target invalidates every earlier loan to it (generation bump `g ↦ g + 1`); the new
      -- loan is issued at the resulting generation.
      let g' := if b then g + 1 else g
      match ((st.setSlot target (.live targetVal g' true targetLoan)).getSlot dst).writeVal?
          targetVal (some (target, g')) with
      | none => none
      | some s' => some ((st.setSlot target (.live targetVal g' true targetLoan)).setSlot dst s')
    | _ => none
  | .storeRef ptr rv =>
    match evalConcreteRvalue st rv with
    | none => none
    | some v =>
      let st₀ := st.ownerReadRvalue rv
      match st₀.getSlot ptr with
      | .live _ _ _ (some (target, expGen)) =>
        match st₀.getSlot target with
        | .live _ curGen true none =>
          if curGen == expGen then
            some (st₀.storeThrough ptr target v (curGen + 1) none)
          else
            none
        | _ => none
      | _ => none

/-- Concrete execution of a statement list. -/
def execStmts (st : CanonState Nat) : List MirStmt → Option (CanonState Nat)
  | [] => some st
  | stmt :: rest =>
    match execStmt st stmt with
    | some st' => execStmts st' rest
    | none => none

/-- Resolve an N-way `switchTable` discriminator value `v` against `(caseVal, targetBb)` pairs
    (comparing `v` with `wrap64 caseVal`), falling back to `otherwiseBb`. -/
def lookupCfgSwitchTarget (v : Nat) : List (Nat × BlockId) → BlockId → BlockId
  | [], otherwiseBb => otherwiseBb
  | (caseVal, targetBb) :: rest, otherwiseBb =>
    if v == wrap64 caseVal then targetBb else lookupCfgSwitchTarget v rest otherwiseBb

/-- Mask-free concrete operational semantics of a multi-block `MirCfg` with step fuel `fuel`
    (one unit per executed basic block). -/
def execCfg (cfg : MirCfg) : Nat → BlockId → CanonState Nat → ExecOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, bb, st =>
    match cfg.blocks[bb]? with
    | none => .fault
    | some blk =>
      match execStmts st blk.stmts with
      | none => .fault
      | some st₁ =>
        match blk.term with
        | .goto target => execCfg cfg fuel target st₁
        | .switchInt discr thenBb elseBb =>
          match readConcreteScalar st₁ discr with
          | none => .fault
          | some v =>
            -- Reading the discriminant is an owner read (invalidates loans to `discr`).
            let st₂ := st₁.ownerReadLoc discr
            if v != 0 then execCfg cfg fuel thenBb st₂ else execCfg cfg fuel elseBb st₂
        | .switchTable discr cases otherwiseBb =>
          match readConcreteScalar st₁ discr with
          | none => .fault
          | some v =>
            let st₂ := st₁.ownerReadLoc discr
            execCfg cfg fuel (lookupCfgSwitchTarget v cases otherwiseBb) st₂
        | .ret retLoc =>
          match readConcreteScalar st₁ retLoc with
          | some v => .ret v
          | none => .fault
        | .unreachable => .fault

/-- Commutativity of `setSlotAt` with `List.map`. -/
theorem map_setSlotAt {Val₁ Val₂ : Type} (f : Slot Val₁ → Slot Val₂) :
    ∀ (slots : List (Slot Val₁)) (loc : Nat) (s : Slot Val₁),
      (setSlotAt slots loc s).map f = setSlotAt (slots.map f) loc (f s)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, s => by
    simp only [setSlotAt, List.map_cons]
    rw [map_setSlotAt f xs i s]

theorem evalSymCanonState_setSlot (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) (loc : LocalId) (s : Slot SymId) :
    evalSymCanonState tbl env (st.setSlot loc s) =
      (evalSymCanonState tbl env st).setSlot loc (evalSymSlot tbl env s) := by
  dsimp [evalSymCanonState, CanonState.setSlot]
  rw [map_setSlotAt]

theorem evalSymSlot_reborn (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.reborn = (evalSymSlot tbl env s).reborn := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live _ g b _ => cases b <;> rfl

theorem evalSymSlot_kill (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.kill = (evalSymSlot tbl env s).kill := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live _ g b _ => cases b <;> rfl

theorem evalSymSlot_writeVal (tbl : SymTable) (env : SymEnv) (s : Slot SymId)
    (symId : Nat) (loan : Option (LocalId × Nat)) :
    evalSymSlot tbl env (s.writeVal symId loan) =
      (evalSymSlot tbl env s).writeVal (evalSymId tbl env symId) loan := by
  cases s <;> rfl

theorem ValidSymSlots_getSlotAt {bound : Nat} :
    ∀ {slots : List (Slot SymId)} (loc : LocalId),
      ValidSymSlots bound slots →
      ValidSymSlot bound (getSlotAt slots loc)
  | [], _, _ => trivial
  | _ :: _, 0, ⟨hHead, _⟩ => hHead
  | _ :: _, loc + 1, ⟨_, hTail⟩ => ValidSymSlots_getSlotAt loc hTail

theorem ValidSymCanonState.getSlot {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) (loc : LocalId) :
    ValidSymSlot bound (st.getSlot loc) :=
  ValidSymSlots_getSlotAt loc hSt

theorem ValidSymSlots_setSlotAt {bound : Nat} :
    ∀ {slots : List (Slot SymId)} (loc : LocalId) {s : Slot SymId},
      ValidSymSlots bound slots →
      ValidSymSlot bound s →
      ValidSymSlots bound (setSlotAt slots loc s)
  | [], _, _, _, _ => trivial
  | _ :: _, 0, _, ⟨_, hTail⟩, hS => ⟨hS, hTail⟩
  | _ :: _, loc + 1, _, ⟨hHead, hTail⟩, hS =>
    ⟨hHead, ValidSymSlots_setSlotAt loc hTail hS⟩

theorem ValidSymCanonState.setSlot {bound : Nat} {st : CanonState SymId}
    {loc : LocalId} {s : Slot SymId}
    (hSt : ValidSymCanonState bound st) (hS : ValidSymSlot bound s) :
    ValidSymCanonState bound (st.setSlot loc s) :=
  ValidSymSlots_setSlotAt loc hSt hS

theorem map_buildCanonSlotsAux (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) :
    ∀ (mask : List Bool) (offset : Nat),
      (buildCanonSlotsAux st.getSlot offset mask).map (evalSymSlot tbl env) =
        buildCanonSlotsAux (evalSymCanonState tbl env st).getSlot offset mask
  | [], _ => rfl
  | isLive :: restMask, offset => by
    simp only [buildCanonSlotsAux, List.map_cons]
    rw [map_buildCanonSlotsAux tbl env st restMask (offset + 1)]
    rw [evalSymCanonState_getSlot]
    cases isLive with
    | true => rfl
    | false =>
      dsimp [normalizeSlotForMask]
      rw [evalSymSlot_kill]

theorem evalSymCanonState_canonicalizeCanon (tbl : SymTable) (env : SymEnv)
    (liveMask : List Bool) (st : CanonState SymId) :
    evalSymCanonState tbl env (canonicalizeCanon liveMask st) =
      canonicalizeCanon liveMask (evalSymCanonState tbl env st) := by
  unfold canonicalizeCanon
  dsimp [evalSymCanonState]
  rw [map_buildCanonSlotsAux tbl env st liveMask 0]
  rfl

theorem ValidSymSlots_buildCanonSlotsAux {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) :
    ∀ (mask : List Bool) (offset : Nat),
      ValidSymSlots bound (buildCanonSlotsAux st.getSlot offset mask)
  | [], _ => trivial
  | isLive :: restMask, offset => by
    dsimp [buildCanonSlotsAux]
    refine ⟨?_, ValidSymSlots_buildCanonSlotsAux hSt restMask (offset + 1)⟩
    cases isLive with
    | true => exact hSt.getSlot offset
    | false => trivial

theorem ValidSymCanonState.canonicalizeCanon {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) (liveMask : List Bool) :
    ValidSymCanonState bound (canonicalizeCanon liveMask st) :=
  ValidSymSlots_buildCanonSlotsAux hSt liveMask 0

/-- Read a live symbolic `SymId` from `st` at `loc` (a slot holding a loan is not a scalar; see
    `readConcreteScalar`). -/
def readSymScalar (st : CanonState SymId) (loc : LocalId) : Option Nat :=
  match st.getSlot loc with
  | .live symId _ _ none => some symId
  | _ => none

theorem readSymScalar_spec {tbl : SymTable} {st : CanonState SymId} {loc : LocalId}
    (env : SymEnv) (hSt : ValidSymCanonState tbl.nodes.length st) :
    match readSymScalar st loc with
    | none => readConcreteScalar (evalSymCanonState tbl env st) loc = none
    | some symId =>
      symId < tbl.nodes.length ∧
        readConcreteScalar (evalSymCanonState tbl env st) loc =
          some (evalSymId tbl env symId) := by
  have hSlot := hSt.getSlot loc
  dsimp [readSymScalar, readConcreteScalar]
  rw [evalSymCanonState_getSlot]
  cases hGet : st.getSlot loc with
  | dead g => rfl
  | uninit g => rfl
  | live symId g b loan =>
    rw [hGet] at hSlot
    cases loan with
    | none => exact ⟨hSlot, rfl⟩
    | some _ => rfl

/-- Symbolic GVN evaluation of a `MirRvalue` in `(st, tbl)`.
    Interns constants and unary/binary expressions into `tbl`, and verifies borrow
    liveness and generation agreement `(curGen == expGen)` on `.derefRef ptr`. -/
def evalSymRvalue (st : CanonState SymId) (tbl : SymTable) :
    MirRvalue → Option (Nat × SymTable)
  | .const v => some (internNode tbl (.const v))
  | .use src =>
    match readSymScalar st src with
    | some symId => some (symId, tbl)
    | none => none
  | .op1 op src =>
    match readSymScalar st src with
    | some srcId => some (internNode tbl (.op1 op srcId))
    | none => none
  | .op2 op lhs rhs =>
    match readSymScalar st lhs, readSymScalar st rhs with
    | some lhsId, some rhsId => some (internNode tbl (.op2 op lhsId rhsId))
    | _, _ => none
  | .derefRef ptr =>
    match st.getSlot ptr with
    | .live _ _ _ (some (target, expGen)) =>
      match st.getSlot target with
      | .live targetSymId curGen true none =>
        if curGen == expGen then some (targetSymId, tbl) else none
      | _ => none
    | _ => none

theorem evalSymRvalue_sound {st : CanonState SymId} {tbl : SymTable}
    {rv : MirRvalue} {resId : Nat} {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hEval : evalSymRvalue st tbl rv = some (resId, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      resId < tbl'.nodes.length ∧
      ∀ env : SymEnv,
        evalConcreteRvalue (evalSymCanonState tbl env st) rv =
          some (evalSymId tbl' env resId) := by
  cases rv with
  | const v =>
    dsimp [evalSymRvalue] at hEval
    injection hEval with hPair
    have hId : resId = (internNode tbl (.const v)).1 := by rw [hPair]
    have hTbl : tbl' = (internNode tbl (.const v)).2 := by rw [hPair]
    subst hId hTbl
    have hNode : ValidNode tbl.nodes.length (.const v) := trivial
    have hV := internNode_valid hValid hNode
    have hE := internNode_extends tbl (.const v)
    refine ⟨hV.1, hE, hV.2, ?_⟩
    intro env
    dsimp [evalConcreteRvalue]
    have hEv := internNode_eval hValid hNode env
    rw [hEv]
    rfl
  | use src =>
    dsimp [evalSymRvalue] at hEval
    cases hRead : readSymScalar st src with
    | none =>
      rw [hRead] at hEval
      cases hEval
    | some symId =>
      rw [hRead] at hEval
      injection hEval with hPair
      injection hPair with hId hTbl
      subst hId hTbl
      refine ⟨hValid, SymTable.Extends.refl tbl, ?_, ?_⟩
      · have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := src)
        rw [hRead] at hSpec
        exact hSpec.1
      · intro env
        have hSpec := readSymScalar_spec env hSt (loc := src)
        rw [hRead] at hSpec
        dsimp [evalConcreteRvalue]
        exact hSpec.2
  | op1 op src =>
    dsimp [evalSymRvalue] at hEval
    cases hRead : readSymScalar st src with
    | none =>
      rw [hRead] at hEval
      cases hEval
    | some srcId =>
      rw [hRead] at hEval
      injection hEval with hPair
      have hId : resId = (internNode tbl (.op1 op srcId)).1 := by rw [hPair]
      have hTbl : tbl' = (internNode tbl (.op1 op srcId)).2 := by rw [hPair]
      subst hId hTbl
      have hSrcLt : srcId < tbl.nodes.length := by
        have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := src)
        rw [hRead] at hSpec
        exact hSpec.1
      have hNode : ValidNode tbl.nodes.length (.op1 op srcId) := hSrcLt
      have hV := internNode_valid hValid hNode
      have hE := internNode_extends tbl (.op1 op srcId)
      refine ⟨hV.1, hE, hV.2, ?_⟩
      intro env
      have hSpec := readSymScalar_spec env hSt (loc := src)
      rw [hRead] at hSpec
      dsimp [evalConcreteRvalue]
      rw [hSpec.2]
      have hEv := internNode_eval hValid hNode env
      rw [hEv]
      rfl
  | op2 op lhs rhs =>
    dsimp [evalSymRvalue] at hEval
    cases hL : readSymScalar st lhs with
    | none =>
      rw [hL] at hEval
      cases hEval
    | some lhsId =>
      rw [hL] at hEval
      cases hR : readSymScalar st rhs with
      | none =>
        rw [hR] at hEval
        cases hEval
      | some rhsId =>
        rw [hR] at hEval
        injection hEval with hPair
        have hId : resId = (internNode tbl (.op2 op lhsId rhsId)).1 := by rw [hPair]
        have hTbl : tbl' = (internNode tbl (.op2 op lhsId rhsId)).2 := by rw [hPair]
        subst hId hTbl
        have hLhsLt : lhsId < tbl.nodes.length := by
          have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := lhs)
          rw [hL] at hSpec
          exact hSpec.1
        have hRhsLt : rhsId < tbl.nodes.length := by
          have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := rhs)
          rw [hR] at hSpec
          exact hSpec.1
        have hNode : ValidNode tbl.nodes.length (.op2 op lhsId rhsId) := ⟨hLhsLt, hRhsLt⟩
        have hV := internNode_valid hValid hNode
        have hE := internNode_extends tbl (.op2 op lhsId rhsId)
        refine ⟨hV.1, hE, hV.2, ?_⟩
        intro env
        have hSpecL := readSymScalar_spec env hSt (loc := lhs)
        have hSpecR := readSymScalar_spec env hSt (loc := rhs)
        rw [hL] at hSpecL
        rw [hR] at hSpecR
        dsimp [evalConcreteRvalue]
        rw [hSpecL.2, hSpecR.2]
        have hEv := internNode_eval hValid hNode env
        rw [hEv]
        rfl
  | derefRef ptr =>
    dsimp [evalSymRvalue] at hEval
    cases hPtr : st.getSlot ptr with
    | dead _ => rw [hPtr] at hEval; cases hEval
    | uninit _ => rw [hPtr] at hEval; cases hEval
    | live ptrId ptrG ptrB ptrLoan =>
      rw [hPtr] at hEval
      cases ptrLoan with
      | none => cases hEval
      | some pair =>
        rcases pair with ⟨target, expGen⟩
        dsimp at hEval
        cases hTgt : st.getSlot target with
        | dead _ => rw [hTgt] at hEval; cases hEval
        | uninit _ => rw [hTgt] at hEval; cases hEval
        | live targetSymId curGen targetB targetLoan =>
          rw [hTgt] at hEval
          cases targetB with
          | false => cases hEval
          | true =>
            cases targetLoan with
            | some _ => cases hEval
            | none =>
              dsimp at hEval
              split at hEval
              · rename_i hGenEq
                injection hEval with hPair
                injection hPair with hId hTbl
                subst hId hTbl
                have hTgtSlot := hSt.getSlot target
                rw [hTgt] at hTgtSlot
                refine ⟨hValid, SymTable.Extends.refl tbl, hTgtSlot, ?_⟩
                intro env
                dsimp [evalConcreteRvalue]
                rw [evalSymCanonState_getSlot, hPtr]
                dsimp [evalSymSlot]
                rw [evalSymCanonState_getSlot, hTgt]
                dsimp [evalSymSlot]
                rw [hGenEq]
                rfl
              · cases hEval

/-- Active branch path condition `Option (SymId × Bool)`:
    - `none`: no active branch assumption,
    - `(brId, true)`: inside a `then` or `caseVal =>` arm where `(evalSymId tbl env brId != 0) = true`,
    - `(brId, false)`: inside an `else` or post-case/`otherwise` arm where
      `(evalSymId tbl env brId != 0) = false`.
    Represented as a conjunctive stack `List (SymId × Bool)` so nested branches conjoin with outer
    branch conditions and `switchTable` `otherwise` (and subsequent case) arms accumulate negated
    prior-case conditions `!(discr == caseVal)`. -/
abbrev PathCond := List (SymId × Bool)

/-- Well-formedness of a conjunctive `PathCond` against a table size `bound`. -/
def PathCondValid (bound : Nat) : PathCond → Prop
  | [] => True
  | (brId, _) :: rest => brId < bound ∧ PathCondValid bound rest

theorem PathCondValid.mono {b₁ b₂ : Nat} :
    ∀ {pc : PathCond}, PathCondValid b₁ pc → b₁ ≤ b₂ → PathCondValid b₂ pc
  | [], _, _ => trivial
  | _ :: _, ⟨hHead, hTail⟩, hLe => ⟨Nat.lt_of_lt_of_le hHead hLe, hTail.mono hLe⟩

/-- Semantic meaning of a conjunctive `pc : PathCond` in `(tbl, env)`. -/
def PathCondHolds (tbl : SymTable) (env : SymEnv) : PathCond → Prop
  | [] => True
  | (brId, polarity) :: rest =>
    (evalSymId tbl env brId != 0) = polarity ∧ PathCondHolds tbl env rest

theorem PathCondHolds.mono {tbl tbl' : SymTable} {env : SymEnv}
    (hValid : ValidTable tbl) (hExt : tbl.Extends tbl') :
    ∀ {pc : PathCond},
      PathCondValid tbl.nodes.length pc →
      PathCondHolds tbl env pc →
      PathCondHolds tbl' env pc
  | [], _, _ => trivial
  | (brId, pol) :: rest, ⟨hBr, hRestValid⟩, ⟨hHead, hTail⟩ => by
    refine ⟨?_, PathCondHolds.mono hValid hExt hRestValid hTail⟩
    show (evalSymId tbl' env brId != 0) = pol
    rw [← evalSymId_mono hValid hExt env hBr]
    exact hHead

/-- Sound GVN-backed non-zero condition recognizer for `MirStmt.assert`:
    recognizes non-zero constants (`.const v` with `v != 0`), negated zero constants
    (`.op1 .boolNot argId` where `argId` is `.const v` with `wrap64 v == 0`, e.g.,
    `!(x < x)`, `!(x - x)`, `!(x ^ x)` after `peepholeOp2`), as well as reflexive
    GVN equality/inequality nodes (`.op2 .eq a b` or `.op2 .le a b` where `a == b`). -/
def isProvablyNonZero (tbl : SymTable) (condId : Nat) : Bool :=
  match tbl.nodes[condId]? with
  | some (.const v) => wrap64 v != 0
  | some (.op1 .boolNot argId) =>
    match tbl.nodes[argId]? with
    | some (.const v) => wrap64 v == 0
    | _ => false
  | some (.op2 .eq a b) => a == b
  | some (.op2 .le a b) => a == b
  | _ => false

/-- Check whether a single branch literal `(brId, polarity)` entails `(evalSymId tbl env condId != 0)`:
    - For `(brId, true)`, `condId == brId` is provably non-zero.
    - For `(brId, false)`, any `condId` interned as `.op1 .boolNot argId` with `argId == brId` is
      provably non-zero (`1`). -/
def isProvablyNonZeroLit (tbl : SymTable) (brId : SymId) (polarity : Bool) (condId : Nat) : Bool :=
  match polarity with
  | true => condId == brId
  | false =>
    match tbl.nodes[condId]? with
    | some (.op1 .boolNot argId) => argId == brId
    | _ => false

/-- Check whether any literal in the conjunctive `pc : PathCond` entails `(evalSymId tbl env condId != 0)`. -/
def isProvablyNonZeroLits (tbl : SymTable) : PathCond → Nat → Bool
  | [], _ => false
  | (brId, polarity) :: rest, condId =>
    if isProvablyNonZeroLit tbl brId polarity condId then true
    else isProvablyNonZeroLits tbl rest condId

/-- Branch-condition-aware non-zero recognizer (`isProvablyNonZeroUnder`):
    extends `isProvablyNonZero` with path-sensitive discharge under the active conjunctive branch
    condition stack `pc : PathCond`. -/
def isProvablyNonZeroUnder (tbl : SymTable) (pc : PathCond) (condId : Nat) : Bool :=
  if isProvablyNonZero tbl condId then
    true
  else
    isProvablyNonZeroLits tbl pc condId

theorem isProvablyNonZero_sound {tbl : SymTable} {condId : Nat}
    (hValid : ValidTable tbl) (hOk : isProvablyNonZero tbl condId = true)
    (env : SymEnv) :
    (evalSymId tbl env condId != 0) = true := by
  dsimp [isProvablyNonZero] at hOk
  cases hLookup : tbl.nodes[condId]? with
  | none =>
    rw [hLookup] at hOk
    cases hOk
  | some node =>
    rw [hLookup] at hOk
    have hEval := evalSymId_eq_evalSymNodeWith hValid env hLookup
    cases node with
    | const v =>
      dsimp at hOk
      rw [hEval]
      dsimp [evalSymNodeWith]
      exact hOk
    | var _ =>
      dsimp at hOk
      cases hOk
    | op1 op argId =>
      cases op <;> dsimp at hOk <;> try cases hOk
      cases hArg : tbl.nodes[argId]? with
      | none => rw [hArg] at hOk; cases hOk
      | some argNode =>
        rw [hArg] at hOk
        cases argNode with
        | const v =>
          dsimp at hOk
          have hEvalArg := evalSymId_eq_evalSymNodeWith hValid env hArg
          rw [hEval]
          dsimp [evalSymNodeWith]
          rw [hEvalArg]
          dsimp [evalSymNodeWith, evalSymOp1]
          rw [hOk]
          rfl
        | var _ => cases hOk
        | op1 _ _ => cases hOk
        | op2 _ _ _ => cases hOk
        | ite _ _ _ => cases hOk
    | ite _ _ _ =>
      dsimp at hOk
      cases hOk
    | op2 op a b =>
      cases op <;> dsimp at hOk <;> try cases hOk
      · have hab : a = b := of_decide_eq_true hOk
        subst hab
        rw [hEval]
        dsimp [evalSymNodeWith, evalSymOp2]
        have hRefl : (evalSymId tbl env a == evalSymId tbl env a) = true :=
          decide_eq_true rfl
        rw [hRefl]
        rfl
      · have hab : a = b := of_decide_eq_true hOk
        subst hab
        rw [hEval]
        dsimp [evalSymNodeWith, evalSymOp2]
        have hRefl : decide (evalSymId tbl env a ≤ evalSymId tbl env a) = true :=
          decide_eq_true (Nat.le_refl _)
        rw [hRefl]
        rfl

theorem isProvablyNonZeroLit_sound {tbl : SymTable} {brId : SymId} {pol : Bool} {condId : Nat}
    {env : SymEnv} (hValid : ValidTable tbl)
    (hLit : (evalSymId tbl env brId != 0) = pol)
    (hOk : isProvablyNonZeroLit tbl brId pol condId = true) :
    (evalSymId tbl env condId != 0) = true := by
  cases pol with
  | true =>
    dsimp [isProvablyNonZeroLit] at hOk
    have hEq : condId = brId := of_decide_eq_true hOk
    subst hEq
    exact hLit
  | false =>
    dsimp [isProvablyNonZeroLit] at hOk
    cases hLookup : tbl.nodes[condId]? with
    | none => rw [hLookup] at hOk; cases hOk
    | some node =>
      rw [hLookup] at hOk
      have hEval := evalSymId_eq_evalSymNodeWith hValid env hLookup
      cases node with
      | const _ => cases hOk
      | var _ => cases hOk
      | op2 _ _ _ => cases hOk
      | ite _ _ _ => cases hOk
      | op1 op argId =>
        cases op <;> dsimp at hOk <;> try cases hOk
        have hArgEq : argId = brId := of_decide_eq_true hOk
        subst hArgEq
        rw [hEval]
        dsimp [evalSymNodeWith, evalSymOp1]
        have hZero : evalSymId tbl env argId = 0 := bne_eq_false_iff_eq.1 hLit
        rw [hZero]
        rfl

theorem isProvablyNonZeroLits_sound {tbl : SymTable} {condId : Nat} {env : SymEnv}
    (hValid : ValidTable tbl) :
    ∀ {pc : PathCond},
      PathCondHolds tbl env pc →
      isProvablyNonZeroLits tbl pc condId = true →
      (evalSymId tbl env condId != 0) = true
  | [], _, hOk => by cases hOk
  | (brId, pol) :: rest, ⟨hHead, hTail⟩, hOk => by
    dsimp [isProvablyNonZeroLits] at hOk
    cases hLit : isProvablyNonZeroLit tbl brId pol condId with
    | true => exact isProvablyNonZeroLit_sound hValid hHead hLit
    | false =>
      rw [hLit] at hOk
      exact isProvablyNonZeroLits_sound hValid hTail hOk

/-- **Path-Sensitive Assertion Soundness (`isProvablyNonZeroUnder_sound`)**:
    Whenever `PathCondHolds tbl env pc` holds, `isProvablyNonZeroUnder tbl pc condId = true`
    guarantees `(evalSymId tbl env condId != 0) = true`. -/
theorem isProvablyNonZeroUnder_sound {tbl : SymTable} {pc : PathCond} {condId : Nat}
    {env : SymEnv} (hValid : ValidTable tbl) (hPc : PathCondHolds tbl env pc)
    (hOk : isProvablyNonZeroUnder tbl pc condId = true) :
    (evalSymId tbl env condId != 0) = true := by
  dsimp [isProvablyNonZeroUnder] at hOk
  cases hBase : isProvablyNonZero tbl condId with
  | true => exact isProvablyNonZero_sound hValid hBase env
  | false =>
    rw [hBase] at hOk
    exact isProvablyNonZeroLits_sound hValid hPc hOk

theorem evalSymSlot_writeVal? (tbl : SymTable) (env : SymEnv) (s : Slot SymId)
    (symId : Nat) (loan : Option (LocalId × Nat)) :
    (s.writeVal? symId loan).map (evalSymSlot tbl env) =
      (evalSymSlot tbl env s).writeVal? (evalSymId tbl env symId) loan := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem ValidSymSlot.writeVal? {bound : Nat} {s s' : Slot SymId} {symId : Nat}
    {loan : Option (LocalId × Nat)} (hW : s.writeVal? symId loan = some s')
    (hId : symId < bound) : ValidSymSlot bound s' := by
  cases s with
  | dead _ => cases hW
  | uninit _ =>
    injection hW with h
    subst h
    exact hId
  | live _ _ b _ =>
    cases b <;> (injection hW with h; subst h; exact hId)

theorem evalSymCanonState_length (tbl : SymTable) (env : SymEnv) (st : CanonState SymId) :
    (evalSymCanonState tbl env st).slots.length = st.slots.length := by
  simp [evalSymCanonState]

theorem evalSymSlot_ownerRead (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.ownerRead = (evalSymSlot tbl env s).ownerRead := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem ValidSymSlot.ownerRead {bound : Nat} {s : Slot SymId} (h : ValidSymSlot bound s) :
    ValidSymSlot bound s.ownerRead := by
  cases s with
  | dead _ => trivial
  | uninit _ => trivial
  | live _ _ b _ => cases b <;> exact h

theorem evalSymCanonState_ownerReadLoc (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (loc : LocalId) :
    evalSymCanonState tbl env (st.ownerReadLoc loc) =
      (evalSymCanonState tbl env st).ownerReadLoc loc := by
  dsimp only [CanonState.ownerReadLoc]
  rw [evalSymCanonState_setSlot, evalSymSlot_ownerRead, evalSymCanonState_getSlot]

theorem ValidSymCanonState.ownerReadLoc {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (loc : LocalId) :
    ValidSymCanonState bound (st.ownerReadLoc loc) :=
  h.setSlot (h.getSlot loc).ownerRead

theorem evalSymCanonState_ownerReadRvalue (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (rv : MirRvalue) :
    evalSymCanonState tbl env (st.ownerReadRvalue rv) =
      (evalSymCanonState tbl env st).ownerReadRvalue rv := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue] <;>
    repeat rw [evalSymCanonState_ownerReadLoc]

theorem ValidSymCanonState.ownerReadRvalue {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (rv : MirRvalue) :
    ValidSymCanonState bound (st.ownerReadRvalue rv) := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue]
  · exact h
  · exact h.ownerReadLoc _
  · exact h.ownerReadLoc _
  · exact (h.ownerReadLoc _).ownerReadLoc _
  · exact h.ownerReadLoc _

theorem evalSymSlot_retarget (tbl : SymTable) (env : SymEnv) (target g : Nat) (s : Slot SymId) :
    evalSymSlot tbl env (s.retarget target g) = (evalSymSlot tbl env s).retarget target g := by
  cases s <;> rfl

theorem ValidSymSlot.retarget {bound : Nat} {s : Slot SymId} (h : ValidSymSlot bound s)
    (target g : Nat) : ValidSymSlot bound (s.retarget target g) := by
  cases s <;> exact h

theorem evalSymCanonState_storeThrough (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (ptr target : LocalId) (symId : SymId) (g : Nat) (loan : Option (LocalId × Nat)) :
    evalSymCanonState tbl env (st.storeThrough ptr target symId g loan) =
      (evalSymCanonState tbl env st).storeThrough ptr target (evalSymId tbl env symId) g loan := by
  dsimp only [CanonState.storeThrough]
  rw [evalSymCanonState_setSlot, evalSymSlot_retarget, ← evalSymCanonState_getSlot,
    evalSymCanonState_setSlot, evalSymCanonState_ownerReadLoc]
  rfl

theorem ValidSymCanonState.storeThrough {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) {ptr target : LocalId} {symId : SymId}
    (hId : symId < bound) (g : Nat) (loan : Option (LocalId × Nat)) :
    ValidSymCanonState bound (st.storeThrough ptr target symId g loan) := by
  dsimp only [CanonState.storeThrough]
  have h₁ : ValidSymCanonState bound
      ((st.ownerReadLoc ptr).setSlot target (.live symId g true loan)) :=
    (h.ownerReadLoc ptr).setSlot hId
  exact h₁.setSlot ((h₁.getSlot ptr).retarget target g)

/-- Symbolic execution of a single `MirStmt` in `(st, tbl)` under optional branch path
    condition `pc` (mirrors `execStmt`'s faults, including `.storeRef` temporal borrow checks
    and owner-read loan invalidation). -/
def symExecStmt (st : CanonState SymId) (tbl : SymTable)
    (stmt : MirStmt) (pc : PathCond := []) : Option (CanonState SymId × SymTable) :=
  match stmt with
  | .assign dst rv =>
    match evalSymRvalue st tbl rv with
    | none => none
    | some (symId, tbl') =>
      let st₀ := st.ownerReadRvalue rv
      match (st₀.getSlot dst).writeVal? symId none with
      | none => none
      | some s' => some (st₀.setSlot dst s', tbl')
  | .storageLive loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).reborn, tbl) else none
  | .storageDead loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).kill, tbl) else none
  | .assert cond =>
    match readSymScalar st cond with
    | some condId =>
      if isProvablyNonZeroUnder tbl pc condId then some (st.ownerReadLoc cond, tbl) else none
    | none => none
  | .retagBorrow dst target =>
    match st.getSlot target with
    | .live targetSymId g b targetLoan =>
      let g' := if b then g + 1 else g
      match ((st.setSlot target (.live targetSymId g' true targetLoan)).getSlot dst).writeVal?
          targetSymId (some (target, g')) with
      | none => none
      | some s' =>
        some ((st.setSlot target (.live targetSymId g' true targetLoan)).setSlot dst s', tbl)
    | _ => none
  | .storeRef ptr rv =>
    match evalSymRvalue st tbl rv with
    | none => none
    | some (symId, tbl') =>
      let st₀ := st.ownerReadRvalue rv
      match st₀.getSlot ptr with
      | .live _ _ _ (some (target, expGen)) =>
        match st₀.getSlot target with
        | .live _ curGen true none =>
          if curGen == expGen then
            some (st₀.storeThrough ptr target symId (curGen + 1) none, tbl')
          else
            none
        | _ => none
      | _ => none

/-- **Path-Sensitive Single-Statement Simulation (`symExecStmt_under_sound`)**: a successful
    symbolic step under path condition `pc` is matched, under every `env` satisfying
    `PathCondHolds tbl env pc`, by the identical concrete step on the evaluated state. -/
theorem symExecStmt_under_sound {st st' : CanonState SymId} {tbl tbl' : SymTable}
    {stmt : MirStmt} {pc : PathCond}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmt st tbl stmt pc = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        PathCondHolds tbl env pc →
        execStmt (evalSymCanonState tbl env st) stmt =
          some (evalSymCanonState tbl' env st') := by
  cases stmt with
  | assign dst rv =>
    dsimp only [symExecStmt] at hExec
    cases hRv : evalSymRvalue st tbl rv with
    | none =>
      rw [hRv] at hExec
      cases hExec
    | some pair =>
      rcases pair with ⟨symId, tbl₁⟩
      rw [hRv] at hExec
      dsimp only at hExec
      cases hW : ((st.ownerReadRvalue rv).getSlot dst).writeVal? symId none with
      | none =>
        rw [hW] at hExec
        cases hExec
      | some s' =>
        rw [hW] at hExec
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        rcases evalSymRvalue_sound hValid hSt hRv with ⟨hValid₁, hExt₁, hSymIdLt, hEvalRv⟩
        have hLenLe : tbl.nodes.length ≤ tbl₁.nodes.length := hExt₁.length_le
        have hSt₁ : ValidSymCanonState tbl₁.nodes.length (st.ownerReadRvalue rv) :=
          ValidSymSlots.mono (hSt.ownerReadRvalue rv) hLenLe
        refine ⟨hValid₁, hExt₁, hSt₁.setSlot (ValidSymSlot.writeVal? hW hSymIdLt), ?_⟩
        intro env _
        dsimp only [execStmt]
        rw [hEvalRv env]
        dsimp only
        rw [evalSymCanonState_mono hValid hExt₁ env hSt, ← evalSymCanonState_ownerReadRvalue,
          evalSymCanonState_getSlot, ← evalSymSlot_writeVal?, hW]
        dsimp only [Option.map]
        rw [evalSymCanonState_setSlot]
  | storageLive loc =>
    dsimp only [symExecStmt] at hExec
    split at hExec
    · rename_i hLt
      injection hExec with hPair
      injection hPair with hSt' hTbl'
      subst hSt' hTbl'
      refine ⟨hValid, SymTable.Extends.refl tbl, hSt.setSlot trivial, ?_⟩
      intro env _
      dsimp only [execStmt]
      rw [evalSymCanonState_length, ite_eq_left hLt, evalSymCanonState_setSlot,
        evalSymCanonState_getSlot, evalSymSlot_reborn]
    · cases hExec
  | storageDead loc =>
    dsimp only [symExecStmt] at hExec
    split at hExec
    · rename_i hLt
      injection hExec with hPair
      injection hPair with hSt' hTbl'
      subst hSt' hTbl'
      refine ⟨hValid, SymTable.Extends.refl tbl, hSt.setSlot trivial, ?_⟩
      intro env _
      dsimp only [execStmt]
      rw [evalSymCanonState_length, ite_eq_left hLt, evalSymCanonState_setSlot,
        evalSymCanonState_getSlot, evalSymSlot_kill]
    · cases hExec
  | assert cond =>
    dsimp only [symExecStmt] at hExec
    cases hRead : readSymScalar st cond with
    | none =>
      rw [hRead] at hExec
      cases hExec
    | some condId =>
      rw [hRead] at hExec
      dsimp only at hExec
      split at hExec
      · rename_i hNz
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        refine ⟨hValid, SymTable.Extends.refl tbl, hSt.ownerReadLoc cond, ?_⟩
        intro env hPc
        have hSpec := readSymScalar_spec env hSt (loc := cond)
        rw [hRead] at hSpec
        dsimp only [execStmt]
        rw [hSpec.2]
        dsimp only
        rw [isProvablyNonZeroUnder_sound hValid hPc hNz, evalSymCanonState_ownerReadLoc]
        rfl
      · cases hExec
  | retagBorrow dst target =>
    dsimp only [symExecStmt] at hExec
    cases hTgt : st.getSlot target with
    | dead _ => rw [hTgt] at hExec; cases hExec
    | uninit _ => rw [hTgt] at hExec; cases hExec
    | live targetSymId g targetB targetLoan =>
      rw [hTgt] at hExec
      dsimp only at hExec
      generalize hg' : (if targetB = true then g + 1 else g) = g' at hExec
      cases hW : ((st.setSlot target (.live targetSymId g' true targetLoan)).getSlot dst).writeVal?
          targetSymId (some (target, g')) with
      | none =>
        rw [hW] at hExec
        cases hExec
      | some s' =>
        rw [hW] at hExec
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        have hTgtValid : targetSymId < tbl.nodes.length := by
          have hSlot := hSt.getSlot target
          rw [hTgt] at hSlot
          exact hSlot
        have hSt₁ := hSt.setSlot (loc := target) (s := .live targetSymId g' true targetLoan)
          hTgtValid
        refine ⟨hValid, SymTable.Extends.refl tbl,
          hSt₁.setSlot (ValidSymSlot.writeVal? hW hTgtValid), ?_⟩
        intro env _
        have hSetEq : (evalSymCanonState tbl env st).setSlot target
            (.live (evalSymId tbl env targetSymId) g' true targetLoan) =
            evalSymCanonState tbl env (st.setSlot target (.live targetSymId g' true targetLoan)) :=
          (evalSymCanonState_setSlot tbl env st target (.live targetSymId g' true targetLoan)).symm
        dsimp only [execStmt]
        rw [evalSymCanonState_getSlot, hTgt]
        dsimp only [evalSymSlot]
        rw [hg', hSetEq, evalSymCanonState_getSlot, ← evalSymSlot_writeVal?, hW]
        dsimp only [Option.map]
        exact congrArg some (evalSymCanonState_setSlot tbl env _ dst s').symm
  | storeRef ptr rv =>
    dsimp only [symExecStmt] at hExec
    cases hRv : evalSymRvalue st tbl rv with
    | none => rw [hRv] at hExec; cases hExec
    | some pair =>
      rcases pair with ⟨symId, tbl₁⟩
      rw [hRv] at hExec
      dsimp only at hExec
      cases hPtr : (st.ownerReadRvalue rv).getSlot ptr with
      | dead _ => rw [hPtr] at hExec; cases hExec
      | uninit _ => rw [hPtr] at hExec; cases hExec
      | live ptrId ptrG ptrB ptrLoan =>
        rw [hPtr] at hExec
        cases ptrLoan with
        | none => cases hExec
        | some lPair =>
          rcases lPair with ⟨target, expGen⟩
          dsimp only at hExec
          cases hTgt : (st.ownerReadRvalue rv).getSlot target with
          | dead _ => rw [hTgt] at hExec; cases hExec
          | uninit _ => rw [hTgt] at hExec; cases hExec
          | live targetSymId curGen targetB targetLoan =>
            rw [hTgt] at hExec
            cases targetB with
            | false => cases hExec
            | true =>
              cases targetLoan with
              | some _ => cases hExec
              | none =>
                dsimp only at hExec
                split at hExec
                · rename_i hGenEq
                  injection hExec with hPair
                  injection hPair with hSt' hTbl'
                  subst hSt' hTbl'
                  rcases evalSymRvalue_sound hValid hSt hRv with
                    ⟨hValid₁, hExt₁, hSymIdLt, hEvalRv⟩
                  have hSt₁ : ValidSymCanonState tbl₁.nodes.length (st.ownerReadRvalue rv) :=
                    ValidSymSlots.mono (hSt.ownerReadRvalue rv) hExt₁.length_le
                  refine ⟨hValid₁, hExt₁, hSt₁.storeThrough hSymIdLt (curGen + 1) none, ?_⟩
                  intro env _
                  dsimp only [execStmt]
                  rw [hEvalRv env]
                  dsimp only
                  rw [← evalSymCanonState_ownerReadRvalue, evalSymCanonState_getSlot, hPtr]
                  dsimp only [evalSymSlot]
                  rw [evalSymCanonState_getSlot, hTgt]
                  dsimp only [evalSymSlot]
                  rw [ite_eq_left hGenEq, evalSymCanonState_storeThrough,
                    evalSymCanonState_mono hValid hExt₁ env (hSt.ownerReadRvalue rv)]
                · cases hExec

/-- **Exact single-statement simulation (`symExecStmt_sound`)** for `pc = none`. -/
theorem symExecStmt_sound {st st' : CanonState SymId} {tbl tbl' : SymTable}
    {stmt : MirStmt}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmt st tbl stmt = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        execStmt (evalSymCanonState tbl env st) stmt =
          some (evalSymCanonState tbl' env st') := by
  rcases symExecStmt_under_sound hValid hSt hExec with ⟨hV, hE, hS, hEv⟩
  exact ⟨hV, hE, hS, fun env => hEv env trivial⟩

/-- Symbolic execution of a list of `MirStmt`s in `(st, tbl)` under optional branch path
    condition `pc`. -/
def symExecStmts (st : CanonState SymId) (tbl : SymTable) :
    List MirStmt → (pc : PathCond := []) → Option (CanonState SymId × SymTable)
  | [], _ => some (st, tbl)
  | stmt :: rest, pc =>
    match symExecStmt st tbl stmt pc with
    | some (st₁, tbl₁) => symExecStmts st₁ tbl₁ rest pc
    | none => none

theorem symExecStmts_under_sound :
    ∀ (stmts : List MirStmt) {st st' : CanonState SymId} {tbl tbl' : SymTable} {pc : PathCond},
      ValidTable tbl →
      ValidSymCanonState tbl.nodes.length st →
      symExecStmts st tbl stmts pc = some (st', tbl') →
      PathCondValid tbl.nodes.length pc →
      ValidTable tbl' ∧
        tbl.Extends tbl' ∧
        ValidSymCanonState tbl'.nodes.length st' ∧
        ∀ env : SymEnv,
          PathCondHolds tbl env pc →
          execStmts (evalSymCanonState tbl env st) stmts =
            some (evalSymCanonState tbl' env st')
  | [], _, _, tbl, _, _, hValid, hSt, hExec, _ => by
    dsimp [symExecStmts] at hExec
    injection hExec with hPair
    injection hPair with hSt' hTbl'
    subst hSt' hTbl'
    exact ⟨hValid, SymTable.Extends.refl tbl, hSt, fun _ _ => rfl⟩
  | stmt :: rest, st, st', tbl, tbl', pc, hValid, hSt, hExec, hPcValid => by
    dsimp [symExecStmts] at hExec
    cases hStep₁ : symExecStmt st tbl stmt pc with
    | none =>
      rw [hStep₁] at hExec
      cases hExec
    | some pair₁ =>
      rcases pair₁ with ⟨st₁, tbl₁⟩
      rw [hStep₁] at hExec
      rcases symExecStmt_under_sound hValid hSt hStep₁ with ⟨hValid₁, hExt₁, hSt₁, hEval₁⟩
      have hPcValid₁ : PathCondValid tbl₁.nodes.length pc := hPcValid.mono hExt₁.length_le
      rcases symExecStmts_under_sound rest hValid₁ hSt₁ hExec hPcValid₁ with
        ⟨hValid₂, hExt₂, hSt₂, hEval₂⟩
      refine ⟨hValid₂, hExt₁.trans hExt₂, hSt₂, ?_⟩
      intro env hPc
      dsimp [execStmts]
      rw [hEval₁ env hPc]
      exact hEval₂ env (PathCondHolds.mono hValid hExt₁ hPcValid hPc)

theorem symExecStmts_sound
    (stmts : List MirStmt) {st st' : CanonState SymId} {tbl tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmts st tbl stmts = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        execStmts (evalSymCanonState tbl env st) stmts =
          some (evalSymCanonState tbl' env st') := by
  rcases symExecStmts_under_sound stmts hValid hSt hExec trivial with ⟨hV, hE, hS, hEv⟩
  exact ⟨hV, hE, hS, fun env => hEv env trivial⟩

/-!
### 3.3 Join-Point Pruning Refinement (`SlotRefines` / `StateRefines`)

The symbolic evaluator prunes dead locals at joins (`joinCanon`), so the states it tracks are
*more dead* than the concrete (unpruned) state: every abstract slot either equals the concrete
slot or is the concrete slot's `kill` (dead, same borrow-dirtied generation). Every concrete
operation is monotone w.r.t. this refinement (`execStmts_refines`), which is what lets the
untrusted liveness mask stay outside the trusted concrete semantics.
-/

/-- Slot refinement: abstract slot `a` equals concrete slot `c`, or is its join-point prune `c.kill`. -/
def SlotRefines (a c : Slot Nat) : Prop := a = c ∨ a = c.kill

/-- Pointwise slot-list refinement (forces equal lengths). -/
def SlotsRefine : List (Slot Nat) → List (Slot Nat) → Prop
  | [], [] => True
  | a :: as, c :: cs => SlotRefines a c ∧ SlotsRefine as cs
  | _, _ => False

/-- State refinement between an abstract (join-pruned) and a concrete `CanonState Nat`. -/
def StateRefines (a c : CanonState Nat) : Prop := SlotsRefine a.slots c.slots

theorem SlotsRefine.refl : ∀ (cs : List (Slot Nat)), SlotsRefine cs cs
  | [] => trivial
  | _ :: cs => ⟨Or.inl rfl, SlotsRefine.refl cs⟩

theorem StateRefines.refl (c : CanonState Nat) : StateRefines c c :=
  SlotsRefine.refl c.slots

theorem SlotsRefine.length_eq : ∀ {as cs : List (Slot Nat)}, SlotsRefine as cs →
    as.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [SlotsRefine.length_eq h]
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

theorem StateRefines.length_eq {a c : CanonState Nat} (h : StateRefines a c) :
    a.slots.length = c.slots.length :=
  SlotsRefine.length_eq h

theorem Slot.kill_reborn {Val : Type} (s : Slot Val) : s.kill.reborn = s.reborn := rfl

/-- A non-dead abstract slot refines only itself. -/
theorem SlotRefines.eq_of_not_dead {a c : Slot Nat} (h : SlotRefines a c)
    (hNot : ∀ g, a ≠ .dead g) : c = a := by
  rcases h with h | h
  · exact h.symm
  · exact absurd h (hNot c.nextGenOnEnd)

theorem SlotsRefine.getSlotAt : ∀ {as cs : List (Slot Nat)} (loc : LocalId),
    SlotsRefine as cs → SlotRefines (getSlotAt as loc) (getSlotAt cs loc)
  | [], [], _, _ => Or.inl rfl
  | _ :: _, _ :: _, 0, ⟨h, _⟩ => h
  | _ :: _, _ :: _, loc + 1, ⟨_, h⟩ => SlotsRefine.getSlotAt loc h
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h

theorem StateRefines.getSlot {a c : CanonState Nat} (h : StateRefines a c) (loc : LocalId) :
    SlotRefines (a.getSlot loc) (c.getSlot loc) :=
  SlotsRefine.getSlotAt loc h

theorem SlotsRefine.setSlotAt : ∀ {as cs : List (Slot Nat)} (loc : LocalId) {a c : Slot Nat},
    SlotsRefine as cs → SlotRefines a c → SlotsRefine (setSlotAt as loc a) (setSlotAt cs loc c)
  | [], [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, 0, _, _, ⟨_, hT⟩, hS => ⟨hS, hT⟩
  | _ :: _, _ :: _, loc + 1, _, _, ⟨hH, hT⟩, hS => ⟨hH, SlotsRefine.setSlotAt loc hT hS⟩
  | [], _ :: _, _, _, _, h, _ => False.elim h
  | _ :: _, [], _, _, _, h, _ => False.elim h

theorem StateRefines.setSlot {a c : CanonState Nat} {loc : LocalId} {sa sc : Slot Nat}
    (h : StateRefines a c) (hS : SlotRefines sa sc) :
    StateRefines (a.setSlot loc sa) (c.setSlot loc sc) :=
  SlotsRefine.setSlotAt loc h hS

theorem readConcreteScalar_refines {a c : CanonState Nat} (h : StateRefines a c)
    {loc : LocalId} {v : Nat} (hRead : readConcreteScalar a loc = some v) :
    readConcreteScalar c loc = some v := by
  unfold readConcreteScalar at hRead ⊢
  have hS := h.getSlot loc
  cases hA : a.getSlot loc with
  | dead g => rw [hA] at hRead; cases hRead
  | uninit g => rw [hA] at hRead; cases hRead
  | live v' g b l =>
    rw [hA] at hRead hS
    rw [hS.eq_of_not_dead (by intro _ hh; cases hh)]
    exact hRead

theorem evalConcreteRvalue_refines {a c : CanonState Nat} (h : StateRefines a c)
    {rv : MirRvalue} {v : Nat} (hEval : evalConcreteRvalue a rv = some v) :
    evalConcreteRvalue c rv = some v := by
  cases rv with
  | const n => exact hEval
  | use src => exact readConcreteScalar_refines h hEval
  | op1 op src =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    cases hR : readConcreteScalar a src with
    | none => rw [hR] at hEval; cases hEval
    | some x =>
      rw [hR] at hEval
      rw [readConcreteScalar_refines h hR]
      exact hEval
  | op2 op lhs rhs =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    cases hL : readConcreteScalar a lhs with
    | none => rw [hL] at hEval; cases hEval
    | some x =>
      cases hR : readConcreteScalar a rhs with
      | none => rw [hL, hR] at hEval; cases hEval
      | some y =>
        rw [hL, hR] at hEval
        rw [readConcreteScalar_refines h hL, readConcreteScalar_refines h hR]
        exact hEval
  | derefRef ptr =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    have hP := h.getSlot ptr
    cases hPtr : a.getSlot ptr with
    | dead _ => rw [hPtr] at hEval; cases hEval
    | uninit _ => rw [hPtr] at hEval; cases hEval
    | live pv pg pb pl =>
      rw [hPtr] at hEval hP
      rw [hP.eq_of_not_dead (by intro _ hh; cases hh)]
      cases pl with
      | none => cases hEval
      | some pair =>
        rcases pair with ⟨target, expGen⟩
        dsimp only at hEval ⊢
        have hT := h.getSlot target
        cases hTgt : a.getSlot target with
        | dead _ => rw [hTgt] at hEval; cases hEval
        | uninit _ => rw [hTgt] at hEval; cases hEval
        | live tv tg tb tl =>
          rw [hTgt] at hEval hT
          rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
          exact hEval

theorem writeVal?_refines {a c : Slot Nat} (h : SlotRefines a c) {v : Nat}
    {l : Option (LocalId × Nat)} {a' : Slot Nat} (hW : a.writeVal? v l = some a') :
    c.writeVal? v l = some a' := by
  have hc : c = a := h.eq_of_not_dead (by
    intro g hg
    subst hg
    cases hW)
  rw [hc]
  exact hW

theorem Slot.ownerRead_kill {Val : Type} (s : Slot Val) : s.ownerRead.kill = s.kill := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem SlotRefines.ownerRead {a c : Slot Nat} (h : SlotRefines a c) :
    SlotRefines a.ownerRead c.ownerRead := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · subst h
    exact Or.inr (Slot.ownerRead_kill c).symm

theorem StateRefines.ownerReadLoc {a c : CanonState Nat} (h : StateRefines a c) (loc : LocalId) :
    StateRefines (a.ownerReadLoc loc) (c.ownerReadLoc loc) :=
  h.setSlot (h.getSlot loc).ownerRead

theorem StateRefines.ownerReadRvalue {a c : CanonState Nat} (h : StateRefines a c) (rv : MirRvalue) :
    StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue]
  · exact h
  · exact h.ownerReadLoc _
  · exact h.ownerReadLoc _
  · exact (h.ownerReadLoc _).ownerReadLoc _
  · exact h.ownerReadLoc _

theorem SlotRefines.retarget {a c : Slot Nat} (h : SlotRefines a c) (target g : Nat) :
    SlotRefines (a.retarget target g) (c.retarget target g) := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · subst h
    cases c with
    | dead _ => exact Or.inr rfl
    | uninit _ => exact Or.inr rfl
    | live pv pg pb pl => exact Or.inr (by cases pb <;> rfl)

theorem StateRefines.storeThrough {a c : CanonState Nat} (h : StateRefines a c)
    (ptr target : LocalId) (v g : Nat) (loan : Option (LocalId × Nat)) :
    StateRefines (a.storeThrough ptr target v g loan) (c.storeThrough ptr target v g loan) := by
  dsimp only [CanonState.storeThrough]
  have h₁ : StateRefines ((a.ownerReadLoc ptr).setSlot target (.live v g true loan))
      ((c.ownerReadLoc ptr).setSlot target (.live v g true loan)) :=
    (h.ownerReadLoc ptr).setSlot (Or.inl rfl)
  exact h₁.setSlot ((h₁.getSlot ptr).retarget target g)

/-- **Refinement Monotonicity of a Concrete Step (`execStmt_refines`)**: if a statement succeeds
    on the (more-dead) abstract state, it succeeds on every refined concrete state, and the
    results remain related. -/
theorem execStmt_refines {a c : CanonState Nat} (h : StateRefines a c) {stmt : MirStmt}
    {a' : CanonState Nat} (hExec : execStmt a stmt = some a') :
    ∃ c', execStmt c stmt = some c' ∧ StateRefines a' c' := by
  cases stmt with
  | assign dst rv =>
    dsimp only [execStmt] at hExec ⊢
    cases hRv : evalConcreteRvalue a rv with
    | none => rw [hRv] at hExec; cases hExec
    | some v =>
      rw [hRv] at hExec
      rw [evalConcreteRvalue_refines h hRv]
      dsimp only at hExec ⊢
      have h₀ : StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) :=
        h.ownerReadRvalue rv
      cases hW : ((a.ownerReadRvalue rv).getSlot dst).writeVal? v none with
      | none => rw [hW] at hExec; cases hExec
      | some s' =>
        rw [hW] at hExec
        rw [writeVal?_refines (h₀.getSlot dst) hW]
        injection hExec with hA'
        subst hA'
        exact ⟨_, rfl, h₀.setSlot (Or.inl rfl)⟩
  | storageLive loc =>
    dsimp only [execStmt] at hExec ⊢
    rw [← h.length_eq]
    split at hExec
    · rename_i hLt
      injection hExec with hA'
      subst hA'
      refine ⟨_, ite_eq_left hLt, h.setSlot ?_⟩
      rcases h.getSlot loc with hS | hS
      · rw [hS]
        exact Or.inl rfl
      · rw [hS, Slot.kill_reborn]
        exact Or.inl rfl
    · cases hExec
  | storageDead loc =>
    dsimp only [execStmt] at hExec ⊢
    rw [← h.length_eq]
    split at hExec
    · rename_i hLt
      injection hExec with hA'
      subst hA'
      refine ⟨_, ite_eq_left hLt, h.setSlot ?_⟩
      rcases h.getSlot loc with hS | hS
      · rw [hS]
        exact Or.inl rfl
      · rw [hS, Slot.kill_idempotent]
        exact Or.inl rfl
    · cases hExec
  | assert cond =>
    dsimp only [execStmt] at hExec ⊢
    cases hR : readConcreteScalar a cond with
    | none => rw [hR] at hExec; cases hExec
    | some v =>
      rw [hR] at hExec
      rw [readConcreteScalar_refines h hR]
      dsimp only at hExec ⊢
      split at hExec
      · rename_i hNz
        injection hExec with hA'
        subst hA'
        exact ⟨c.ownerReadLoc cond, ite_eq_left hNz, h.ownerReadLoc cond⟩
      · cases hExec
  | retagBorrow dst target =>
    dsimp only [execStmt] at hExec ⊢
    have hT := h.getSlot target
    cases hTgt : a.getSlot target with
    | dead _ => rw [hTgt] at hExec; cases hExec
    | uninit _ => rw [hTgt] at hExec; cases hExec
    | live tv g b tl =>
      rw [hTgt] at hExec hT
      rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
      dsimp only at hExec ⊢
      generalize (if b = true then g + 1 else g) = g' at hExec ⊢
      have h₁ : StateRefines (a.setSlot target (.live tv g' true tl))
          (c.setSlot target (.live tv g' true tl)) := h.setSlot (Or.inl rfl)
      cases hW : ((a.setSlot target (.live tv g' true tl)).getSlot dst).writeVal? tv
          (some (target, g')) with
      | none => rw [hW] at hExec; cases hExec
      | some s' =>
        rw [hW] at hExec
        rw [writeVal?_refines (h₁.getSlot dst) hW]
        injection hExec with hA'
        subst hA'
        exact ⟨_, rfl, h₁.setSlot (Or.inl rfl)⟩
  | storeRef ptr rv =>
    dsimp only [execStmt] at hExec ⊢
    cases hRv : evalConcreteRvalue a rv with
    | none => rw [hRv] at hExec; cases hExec
    | some v =>
      rw [hRv] at hExec
      rw [evalConcreteRvalue_refines h hRv]
      dsimp only at hExec ⊢
      have h₀ : StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) :=
        h.ownerReadRvalue rv
      have hP := h₀.getSlot ptr
      cases hPtr : (a.ownerReadRvalue rv).getSlot ptr with
      | dead _ => rw [hPtr] at hExec; cases hExec
      | uninit _ => rw [hPtr] at hExec; cases hExec
      | live pv pg pb pl =>
        rw [hPtr] at hExec hP
        rw [hP.eq_of_not_dead (by intro _ hh; cases hh)]
        cases pl with
        | none => cases hExec
        | some lPair =>
          rcases lPair with ⟨target, expGen⟩
          dsimp only at hExec ⊢
          have hT := h₀.getSlot target
          cases hTgt : (a.ownerReadRvalue rv).getSlot target with
          | dead _ => rw [hTgt] at hExec; cases hExec
          | uninit _ => rw [hTgt] at hExec; cases hExec
          | live tv curGen tb tl =>
            rw [hTgt] at hExec hT
            rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
            cases tb with
            | false => cases hExec
            | true =>
              cases tl with
              | some _ => cases hExec
              | none =>
                dsimp only at hExec ⊢
                split at hExec
                · rename_i hGenEq
                  injection hExec with hA'
                  subst hA'
                  exact ⟨_, ite_eq_left hGenEq, h₀.storeThrough ptr target v (curGen + 1) none⟩
                · cases hExec

theorem execStmts_refines : ∀ (stmts : List MirStmt) {a c a' : CanonState Nat},
    StateRefines a c → execStmts a stmts = some a' →
    ∃ c', execStmts c stmts = some c' ∧ StateRefines a' c'
  | [], a, c, a', h, hExec => by
    dsimp only [execStmts] at hExec
    injection hExec with hA'
    subst hA'
    exact ⟨c, rfl, h⟩
  | stmt :: rest, a, c, a', h, hExec => by
    dsimp only [execStmts] at hExec ⊢
    cases hS : execStmt a stmt with
    | none => rw [hS] at hExec; cases hExec
    | some a₁ =>
      rw [hS] at hExec
      dsimp only at hExec
      rcases execStmt_refines h hS with ⟨c₁, hC₁, hR₁⟩
      rw [hC₁]
      exact execStmts_refines rest hR₁ hExec

/-- Length-preserving join-point pruning of a dense slot list against a liveness mask: slot
    `i` is kept when `mask[i] = true` (or when the mask is shorter than the slot list) and
    replaced by `Slot.kill` (dead, keeping its borrow-dirtied generation) when
    `mask[i] = false`. -/
def pruneSlots {Val : Type} : List Bool → List (Slot Val) → List (Slot Val)
  | [], ss => ss
  | _ :: _, [] => []
  | b :: bs, s :: ss => normalizeSlotForMask b s :: pruneSlots bs ss

/-- Join-point canonicalization of a dense `CanonState` (`CanonLocals` pruning). -/
def joinCanon {Val : Type} (mask : List Bool) (st : CanonState Val) : CanonState Val :=
  { slots := pruneSlots mask st.slots }

theorem pruneSlots_idempotent {Val : Type} : ∀ (mask : List Bool) (ss : List (Slot Val)),
    pruneSlots mask (pruneSlots mask ss) = pruneSlots mask ss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, s :: ss => by
    simp only [pruneSlots]
    rw [normalizeSlotForMask_idempotent, pruneSlots_idempotent bs ss]

/-- `joinCanon` is idempotent (re-pruning a pruned state is a no-op). -/
theorem joinCanon_idempotent {Val : Type} (mask : List Bool) (st : CanonState Val) :
    joinCanon mask (joinCanon mask st) = joinCanon mask st := by
  dsimp only [joinCanon]
  rw [pruneSlots_idempotent]

theorem SlotRefines.normalize {a c : Slot Nat} (h : SlotRefines a c) (b : Bool) :
    SlotRefines (normalizeSlotForMask b a) c := by
  cases b with
  | true => exact h
  | false =>
    rcases h with h | h
    · subst h
      exact Or.inr rfl
    · subst h
      exact Or.inr (Slot.kill_idempotent c)

theorem pruneSlots_refines : ∀ (mask : List Bool) {as cs : List (Slot Nat)},
    SlotsRefine as cs → SlotsRefine (pruneSlots mask as) cs
  | [], _, _, h => h
  | _ :: _, [], [], _ => trivial
  | b :: bs, _ :: _, _ :: _, ⟨hH, hT⟩ => ⟨hH.normalize b, pruneSlots_refines bs hT⟩
  | _ :: _, [], _ :: _, h => False.elim h
  | _ :: _, _ :: _, [], h => False.elim h

/-- Pruning dead locals keeps a refined state refined (the abstract side only gets deader). -/
theorem StateRefines.joinCanon {a c : CanonState Nat} (h : StateRefines a c) (mask : List Bool) :
    StateRefines (joinCanon mask a) c :=
  pruneSlots_refines mask h

theorem map_pruneSlots (tbl : SymTable) (env : SymEnv) :
    ∀ (mask : List Bool) (ss : List (Slot SymId)),
      (pruneSlots mask ss).map (evalSymSlot tbl env) =
        pruneSlots mask (ss.map (evalSymSlot tbl env))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, s :: ss => by
    simp only [pruneSlots, List.map_cons]
    rw [map_pruneSlots tbl env bs ss]
    cases b with
    | true => rfl
    | false =>
      dsimp [normalizeSlotForMask]
      rw [evalSymSlot_kill]

theorem evalSymCanonState_joinCanon (tbl : SymTable) (env : SymEnv) (mask : List Bool)
    (st : CanonState SymId) :
    evalSymCanonState tbl env (joinCanon mask st) =
      joinCanon mask (evalSymCanonState tbl env st) := by
  dsimp only [evalSymCanonState, joinCanon]
  rw [map_pruneSlots]

theorem ValidSymSlots_pruneSlots {bound : Nat} : ∀ (mask : List Bool) {ss : List (Slot SymId)},
    ValidSymSlots bound ss → ValidSymSlots bound (pruneSlots mask ss)
  | [], _, h => h
  | _ :: _, [], _ => trivial
  | b :: bs, _ :: _, ⟨hH, hT⟩ => by
    refine ⟨?_, ValidSymSlots_pruneSlots bs hT⟩
    cases b with
    | true => exact hH
    | false => trivial

theorem ValidSymCanonState.joinCanon {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (mask : List Bool) :
    ValidSymCanonState bound (joinCanon mask st) :=
  ValidSymSlots_pruneSlots mask h

/-!
### 3.4 Compositional Diamond Join (`symExecDiamondJoin`, `wpJoinBlock_sound`)
-/

/-- `goto` target of an arm block, if its terminator is a `goto`. -/
def armGoto? (blk : MirBlock) : Option BlockId :=
  match blk.term with
  | .goto j => some j
  | _ => none

theorem armGoto?_spec {blk : MirBlock} {j : BlockId} (h : armGoto? blk = some j) :
    blk.term = .goto j := by
  unfold armGoto? at h
  split at h
  · rename_i j' hTerm
    injection h with hj
    subst hj
    exact hTerm
  · cases h

/-- Recognize a `switchInt` diamond: both arm blocks exist and end in `goto` the same join
    block. Returns `(thenStmts, elseStmts, joinBb)`. -/
def matchDiamond (cfg : MirCfg) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId) :=
  match cfg.blocks[thenBb]?, cfg.blocks[elseBb]? with
  | some tBlk, some eBlk =>
    match armGoto? tBlk, armGoto? eBlk with
    | some jT, some jF => if jT = jF then some (tBlk.stmts, eBlk.stmts, jT) else none
    | _, _ => none
  | _, _ => none

theorem matchDiamond_spec {cfg : MirCfg} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt}
    (h : matchDiamond cfg thenBb elseBb = some (thenStmts, elseStmts, joinBb)) :
    ∃ tBlk eBlk, cfg.blocks[thenBb]? = some tBlk ∧ cfg.blocks[elseBb]? = some eBlk ∧
      tBlk.stmts = thenStmts ∧ eBlk.stmts = elseStmts ∧
      tBlk.term = .goto joinBb ∧ eBlk.term = .goto joinBb := by
  unfold matchDiamond at h
  split at h
  · rename_i tBlk eBlk hT hE
    split at h
    · rename_i jT jF hjT hjF
      split at h
      · rename_i hj
        subst hj
        injection h with h1
        injection h1 with hS1 h2
        injection h2 with hS2 hJ
        subst hS1 hS2 hJ
        exact ⟨tBlk, eBlk, hT, hE, rfl, rfl, armGoto?_spec hjT, armGoto?_spec hjF⟩
      · cases h
    · cases h
  · cases h

/-- Diamond merge plan: a recognized diamond whose join block carries a liveness hint. -/
def diamondMergePlan (cfg : MirCfg) (hints : JoinHints) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId × List Bool) :=
  match matchDiamond cfg thenBb elseBb with
  | some (thenStmts, elseStmts, joinBb) =>
    match hints joinBb with
    | some mask => some (thenStmts, elseStmts, joinBb, mask)
    | none => none
  | none => none

theorem diamondMergePlan_spec {cfg : MirCfg} {hints : JoinHints} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (h : diamondMergePlan cfg hints thenBb elseBb = some (thenStmts, elseStmts, joinBb, mask)) :
    matchDiamond cfg thenBb elseBb = some (thenStmts, elseStmts, joinBb) := by
  unfold diamondMergePlan at h
  split at h
  · rename_i tS eS j hM
    split at h
    · injection h with h1
      injection h1 with hS1 h2
      injection h2 with hS2 h3
      injection h3 with hJ _
      subst hS1 hS2 hJ
      exact hM
    · cases h
  · cases h

/-- Triangle plan with the arm on the `then` side: the `then` successor is an arm block ending in
    `goto elseBb`, and the `else` successor **is** the (hinted) join block. -/
def triangleThenPlan (cfg : MirCfg) (hints : JoinHints) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId × List Bool) :=
  match cfg.blocks[thenBb]? with
  | some tBlk =>
    match armGoto? tBlk with
    | some j =>
      if j = elseBb then
        match hints elseBb with
        | some mask => some (tBlk.stmts, [], elseBb, mask)
        | none => none
      else none
    | none => none
  | none => none

/-- Triangle plan with the arm on the `else` side: the `else` successor is an arm block ending in
    `goto thenBb`, and the `then` successor **is** the (hinted) join block. -/
def triangleElsePlan (cfg : MirCfg) (hints : JoinHints) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId × List Bool) :=
  match cfg.blocks[elseBb]? with
  | some eBlk =>
    match armGoto? eBlk with
    | some j =>
      if j = thenBb then
        match hints thenBb with
        | some mask => some ([], eBlk.stmts, thenBb, mask)
        | none => none
      else none
    | none => none
  | none => none

/-- Triangle merge plan (`if c { arm }` without `else`, the shape post-`SimplifyCfg` MIR gives every
    `if` without `else` and most sequential bounds/bit-validity fix-ups): returns
    `(thenStmts, elseStmts, joinBb, mask)` with `[]` on the side that jumps straight to the join, so
    `symExecDiamondJoin` / `wpJoinBlock_sound` apply unchanged and the join is evaluated once. -/
def triangleMergePlan (cfg : MirCfg) (hints : JoinHints) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId × List Bool) :=
  match triangleThenPlan cfg hints thenBb elseBb with
  | some plan => some plan
  | none => triangleElsePlan cfg hints thenBb elseBb

theorem triangleThenPlan_spec {cfg : MirCfg} {hints : JoinHints} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (h : triangleThenPlan cfg hints thenBb elseBb = some (thenStmts, elseStmts, joinBb, mask)) :
    ∃ tBlk, cfg.blocks[thenBb]? = some tBlk ∧ tBlk.stmts = thenStmts ∧
      tBlk.term = .goto joinBb ∧ elseBb = joinBb ∧ elseStmts = [] := by
  unfold triangleThenPlan at h
  split at h
  · rename_i tBlk hT
    split at h
    · rename_i j hj
      split at h
      · rename_i hjE
        subst hjE
        split at h
        · injection h with h1
          injection h1 with hS1 h2
          injection h2 with hS2 h3
          injection h3 with hJ _
          subst hS1 hS2 hJ
          exact ⟨tBlk, hT, rfl, armGoto?_spec hj, rfl, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem triangleElsePlan_spec {cfg : MirCfg} {hints : JoinHints} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (h : triangleElsePlan cfg hints thenBb elseBb = some (thenStmts, elseStmts, joinBb, mask)) :
    ∃ eBlk, cfg.blocks[elseBb]? = some eBlk ∧ eBlk.stmts = elseStmts ∧
      eBlk.term = .goto joinBb ∧ thenBb = joinBb ∧ thenStmts = [] := by
  unfold triangleElsePlan at h
  split at h
  · rename_i eBlk hE
    split at h
    · rename_i j hj
      split at h
      · rename_i hjT
        subst hjT
        split at h
        · injection h with h1
          injection h1 with hS1 h2
          injection h2 with hS2 h3
          injection h3 with hJ _
          subst hS1 hS2 hJ
          exact ⟨eBlk, hE, rfl, armGoto?_spec hj, rfl, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem triangleMergePlan_spec {cfg : MirCfg} {hints : JoinHints} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (h : triangleMergePlan cfg hints thenBb elseBb = some (thenStmts, elseStmts, joinBb, mask)) :
    (∃ tBlk, cfg.blocks[thenBb]? = some tBlk ∧ tBlk.stmts = thenStmts ∧
        tBlk.term = .goto joinBb ∧ elseBb = joinBb ∧ elseStmts = []) ∨
      (∃ eBlk, cfg.blocks[elseBb]? = some eBlk ∧ eBlk.stmts = elseStmts ∧
        eBlk.term = .goto joinBb ∧ thenBb = joinBb ∧ thenStmts = []) := by
  unfold triangleMergePlan at h
  cases hT : triangleThenPlan cfg hints thenBb elseBb with
  | some plan =>
    rw [hT] at h
    injection h with hEq
    subst hEq
    exact Or.inl (triangleThenPlan_spec hT)
  | none =>
    rw [hT] at h
    exact Or.inr (triangleElsePlan_spec h)

/-- Execute both diamond arms symbolically from `(st, tbl)` under their respective branch
    path conditions conjoined with the enclosing `pc` (`(condId, true) :: pc` for `thenStmts`,
    `(condId, false) :: pc` for `elseStmts`), prune both post-states with the (untrusted) join mask,
    and merge them into ONE continuation state under `condId`. -/
def symExecDiamondJoin (st : CanonState SymId) (tbl : SymTable) (condId : SymId)
    (thenStmts elseStmts : List MirStmt) (mask : List Bool) (pc : PathCond := []) :
    Option (CanonState SymId × SymTable) :=
  match symExecStmts st tbl thenStmts ((condId, true) :: pc) with
  | none => none
  | some (stT, tbl₁) =>
    match symExecStmts st tbl₁ elseStmts ((condId, false) :: pc) with
    | none => none
    | some (stF, tbl₂) => mergeJoinStates tbl₂ condId (joinCanon mask stT) (joinCanon mask stF)

/-- Alias for `symExecDiamondJoin` (`wpJoinDiamond`). -/
abbrev wpJoinDiamond := @symExecDiamondJoin

/-- **Path-Sensitive Compositional Join-Point Soundness (`wpJoinBlock_under_sound`)**: under an
    enclosing conjunctive `pc : PathCond`, the single merged state `stM` produced by
    `symExecDiamondJoin` soundly abstracts — via `StateRefines` — the concrete post-state of
    whichever arm the concrete (mask-free) execution takes. -/
theorem wpJoinBlock_under_sound {st stM : CanonState SymId} {tbl tblM : SymTable} {condId : SymId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool} {pc : PathCond}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hCond : condId < tbl.nodes.length)
    (hPcValid : PathCondValid tbl.nodes.length pc)
    (hJoin : symExecDiamondJoin st tbl condId thenStmts elseStmts mask pc = some (stM, tblM)) :
    ValidTable tblM ∧ tbl.Extends tblM ∧ ValidSymCanonState tblM.nodes.length stM ∧
      ∀ (env : SymEnv) (cst : CanonState Nat),
        PathCondHolds tbl env pc →
        StateRefines (evalSymCanonState tbl env st) cst →
        ∃ cst', execStmts cst (if evalSymId tbl env condId != 0 then thenStmts else elseStmts) =
            some cst' ∧
          StateRefines (evalSymCanonState tblM env stM) cst' := by
  unfold symExecDiamondJoin at hJoin
  cases hThen : symExecStmts st tbl thenStmts ((condId, true) :: pc) with
  | none => rw [hThen] at hJoin; cases hJoin
  | some pT =>
    rcases pT with ⟨stT, tbl₁⟩
    rw [hThen] at hJoin
    dsimp only at hJoin
    rcases symExecStmts_under_sound thenStmts hValid hSt hThen ⟨hCond, hPcValid⟩ with
      ⟨hValid₁, hExt₁, hStT, hEvalT⟩
    have hSt₁ : ValidSymCanonState tbl₁.nodes.length st := ValidSymSlots.mono hSt hExt₁.length_le
    have hCond₁ : condId < tbl₁.nodes.length := Nat.lt_of_lt_of_le hCond hExt₁.length_le
    have hPcValid₁ : PathCondValid tbl₁.nodes.length pc := hPcValid.mono hExt₁.length_le
    cases hElse : symExecStmts st tbl₁ elseStmts ((condId, false) :: pc) with
    | none => rw [hElse] at hJoin; cases hJoin
    | some pF =>
      rcases pF with ⟨stF, tbl₂⟩
      rw [hElse] at hJoin
      dsimp only at hJoin
      rcases symExecStmts_under_sound elseStmts hValid₁ hSt₁ hElse ⟨hCond₁, hPcValid₁⟩ with
        ⟨hValid₂, hExt₂, hStF, hEvalF⟩
      have hExt₀₂ : tbl.Extends tbl₂ := hExt₁.trans hExt₂
      have hCond₂ : condId < tbl₂.nodes.length := Nat.lt_of_lt_of_le hCond hExt₀₂.length_le
      have hStTc : ValidSymCanonState tbl₂.nodes.length (joinCanon mask stT) :=
        ValidSymSlots.mono (hStT.joinCanon mask) hExt₂.length_le
      have hStFc : ValidSymCanonState tbl₂.nodes.length (joinCanon mask stF) :=
        hStF.joinCanon mask
      rcases mergeJoinStates_eval hValid₂ hCond₂ hStTc hStFc hJoin with
        ⟨hValidM, hExtM, hStM, hEvalM⟩
      refine ⟨hValidM, hExt₀₂.trans hExtM, hStM, ?_⟩
      intro env cst hPc hR
      rw [hEvalM env, ← evalSymId_mono hValid hExt₀₂ env hCond]
      cases hB : (evalSymId tbl env condId != 0) with
      | true =>
        rcases execStmts_refines thenStmts hR (hEvalT env ⟨hB, hPc⟩) with ⟨cT, hCT, hRT⟩
        refine ⟨cT, by rw [ite_eq_left rfl]; exact hCT, ?_⟩
        rw [ite_eq_left rfl, ← evalSymCanonState_mono hValid₁ hExt₂ env (hStT.joinCanon mask),
          evalSymCanonState_joinCanon]
        exact hRT.joinCanon mask
      | false =>
        have hR₁ : StateRefines (evalSymCanonState tbl₁ env st) cst := by
          rw [← evalSymCanonState_mono hValid hExt₁ env hSt]
          exact hR
        have hB₁ : PathCondHolds tbl₁ env ((condId, false) :: pc) := by
          refine ⟨?_, PathCondHolds.mono hValid hExt₁ hPcValid hPc⟩
          show (evalSymId tbl₁ env condId != 0) = false
          rw [← evalSymId_mono hValid hExt₁ env hCond]
          exact hB
        rcases execStmts_refines elseStmts hR₁ (hEvalF env hB₁) with ⟨cF, hCF, hRF⟩
        refine ⟨cF, by rw [ite_eq_right Bool.false_ne_true]; exact hCF, ?_⟩
        rw [ite_eq_right Bool.false_ne_true, evalSymCanonState_joinCanon]
        exact hRF.joinCanon mask

/-- **Compositional Join-Point Soundness (`wpJoinBlock_sound`)**: the single merged state
    `stM` produced by `symExecDiamondJoin` soundly abstracts — via `StateRefines` — the
    concrete post-state of whichever arm the concrete (mask-free) execution takes, from every
    concrete state refined by the evaluated entry state. The join continuation can therefore
    be analyzed **once**, from `stM`. -/
theorem wpJoinBlock_sound {st stM : CanonState SymId} {tbl tblM : SymTable} {condId : SymId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hCond : condId < tbl.nodes.length)
    (hJoin : symExecDiamondJoin st tbl condId thenStmts elseStmts mask = some (stM, tblM)) :
    ValidTable tblM ∧ tbl.Extends tblM ∧ ValidSymCanonState tblM.nodes.length stM ∧
      ∀ (env : SymEnv) (cst : CanonState Nat),
        StateRefines (evalSymCanonState tbl env st) cst →
        ∃ cst', execStmts cst (if evalSymId tbl env condId != 0 then thenStmts else elseStmts) =
            some cst' ∧
          StateRefines (evalSymCanonState tblM env stM) cst' := by
  rcases wpJoinBlock_under_sound (pc := []) hValid hSt hCond trivial hJoin with
    ⟨hVM, hEM, hStM, hEv⟩
  exact ⟨hVM, hEM, hStM, fun env cst hR => hEv env cst trivial hR⟩

end Anneal.Rustc.V2026_06_01.SymbolicEval
