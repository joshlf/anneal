-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.SimpLemmas

/-!
# Radix-2 Trie RUP / LRAT Certificate Checker (`Workbench.Pass1.BitTrieLrat`)

Pass-1-portable (`prelude` + locked `Init.*` only, `[propext]` only, zero
`._unsafe_rec`, zero `bv_decide`) propositional UNSAT certificate checker:

- Uses `@Nat.rec` and `List.foldr` exclusively so Lean emits zero `._unsafe_rec`
  or `isPartial` helpers.
- `checkRupProof_sound` discharges `UnsatCnf cnf` from `checkRupProof depth cnf
  steps = .unsatVerified` via `rfl` or `decide`.
- Includes positive diamond UNSAT and forged-hint rejection canaries.
-/

namespace Workbench.Pass1.BitTrieLrat

def strictNat {α : Type} (v : Nat) (k : Nat → α) : α :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem strictNat_eq {α : Type} (v : Nat) (k : Nat → α) :
    strictNat v k = k v := by
  cases v <;> rfl

def listFoldl {α β : Type} (f : β → α → β) (init : β) (xs : List α) : β :=
  List.foldr (fun (x : α) (k : β → β) (acc : β) => k (f acc x))
    (fun (acc : β) => acc) xs init

theorem listFoldl_cons {α β : Type} (f : β → α → β) (init : β)
    (x : α) (xs : List α) :
    listFoldl f init (x :: xs) = listFoldl f (f init x) xs := rfl

def boolNot (b : Bool) : Bool :=
  match b with | true => false | false => true

def boolOr (a b : Bool) : Bool :=
  match a with | true => true | false => b

def boolAnd (a b : Bool) : Bool :=
  match a with | true => b | false => false

def boolBeq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolAnd_eq_true :
    ∀ (a b : Bool), boolAnd a b = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, true, h => nomatch h
  | false, false, h => nomatch h

theorem boolOr_eq_false :
    ∀ (a b : Bool), boolOr a b = false → a = false ∧ b = false
  | false, false, _ => ⟨rfl, rfl⟩
  | false, true, h => nomatch h
  | true, false, h => nomatch h
  | true, true, h => nomatch h

theorem boolBeq_false_not :
    ∀ (a b : Bool), boolBeq a b = false → a = boolNot b
  | true, true, h => nomatch h
  | true, false, _ => rfl
  | false, true, _ => rfl
  | false, false, h => nomatch h

theorem boolBeq_true_eq :
    ∀ (a b : Bool), boolBeq a b = true → a = b
  | true, true, _ => rfl
  | true, false, h => nomatch h
  | false, true, h => nomatch h
  | false, false, _ => rfl

theorem eq_of_nat_beq : ∀ (a b : Nat), Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg Nat.succ (eq_of_nat_beq a b h)

theorem mod2_eq_one_of_beq_zero_false (m : Nat)
    (h : Nat.beq (Nat.mod m 2) 0 = false) : Nat.mod m 2 = 1 := by
  have hLt : Nat.mod m 2 < 2 := Nat.mod_lt m (by decide)
  cases hm : Nat.mod m 2 with
  | zero => rw [hm] at h; nomatch h
  | succ k =>
    rw [hm] at hLt
    cases k with
    | zero => rfl
    | succ k2 =>
      nomatch (@Nat.lt_of_succ_lt_succ k2 0
        (@Nat.lt_of_succ_lt_succ (k2 + 1) 1 hLt))

theorem div2_mod2_inj (m n : Nat)
    (hDiv : Nat.div n 2 = Nat.div m 2)
    (hMod : Nat.mod n 2 = Nat.mod m 2) : n = m := by
  have hm : 2 * Nat.div m 2 + Nat.mod m 2 = m := Nat.div_add_mod m 2
  have hn : 2 * Nat.div n 2 + Nat.mod n 2 = n := Nat.div_add_mod n 2
  rw [hDiv, hMod] at hn
  rw [← hn, hm]

/-! ## 1. Depth-Bounded Radix-2 Trie (`Trie α`) -/

inductive Trie (α : Type) where
  | leaf
  | node (val : Option α) (ev od : Trie α)

def strictTrie {α β : Type} (t : Trie α) (k : Trie α → β) : β :=
  match t with
  | .leaf => k .leaf
  | .node v l r => k (.node v l r)

theorem strictTrie_eq {α β : Type} (t : Trie α) (k : Trie α → β) :
    strictTrie t k = k t := by
  cases t <;> rfl

def Trie.get {α : Type} (depth : Nat) (t : Trie α) (k : Nat) : Option α :=
  @Nat.rec (fun _ => Trie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur idx =>
      match cur with
      | .leaf => none
      | .node v ev od =>
        match idx with
        | 0 => v
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => ih ev q
            | false => ih od q))
    depth t k

theorem Trie.get_succ {α : Type} (d : Nat) (t : Trie α) (idx : Nat) :
    Trie.get (d + 1) t idx =
      match t with
      | .leaf => none
      | .node v ev od =>
        match idx with
        | 0 => v
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => Trie.get d ev q
            | false => Trie.get d od q) := rfl

def Trie.set {α : Type} (depth : Nat) (t : Trie α) (k : Nat) (v : α) :
    Trie α :=
  @Nat.rec (fun _ => Trie α → Nat → Trie α)
    (fun cur _ => cur)
    (fun _ ih cur idx =>
      match cur with
      | .leaf =>
        match idx with
        | 0 => .node (some v) .leaf .leaf
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => strictTrie (ih .leaf q) (fun ev' => .node none ev' .leaf)
            | false => strictTrie (ih .leaf q) (fun od' => .node none .leaf od'))
      | .node v0 ev0 od0 =>
        match idx with
        | 0 => .node (some v) ev0 od0
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => strictTrie (ih ev0 q) (fun ev' => .node v0 ev' od0)
            | false => strictTrie (ih od0 q) (fun od' => .node v0 ev0 od')))
    depth t k

def trieVal {α : Type} (t : Trie α) : Option α :=
  match t with | .leaf => none | .node v _ _ => v

def trieEv {α : Type} (t : Trie α) : Trie α :=
  match t with | .leaf => .leaf | .node _ ev _ => ev

def trieOd {α : Type} (t : Trie α) : Trie α :=
  match t with | .leaf => .leaf | .node _ _ od => od

theorem Trie.set_succ_parts {α : Type} (d : Nat) (t : Trie α) (idx : Nat)
    (v : α) :
    Trie.set (d + 1) t idx v =
      match idx with
      | 0 => .node (some v) (trieEv t) (trieOd t)
      | m + 1 =>
        strictNat (Nat.div m 2) (fun q =>
          match Nat.beq (Nat.mod m 2) 0 with
          | true =>
            strictTrie (Trie.set d (trieEv t) q v)
              (fun ev' => .node (trieVal t) ev' (trieOd t))
          | false =>
            strictTrie (Trie.set d (trieOd t) q v)
              (fun od' => .node (trieVal t) (trieEv t) od')) := by
  cases t <;> cases idx <;> rfl

def Trie.erase {α : Type} (depth : Nat) (t : Trie α) (k : Nat) : Trie α :=
  @Nat.rec (fun _ => Trie α → Nat → Trie α)
    (fun cur _ => cur)
    (fun _ ih cur idx =>
      match cur with
      | .leaf => .leaf
      | .node v0 ev0 od0 =>
        match idx with
        | 0 => .node none ev0 od0
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => strictTrie (ih ev0 q) (fun ev' => .node v0 ev' od0)
            | false => strictTrie (ih od0 q) (fun od' => .node v0 ev0 od')))
    depth t k

theorem Trie.erase_succ {α : Type} (d : Nat) (t : Trie α) (idx : Nat) :
    Trie.erase (d + 1) t idx =
      match t with
      | .leaf => .leaf
      | .node v0 ev0 od0 =>
        match idx with
        | 0 => .node none ev0 od0
        | m + 1 =>
          strictNat (Nat.div m 2) (fun q =>
            match Nat.beq (Nat.mod m 2) 0 with
            | true => strictTrie (Trie.erase d ev0 q)
                        (fun ev' => .node v0 ev' od0)
            | false => strictTrie (Trie.erase d od0 q)
                        (fun od' => .node v0 ev0 od')) := rfl

theorem Trie.get_leaf {α : Type} :
    ∀ (d k : Nat), Trie.get d (.leaf : Trie α) k = none
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem Trie.get_set_inv {α : Type} :
    ∀ (d : Nat) (t : Trie α) (k : Nat) (v : α) (q : Nat) (w : α),
      Trie.get d (Trie.set d t k v) q = some w →
      (q = k ∧ w = v) ∨ Trie.get d t q = some w
  | 0, _, _, _, _, _, h => nomatch h
  | d + 1, t, 0, _, 0, _, h => by
    rw [Trie.set_succ_parts, Trie.get_succ] at h
    injection h with e
    exact Or.inl ⟨rfl, e.symm⟩
  | d + 1, t, 0, _, n + 1, _, h => by
    rw [Trie.set_succ_parts, Trie.get_succ] at h
    cases t with
    | leaf =>
      dsimp only [trieEv, trieOd] at h
      rw [strictNat_eq] at h
      cases hb : Nat.beq (Nat.mod n 2) 0 <;>
        (rw [hb] at h; dsimp only at h; rw [Trie.get_leaf] at h; nomatch h)
    | node _ _ _ =>
      rw [Trie.get_succ]
      exact Or.inr h
  | d + 1, t, m + 1, _, 0, _, h => by
    rw [Trie.set_succ_parts] at h; dsimp only at h; rw [strictNat_eq] at h
    cases t with
    | leaf =>
      cases hm : Nat.beq (Nat.mod m 2) 0 <;>
        (rw [hm] at h; dsimp only at h
         rw [strictTrie_eq, Trie.get_succ] at h; nomatch h)
    | node _ _ _ =>
      cases hm : Nat.beq (Nat.mod m 2) 0 <;>
        (rw [hm] at h; dsimp only at h
         rw [strictTrie_eq, Trie.get_succ] at h
         rw [Trie.get_succ]; exact Or.inr h)
  | d + 1, t, m + 1, v, n + 1, w, h => by
    rw [Trie.set_succ_parts] at h; dsimp only at h; rw [strictNat_eq] at h
    have hEv :
        Trie.get d (trieEv t) (Nat.div n 2) = some w →
        Nat.beq (Nat.mod n 2) 0 = true →
        Trie.get (d + 1) t (n + 1) = some w := by
      intro hs hn
      cases t with
      | leaf =>
        dsimp only [trieEv] at hs; rw [Trie.get_leaf] at hs; nomatch hs
      | node _ _ _ =>
        rw [Trie.get_succ]; dsimp only; rw [strictNat_eq, hn]; exact hs
    have hOd :
        Trie.get d (trieOd t) (Nat.div n 2) = some w →
        Nat.beq (Nat.mod n 2) 0 = false →
        Trie.get (d + 1) t (n + 1) = some w := by
      intro hs hn
      cases t with
      | leaf =>
        dsimp only [trieOd] at hs; rw [Trie.get_leaf] at hs; nomatch hs
      | node _ _ _ =>
        rw [Trie.get_succ]; dsimp only; rw [strictNat_eq, hn]; exact hs
    cases hm : Nat.beq (Nat.mod m 2) 0 with
    | true =>
      rw [hm] at h; dsimp only at h
      rw [strictTrie_eq, Trie.get_succ] at h; dsimp only at h
      rw [strictNat_eq] at h
      cases hn : Nat.beq (Nat.mod n 2) 0 with
      | true =>
        rw [hn] at h; dsimp only at h
        cases Trie.get_set_inv d (trieEv t) (Nat.div m 2) v (Nat.div n 2) w h with
        | inl e =>
          exact Or.inl
            ⟨congrArg Nat.succ (div2_mod2_inj m n e.1
              (by rw [eq_of_nat_beq _ 0 hn, eq_of_nat_beq _ 0 hm])), e.2⟩
        | inr o => exact Or.inr (hEv o hn)
      | false =>
        rw [hn] at h; dsimp only at h; exact Or.inr (hOd h hn)
    | false =>
      rw [hm] at h; dsimp only at h
      rw [strictTrie_eq, Trie.get_succ] at h; dsimp only at h
      rw [strictNat_eq] at h
      cases hn : Nat.beq (Nat.mod n 2) 0 with
      | true =>
        rw [hn] at h; dsimp only at h; exact Or.inr (hEv h hn)
      | false =>
        rw [hn] at h; dsimp only at h
        cases Trie.get_set_inv d (trieOd t) (Nat.div m 2) v (Nat.div n 2) w h with
        | inl e =>
          exact Or.inl
            ⟨congrArg Nat.succ (div2_mod2_inj m n e.1
              (by rw [mod2_eq_one_of_beq_zero_false n hn,
                      mod2_eq_one_of_beq_zero_false m hm])), e.2⟩
        | inr o => exact Or.inr (hOd o hn)

theorem Trie.get_erase_inv {α : Type} :
    ∀ (d : Nat) (t : Trie α) (k q : Nat) (w : α),
      Trie.get d (Trie.erase d t k) q = some w →
      Trie.get d t q = some w
  | 0, _, _, _, _, h => nomatch h
  | _ + 1, .leaf, _, _, _, h => by
    rw [Trie.erase_succ, Trie.get_leaf] at h; nomatch h
  | _ + 1, .node _ _ _, 0, 0, _, h => by
    rw [Trie.erase_succ, Trie.get_succ] at h; nomatch h
  | d + 1, .node _ _ _, 0, _ + 1, _, h => by
    rw [Trie.erase_succ, Trie.get_succ] at h; rw [Trie.get_succ]; exact h
  | d + 1, .node _ _ _, m + 1, 0, _, h => by
    rw [Trie.erase_succ] at h; dsimp only at h; rw [strictNat_eq] at h
    cases hm : Nat.beq (Nat.mod m 2) 0 <;>
      (rw [hm] at h; dsimp only at h
       rw [strictTrie_eq, Trie.get_succ] at h
       rw [Trie.get_succ]; exact h)
  | d + 1, .node _ ev0 od0, m + 1, n + 1, w, h => by
    rw [Trie.erase_succ] at h; dsimp only at h; rw [strictNat_eq] at h
    rw [Trie.get_succ]; dsimp only; rw [strictNat_eq]
    cases hm : Nat.beq (Nat.mod m 2) 0 with
    | true =>
      rw [hm] at h; dsimp only at h
      rw [strictTrie_eq, Trie.get_succ] at h; dsimp only at h
      rw [strictNat_eq] at h
      cases hn : Nat.beq (Nat.mod n 2) 0 with
      | true =>
        rw [hn] at h; dsimp only at h; dsimp only
        exact Trie.get_erase_inv d ev0 (Nat.div m 2) (Nat.div n 2) w h
      | false => rw [hn] at h; dsimp only at h; dsimp only; exact h
    | false =>
      rw [hm] at h; dsimp only at h
      rw [strictTrie_eq, Trie.get_succ] at h; dsimp only at h
      rw [strictNat_eq] at h
      cases hn : Nat.beq (Nat.mod n 2) 0 with
      | true => rw [hn] at h; dsimp only at h; dsimp only; exact h
      | false =>
        rw [hn] at h; dsimp only at h; dsimp only
        exact Trie.get_erase_inv d od0 (Nat.div m 2) (Nat.div n 2) w h

/-! ## 2. CNF Semantics & RUP/LRAT Checker (`checkRupProof_sound`) -/

abbrev Valuation := Nat → Bool
abbrev Clause := List Nat

def mkLit (varId : Nat) (isPos : Bool) : Nat :=
  match isPos with
  | true => 2 * varId
  | false => 2 * varId + 1

def litVar (lit : Nat) : Nat := Nat.div lit 2
def litPos (lit : Nat) : Bool := Nat.beq (Nat.land lit 1) 0

def evalLit (σ : Valuation) (lit : Nat) : Bool :=
  boolBeq (σ (litVar lit)) (litPos lit)

def evalClause (σ : Valuation) (cls : Clause) : Bool :=
  List.foldr (fun lit acc => boolOr (evalLit σ lit) acc) false cls

theorem evalClause_cons (σ : Valuation) (lit : Nat) (rest : Clause) :
    evalClause σ (lit :: rest) =
      boolOr (evalLit σ lit) (evalClause σ rest) := rfl

def evalCnf (σ : Valuation) (cnf : List Clause) : Bool :=
  List.foldr (fun cls acc => boolAnd (evalClause σ cls) acc) true cnf

theorem evalCnf_cons (σ : Valuation) (cls : Clause) (rest : List Clause) :
    evalCnf σ (cls :: rest) =
      boolAnd (evalClause σ cls) (evalCnf σ rest) := rfl

def UnsatCnf (cnf : List Clause) : Prop :=
  ∀ (σ : Valuation), evalCnf σ cnf = false

inductive ClauseRupState where
  | allFalse
  | unit (uLit : Nat)
  | satOrMulti

def stepLitRUP (depth : Nat) (assign : Trie Bool) (lit : Nat)
    (sub : ClauseRupState) : ClauseRupState :=
  match Trie.get depth assign (litVar lit) with
  | some val =>
    match boolBeq val (litPos lit) with
    | true => .satOrMulti
    | false => sub
  | none =>
    match sub with
    | .allFalse => .unit lit
    | .unit _ => .satOrMulti
    | .satOrMulti => .satOrMulti

def evalClauseRUP (depth : Nat) (assign : Trie Bool) (cls : Clause) :
    ClauseRupState :=
  List.foldr (stepLitRUP depth assign) .allFalse cls

theorem evalClauseRUP_cons (depth : Nat) (assign : Trie Bool) (lit : Nat)
    (rest : Clause) :
    evalClauseRUP depth assign (lit :: rest) =
      stepLitRUP depth assign lit (evalClauseRUP depth assign rest) := rfl

inductive HintPropState where
  | prop (assign : Trie Bool)
  | conflict
  | invalidHint (badCid : Nat)

def stepRupHint (depth : Nat) (db : Trie Clause) (st : HintPropState)
    (cid : Nat) : HintPropState :=
  match st with
  | .conflict => .conflict
  | .invalidHint bad => .invalidHint bad
  | .prop a =>
    match Trie.get depth db cid with
    | none => .invalidHint cid
    | some cls =>
      match evalClauseRUP depth a cls with
      | .allFalse => .conflict
      | .satOrMulti => .invalidHint cid
      | .unit uLit =>
        strictNat (litVar uLit) (fun v =>
          strictTrie (Trie.set depth a v (litPos uLit)) (fun a' => .prop a'))

def initRupAssign (depth : Nat) (target : Clause) : Trie Bool :=
  List.foldr
    (fun lit acc =>
      strictNat (litVar lit) (fun v =>
        strictTrie (Trie.set depth acc v (boolNot (litPos lit)))
          (fun a' => a')))
    Trie.leaf target

theorem initRupAssign_nil (depth : Nat) :
    initRupAssign depth [] = Trie.leaf := rfl

theorem initRupAssign_cons (depth : Nat) (lit : Nat) (rest : Clause) :
    initRupAssign depth (lit :: rest) =
      strictNat (litVar lit) (fun v =>
        strictTrie (Trie.set depth (initRupAssign depth rest) v
          (boolNot (litPos lit))) (fun a' => a')) := rfl

def propagateHints (depth : Nat) (db : Trie Clause) (st : HintPropState)
    (hints : List Nat) : HintPropState :=
  listFoldl (stepRupHint depth db) st hints

def checkRupStep (depth : Nat) (db : Trie Clause) (target : Clause)
    (hints : List Nat) : HintPropState :=
  propagateHints depth db (.prop (initRupAssign depth target)) hints

inductive RupStep where
  | addRup (cid : Nat) (clause : Clause) (hints : List Nat)
  | del (cids : List Nat)

inductive RupVerdict where
  | unsatVerified
  | errBadHint (stepCid : Nat) (hintCid : Nat)
  | errNoConflict (stepCid : Nat)
  | errFinalNotEmpty

def loadCnfTrie (depth : Nat) (cnf : List Clause) : Trie Clause :=
  (listFoldl
    (fun (st : Nat × Trie Clause) cls =>
      match st with
      | (idx, db) =>
        strictNat (idx + 1) (fun idx' =>
          strictTrie (Trie.set depth db idx cls) (fun db' => (idx', db'))))
    (0, Trie.leaf) cnf).2

def eraseIdsTrie (depth : Nat) (db : Trie Clause) (cids : List Nat) :
    Trie Clause :=
  listFoldl (fun cur cid => strictTrie (Trie.erase depth cur cid) (fun t' => t'))
    db cids

inductive ProofLoopState where
  | active (db : Trie Clause) (derivedEmpty : Bool)
  | failedBadHint (stepCid : Nat) (hintCid : Nat)
  | failedNoConflict (stepCid : Nat)

def isEmptyClause (cls : Clause) : Bool :=
  match cls with | [] => true | _ :: _ => false

def stepRupProof (depth : Nat) (st : ProofLoopState) (step : RupStep) :
    ProofLoopState :=
  match st with
  | .failedBadHint s h => .failedBadHint s h
  | .failedNoConflict s => .failedNoConflict s
  | .active db gotEmpty =>
    match step with
    | .del cids => .active (eraseIdsTrie depth db cids) gotEmpty
    | .addRup cid cls hints =>
      match checkRupStep depth db cls hints with
      | .conflict =>
        strictTrie (Trie.set depth db cid cls)
          (fun db' => .active db' (boolOr gotEmpty (isEmptyClause cls)))
      | .invalidHint badCid => .failedBadHint cid badCid
      | .prop _ => .failedNoConflict cid

def checkRupProof (depth : Nat) (cnf : List Clause) (steps : List RupStep) :
    RupVerdict :=
  match listFoldl (stepRupProof depth)
          (.active (loadCnfTrie depth cnf) false) steps with
  | .failedBadHint s h => .errBadHint s h
  | .failedNoConflict s => .errNoConflict s
  | .active _ true => .unsatVerified
  | .active _ false => .errFinalNotEmpty

def AssignConsistent (depth : Nat) (σ : Valuation) (assign : Trie Bool) :
    Prop :=
  ∀ (v : Nat) (b : Bool), Trie.get depth assign v = some b → σ v = b

def DbEntailed (depth : Nat) (σ : Valuation) (db : Trie Clause) : Prop :=
  ∀ (cid : Nat) (cls : Clause),
    Trie.get depth db cid = some cls → evalClause σ cls = true

theorem initRupAssign_consistent (depth : Nat) (σ : Valuation) :
    ∀ (target : Clause),
      evalClause σ target = false →
      AssignConsistent depth σ (initRupAssign depth target)
  | [], _ => fun _ _ hGet => by
    rw [initRupAssign_nil, Trie.get_leaf] at hGet; nomatch hGet
  | lit :: rest, hFalse => by
    rw [evalClause_cons] at hFalse
    have hPair := boolOr_eq_false _ _ hFalse
    have ih := initRupAssign_consistent depth σ rest hPair.2
    have hVal := boolBeq_false_not _ _ hPair.1
    intro q w hGet
    rw [initRupAssign_cons, strictNat_eq, strictTrie_eq] at hGet
    cases Trie.get_set_inv depth (initRupAssign depth rest)
            (litVar lit) (boolNot (litPos lit)) q w hGet with
    | inl hEq => rw [hEq.1, hEq.2]; exact hVal
    | inr hOld => exact ih q w hOld

theorem evalClauseRUP_sound (depth : Nat) (σ : Valuation) (assign : Trie Bool)
    (hCons : AssignConsistent depth σ assign) :
    ∀ (cls : Clause),
      (evalClauseRUP depth assign cls = .allFalse →
        evalClause σ cls = false) ∧
      (∀ (uLit : Nat),
        evalClauseRUP depth assign cls = .unit uLit →
        evalClause σ cls = true →
        evalLit σ uLit = true)
  | [] => ⟨(fun _ => rfl), (fun _ hUnit _ => nomatch hUnit)⟩
  | lit :: rest => by
    have ih := evalClauseRUP_sound depth σ assign hCons rest
    rw [evalClauseRUP_cons]
    dsimp only [stepLitRUP]
    cases hGet : Trie.get depth assign (litVar lit) with
    | some val =>
      have hSigma := hCons (litVar lit) val hGet
      dsimp only
      cases hMatch : boolBeq val (litPos lit) with
      | true =>
        dsimp only
        exact ⟨(fun h => nomatch h), (fun _ h _ => nomatch h)⟩
      | false =>
        dsimp only
        have hLF : evalLit σ lit = false := by
          dsimp only [evalLit]; rw [hSigma]; exact hMatch
        exact
          ⟨(fun hA => by rw [evalClause_cons, hLF]; exact ih.1 hA),
           (fun u hU hC => by
             rw [evalClause_cons, hLF] at hC
             exact ih.2 u hU hC)⟩
    | none =>
      dsimp only
      cases hSub : evalClauseRUP depth assign rest with
      | allFalse =>
        dsimp only
        have hRF := ih.1 hSub
        constructor
        · intro h; nomatch h
        · intro uLit hUnit hClsTrue
          injection hUnit with hEq
          rw [← hEq]
          rw [evalClause_cons, hRF] at hClsTrue
          cases hL : evalLit σ lit with
          | true => rfl
          | false => rw [hL] at hClsTrue; nomatch hClsTrue
      | unit _ =>
        dsimp only; exact ⟨(fun h => nomatch h), (fun _ h _ => nomatch h)⟩
      | satOrMulti =>
        dsimp only; exact ⟨(fun h => nomatch h), (fun _ h _ => nomatch h)⟩

theorem propagateHints_no_conflict (depth : Nat) (σ : Valuation)
    (db : Trie Clause) (hDb : DbEntailed depth σ db) :
    ∀ (hints : List Nat) (a : Trie Bool),
      AssignConsistent depth σ a →
      propagateHints depth db (.prop a) hints = .conflict → False
  | [], _, _, h => nomatch h
  | cid :: rest, a, hCons, hRun => by
    dsimp only [propagateHints] at hRun
    rw [listFoldl_cons] at hRun
    dsimp only [stepRupHint] at hRun
    have hStick :
        ∀ (hs : List Nat) (bad : Nat),
          listFoldl (stepRupHint depth db) (.invalidHint bad) hs =
            .invalidHint bad := by
      intro hs bad
      induction hs with
      | nil => rfl
      | cons _ _ ih => rw [listFoldl_cons]; dsimp only [stepRupHint]; exact ih
    cases hLookup : Trie.get depth db cid with
    | none => rw [hLookup, hStick rest cid] at hRun; nomatch hRun
    | some cls =>
      rw [hLookup] at hRun; dsimp only at hRun
      have hClsTrue := hDb cid cls hLookup
      have hRup := evalClauseRUP_sound depth σ a hCons cls
      cases hEv : evalClauseRUP depth a cls with
      | allFalse =>
        have hF := hRup.1 hEv
        rw [hClsTrue] at hF
        nomatch hF
      | unit uLit =>
        rw [hEv] at hRun; dsimp only at hRun
        rw [strictNat_eq, strictTrie_eq] at hRun
        have hUS := boolBeq_true_eq _ _ (hRup.2 uLit hEv hClsTrue)
        have hCons' :
            AssignConsistent depth σ
              (Trie.set depth a (litVar uLit) (litPos uLit)) := by
          intro q w hGet
          cases Trie.get_set_inv depth a (litVar uLit) (litPos uLit) q w hGet with
          | inl hEq => rw [hEq.1, hEq.2]; exact hUS
          | inr hOld => exact hCons q w hOld
        exact propagateHints_no_conflict depth σ db hDb rest _ hCons' hRun
      | satOrMulti =>
        rw [hEv] at hRun; dsimp only at hRun
        rw [hStick rest cid] at hRun; nomatch hRun

theorem checkRupStep_sound (depth : Nat) (σ : Valuation) (db : Trie Clause)
    (hDb : DbEntailed depth σ db) (target : Clause) (hints : List Nat)
    (hOk : checkRupStep depth db target hints = .conflict) :
    evalClause σ target = true := by
  cases hEval : evalClause σ target with
  | true => rfl
  | false =>
    exact False.elim
      (propagateHints_no_conflict depth σ db hDb hints _
        (initRupAssign_consistent depth σ target hEval) hOk)

theorem loadCnfTrie_aux (depth : Nat) (σ : Valuation) :
    ∀ (cs : List Clause) (idx : Nat) (db : Trie Clause),
      evalCnf σ cs = true →
      DbEntailed depth σ db →
      DbEntailed depth σ
        (listFoldl
          (fun (st : Nat × Trie Clause) cls =>
            match st with
            | (i, t) =>
              strictNat (i + 1) (fun i' =>
                strictTrie (Trie.set depth t i cls) (fun t' => (i', t'))))
          (idx, db) cs).2
  | [], _, _, _, hDb => hDb
  | cls :: rest, idx, db, hCnf, hDb => by
    rw [evalCnf_cons] at hCnf
    have hPair := boolAnd_eq_true _ _ hCnf
    rw [listFoldl_cons]; dsimp only; rw [strictNat_eq, strictTrie_eq]
    have hDb' : DbEntailed depth σ (Trie.set depth db idx cls) := by
      intro q w hGet
      cases Trie.get_set_inv depth db idx cls q w hGet with
      | inl hEq => rw [hEq.2]; exact hPair.1
      | inr hOld => exact hDb q w hOld
    exact loadCnfTrie_aux depth σ rest (idx + 1) (Trie.set depth db idx cls)
      hPair.2 hDb'

theorem eraseIdsTrie_entailed (depth : Nat) (σ : Valuation) :
    ∀ (cids : List Nat) (db : Trie Clause),
      DbEntailed depth σ db →
      DbEntailed depth σ (eraseIdsTrie depth db cids)
  | [], _, hDb => hDb
  | cid :: rest, db, hDb => by
    dsimp only [eraseIdsTrie]
    rw [listFoldl_cons, strictTrie_eq]
    exact eraseIdsTrie_entailed depth σ rest _
      (fun q w hGet => hDb q w (Trie.get_erase_inv depth db cid q w hGet))

theorem proofLoop_preserves_nonempty (depth : Nat) (σ : Valuation) :
    ∀ (steps : List RupStep) (db dbFinal : Trie Clause),
      DbEntailed depth σ db →
      listFoldl (stepRupProof depth) (.active db false) steps ≠
        .active dbFinal true
  | [], _, _, _ => fun h => nomatch h
  | step :: rest, db, dbFinal, hDb => by
    have hSB :
        ∀ (ss : List RupStep) (s hId : Nat),
          listFoldl (stepRupProof depth) (.failedBadHint s hId) ss ≠
            .active dbFinal true := by
      intro ss s hId
      induction ss with
      | nil => intro h; nomatch h
      | cons _ _ ih => rw [listFoldl_cons]; dsimp only [stepRupProof]; exact ih
    have hSN :
        ∀ (ss : List RupStep) (s : Nat),
          listFoldl (stepRupProof depth) (.failedNoConflict s) ss ≠
            .active dbFinal true := by
      intro ss s
      induction ss with
      | nil => intro h; nomatch h
      | cons _ _ ih => rw [listFoldl_cons]; dsimp only [stepRupProof]; exact ih
    intro h
    rw [listFoldl_cons] at h
    cases step with
    | del cids =>
      dsimp only [stepRupProof] at h
      exact proofLoop_preserves_nonempty depth σ rest _ dbFinal
        (eraseIdsTrie_entailed depth σ cids db hDb) h
    | addRup cid cls hints =>
      dsimp only [stepRupProof] at h
      cases hStep : checkRupStep depth db cls hints with
      | conflict =>
        rw [hStep] at h; dsimp only at h; rw [strictTrie_eq] at h
        have hCls := checkRupStep_sound depth σ db hDb cls hints hStep
        have hNE : isEmptyClause cls = false := by
          cases cls with
          | nil => nomatch hCls
          | cons _ _ => rfl
        rw [hNE] at h; dsimp only [boolOr] at h
        have hDb' : DbEntailed depth σ (Trie.set depth db cid cls) := by
          intro q w hGet
          cases Trie.get_set_inv depth db cid cls q w hGet with
          | inl hEq => rw [hEq.2]; exact hCls
          | inr hOld => exact hDb q w hOld
        exact proofLoop_preserves_nonempty depth σ rest _ dbFinal hDb' h
      | invalidHint bad =>
        rw [hStep] at h; dsimp only at h; exact hSB rest cid bad h
      | prop _ =>
        rw [hStep] at h; dsimp only at h; exact hSN rest cid h

/-- Master RUP/LRAT Soundness Theorem (`[propext]` only, `0` `._unsafe_rec`). -/
theorem checkRupProof_sound (depth : Nat) (cnf : List Clause)
    (steps : List RupStep)
    (hOk : checkRupProof depth cnf steps = .unsatVerified) :
    UnsatCnf cnf := by
  intro σ
  cases hCnf : evalCnf σ cnf with
  | false => rfl
  | true =>
    have hEmptyDb : DbEntailed depth σ Trie.leaf := by
      intro q _ hGet; rw [Trie.get_leaf] at hGet; nomatch hGet
    have hInitDb := loadCnfTrie_aux depth σ cnf 0 Trie.leaf hCnf hEmptyDb
    dsimp only [checkRupProof] at hOk
    cases hLoop :
        listFoldl (stepRupProof depth)
          (.active (loadCnfTrie depth cnf) false) steps with
    | failedBadHint _ _ => rw [hLoop] at hOk; nomatch hOk
    | failedNoConflict _ => rw [hLoop] at hOk; nomatch hOk
    | active dbF gotEmpty =>
      rw [hLoop] at hOk
      cases gotEmpty with
      | false => nomatch hOk
      | true =>
        exact False.elim
          (proofLoop_preserves_nonempty depth σ steps _ dbF hInitDb hLoop)

/-! ## 3. Built-In Positive & Negative Canaries -/

def sampleUnsatCnf : List Clause :=
  [ [mkLit 0 true]
  , [mkLit 0 false, mkLit 1 true, mkLit 2 true]
  , [mkLit 1 false, mkLit 3 true]
  , [mkLit 2 false, mkLit 3 true]
  , [mkLit 3 false]
  ]

def sampleUnsatSteps : List RupStep :=
  [ .addRup 5 [mkLit 3 true] [0, 2, 3, 1]
  , .del [0, 1, 2, 3]
  , .addRup 6 [] [5, 4]
  ]

theorem sampleUnsat_verified : UnsatCnf sampleUnsatCnf :=
  checkRupProof_sound 6 sampleUnsatCnf sampleUnsatSteps rfl

theorem sampleForgedHint_rejected :
    checkRupProof 6 sampleUnsatCnf [.addRup 5 [mkLit 3 true] [99, 0]] =
      .errBadHint 5 99 := rfl

end Workbench.Pass1.BitTrieLrat
