import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Scalars
import Anneal.Memory
import Anneal.UnsafeObligations
import Anneal.SepLogic
import Anneal.Rustc.V2026_06_01.Lower

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
Append-only `SymTable` GVN with monotone evaluation and peepholes, `CanonLocals` /
`CanonState` canonical MIR state, and CPS spine forcing.
-/

/-!
## Section 1 — Append-Only `SymTable` GVN & Monotone Evaluation
-/

/-- Symbolic value identifier indexing into an append-only `SymTable`. -/
abbrev SymId := Nat

/-- Concrete environment mapping symbolic input variable indices to 64-bit scalar words. -/
abbrev SymEnv := Nat → Nat

/-- 64-bit word modulus $2^{64}$ used for bounded modular arithmetic operations. -/
def word64Modulus : Nat := 18446744073709551616

/-- Unary symbolic operations in `SymNode`. -/
inductive SymOp1 where
  | id
  | boolNot
  | wrappingNeg64
  | maskLow32
  | xorConst (mask : Nat)
  | addConst (delta : Nat)
  deriving DecidableEq

/-- Binary symbolic operations in `SymNode`. -/
inductive SymOp2 where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | eq
  | lt
  | le
  deriving DecidableEq

/-- Hash-consed symbolic DAG node. Child operands reference earlier `SymId` (`Nat`)
    entries in the append-only `SymTable`. -/
inductive SymNode where
  | const (val : Nat)
  | var (inputIdx : Nat)
  | op1 (op : SymOp1) (arg : Nat)
  | op2 (op : SymOp2) (lhs rhs : Nat)
  | ite (cond thenBr elseBr : Nat)
  deriving DecidableEq

/-- Reduce a natural number to a 64-bit machine word (`v mod 2^64`). Every value produced by
    `SymNode` / `ExprTree` / MIR evaluation is passed through `wrap64` (or is a `0`/`1` flag),
    so all symbolic and concrete values are genuine `u64` words (`evalSymId_lt_word64`). -/
def wrap64 (v : Nat) : Nat := v % word64Modulus

theorem wrap64_lt (v : Nat) : wrap64 v < word64Modulus :=
  Nat.mod_lt v (by decide)

/-- Concrete evaluation of unary operations (`u64` wrapping semantics). -/
def evalSymOp1 (op : SymOp1) (v : Nat) : Nat :=
  match op with
  | .id => v
  | .boolNot => if v == 0 then 1 else 0
  | .wrappingNeg64 => (word64Modulus - (v % word64Modulus)) % word64Modulus
  | .maskLow32 => v % 4294967296
  | .xorConst mask => wrap64 (Nat.xor v mask)
  | .addConst delta => wrap64 (v + delta)

/-- Concrete evaluation of binary operations with Rust `u64` `wrapping_*` semantics
    (`add`/`sub`/`mul`/`shl` wrap modulo `2^64`; `sub` is `wrapping_sub`, **not** truncated
    `Nat` subtraction; shift amounts are masked to `b % 64` like Rust's `wrapping_shl`). -/
def evalSymOp2 (op : SymOp2) (a b : Nat) : Nat :=
  match op with
  | .add => wrap64 (a + b)
  | .sub => wrap64 (a + (word64Modulus - b % word64Modulus))
  | .mul => wrap64 (a * b)
  | .bitAnd => wrap64 (Nat.land a b)
  | .bitOr => wrap64 (Nat.lor a b)
  | .bitXor => wrap64 (Nat.xor a b)
  | .shl => wrap64 (Nat.shiftLeft a (b % 64))
  | .shr => wrap64 (Nat.shiftRight a (b % 64))
  | .eq => if a == b then 1 else 0
  | .lt => if decide (a < b) then 1 else 0
  | .le => if decide (a ≤ b) then 1 else 0

/-- Non-vacuity witnesses for `u64` wrapping semantics (`u64::MAX + 1 = 0`,
    `3.wrapping_sub(5) = 2^64 - 2`, `(2^63) << 1 = 0`). -/
theorem evalSymOp2_wrapping_witness :
    evalSymOp2 .add 18446744073709551615 1 = 0 ∧
      evalSymOp2 .sub 3 5 = 18446744073709551614 ∧
      evalSymOp2 .shl 9223372036854775808 1 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Boolean check that all child `SymId`s in a `SymNode` are strictly below `bound`. -/
def validNodeB (bound : Nat) : SymNode → Bool
  | .const _ => true
  | .var _ => true
  | .op1 _ a => decide (a < bound)
  | .op2 _ a b => decide (a < bound) && decide (b < bound)
  | .ite c t e => decide (c < bound) && decide (t < bound) && decide (e < bound)

/-- Propositional well-formedness of a `SymNode` at table bound `bound`: every
    child `SymId` is strictly less than `bound`, enforcing a strict topological DAG. -/
def ValidNode (bound : Nat) (node : SymNode) : Prop :=
  match node with
  | .const _ => True
  | .var _ => True
  | .op1 _ a => a < bound
  | .op2 _ a b => a < bound ∧ b < bound
  | .ite c t e => c < bound ∧ t < bound ∧ e < bound

theorem validNode_iff_validNodeB (bound : Nat) (node : SymNode) :
    ValidNode bound node ↔ validNodeB bound node = true := by
  cases node with
  | const _ => simp [ValidNode, validNodeB]
  | var _ => simp [ValidNode, validNodeB]
  | op1 _ a => simp [ValidNode, validNodeB]
  | op2 _ a b => simp [ValidNode, validNodeB, Bool.and_eq_true]
  | ite c t e => simp [ValidNode, validNodeB, Bool.and_eq_true, and_assoc]

theorem ValidNode.mono {b₁ b₂ : Nat} {node : SymNode} (h : ValidNode b₁ node) (hle : b₁ ≤ b₂) :
    ValidNode b₂ node := by
  cases node with
  | const _ => trivial
  | var _ => trivial
  | op1 _ a =>
    exact Nat.lt_of_lt_of_le h hle
  | op2 _ a b =>
    exact ⟨Nat.lt_of_lt_of_le h.1 hle, Nat.lt_of_lt_of_le h.2 hle⟩
  | ite c t e =>
    exact ⟨Nat.lt_of_lt_of_le h.1 hle, Nat.lt_of_lt_of_le h.2.1 hle, Nat.lt_of_lt_of_le h.2.2 hle⟩

/-- Append-only Global Value Numbering (`SymTable`) table storing `SymNode`s in
    topological creation order. -/
structure SymTable where
  nodes : List SymNode := []
  deriving DecidableEq

/-- A `SymTable` is valid when every node at index `idx` only references strictly
    earlier `SymId`s `< idx`. -/
def ValidTable (tbl : SymTable) : Prop :=
  ∀ (idx : Nat) (node : SymNode), tbl.nodes[idx]? = some node → ValidNode idx node

theorem ValidTable.empty : ValidTable { nodes := [] } := by
  intro idx node h
  simp at h

/-- Structural monotonicity (`Extends`): `tbl₂` extends `tbl₁` when every index
    valid in `tbl₁` maps to the exact same `SymNode` in `tbl₂`. -/
def SymTable.Extends (tbl₁ tbl₂ : SymTable) : Prop :=
  ∀ (idx : Nat) (node : SymNode), tbl₁.nodes[idx]? = some node → tbl₂.nodes[idx]? = some node

theorem SymTable.Extends.refl (tbl : SymTable) : tbl.Extends tbl := by
  intro idx node h
  exact h

theorem SymTable.Extends.trans {tbl₁ tbl₂ tbl₃ : SymTable}
    (h₁₂ : tbl₁.Extends tbl₂) (h₂₃ : tbl₂.Extends tbl₃) :
    tbl₁.Extends tbl₃ := by
  intro idx node h
  exact h₂₃ idx node (h₁₂ idx node h)

theorem getElem?_append_left_of_some {α : Type} {xs ys : List α} {idx : Nat} {v : α}
    (h : xs[idx]? = some v) :
    (xs ++ ys)[idx]? = some v := by
  have hlt : idx < xs.length := by
    cases hlt' : decide (idx < xs.length) with
    | true => exact of_decide_eq_true hlt'
    | false =>
      have hge : xs.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt')
      rw [List.getElem?_eq_none hge] at h
      cases h
  rw [List.getElem?_append_left hlt]
  exact h

theorem SymTable.extends_append (tbl : SymTable) (extra : List SymNode) :
    tbl.Extends { nodes := tbl.nodes ++ extra } := by
  intro idx node h
  exact getElem?_append_left_of_some h

theorem SymTable.Extends.length_le {tbl₁ tbl₂ : SymTable}
    (hExt : tbl₁.Extends tbl₂) : tbl₁.nodes.length ≤ tbl₂.nodes.length := by
  cases h : tbl₁.nodes.length with
  | zero => exact Nat.zero_le _
  | succ k =>
    have hlt : k < tbl₁.nodes.length := by omega
    have hSome : tbl₁.nodes[k]? = some tbl₁.nodes[k] := List.getElem?_eq_getElem hlt
    have hSome₂ := hExt k tbl₁.nodes[k] hSome
    cases hlt₂ : decide (k < tbl₂.nodes.length) with
    | true =>
      have hk : k < tbl₂.nodes.length := of_decide_eq_true hlt₂
      omega
    | false =>
      have hge : tbl₂.nodes.length ≤ k := Nat.le_of_not_lt (of_decide_eq_false hlt₂)
      rw [List.getElem?_eq_none hge] at hSome₂
      cases hSome₂

/-- Evaluate a single `SymNode` given an evaluator `evalChild` for child `SymId`s. -/
def evalSymNodeWith (evalChild : SymId → Nat) (env : SymEnv) : SymNode → Nat
  | .const v => wrap64 v
  | .var idx => wrap64 (env idx)
  | .op1 op a => evalSymOp1 op (evalChild a)
  | .op2 op a b => evalSymOp2 op (evalChild a) (evalChild b)
  | .ite c t e => if evalChild c != 0 then evalChild t else evalChild e

/-- Fuel-bounded structural evaluation of a `SymId` in `tbl`.
    `evalSymId tbl env id` sets `fuel = id + 1`, which depends ONLY on `id`
    and NOT on `tbl.nodes.length`. Because every valid node at `idx` only references
    children `< idx`, `id + 1` steps of fuel always suffice and `evalSymId_mono` holds
    directly across table extensions without fuel-shifting boilerplate. -/
def evalSymIdAux (tbl : SymTable) (env : SymEnv) : Nat → SymId → Nat
  | 0, _ => 0
  | fuel + 1, id =>
    match tbl.nodes[id]? with
    | none => 0
    | some node => evalSymNodeWith (evalSymIdAux tbl env fuel) env node

/-- Evaluate `id : SymId` in `tbl` under concrete input environment `env`. -/
def evalSymId (tbl : SymTable) (env : SymEnv) (id : SymId) : Nat :=
  evalSymIdAux tbl env (id + 1) id

/-- Monotonicity of `evalSymIdAux` across `SymTable.Extends`. -/
theorem evalSymIdAux_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) :
    ∀ (fuel : Nat) (id : SymId),
      id < tbl₁.nodes.length →
      evalSymIdAux tbl₁ env fuel id = evalSymIdAux tbl₂ env fuel id
  | 0, _, _ => rfl
  | fuel + 1, id, hlt => by
    have hSome₁ : tbl₁.nodes[id]? = some tbl₁.nodes[id] := List.getElem?_eq_getElem hlt
    have hSome₂ : tbl₂.nodes[id]? = some tbl₁.nodes[id] := hExt id tbl₁.nodes[id] hSome₁
    have hNodeValid : ValidNode id tbl₁.nodes[id] := hValid id tbl₁.nodes[id] hSome₁
    dsimp [evalSymIdAux]
    rw [hSome₁, hSome₂]
    dsimp
    cases hNode : tbl₁.nodes[id] with
    | const v => rfl
    | var idx => rfl
    | op1 op a =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel a (Nat.lt_trans hNodeValid hlt)]
    | op2 op a b =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel a (Nat.lt_trans hNodeValid.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel b (Nat.lt_trans hNodeValid.2 hlt)]
    | ite c t e =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel c (Nat.lt_trans hNodeValid.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel t (Nat.lt_trans hNodeValid.2.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel e (Nat.lt_trans hNodeValid.2.2 hlt)]

/-- **Core Monotonicity Theorem (`evalSymId_mono`)**:
    Extending an append-only `SymTable` preserves the concrete evaluation of every
    previously allocated `SymId`. -/
theorem evalSymId_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {id : SymId}
    (hlt : id < tbl₁.nodes.length) :
    evalSymId tbl₁ env id = evalSymId tbl₂ env id :=
  evalSymIdAux_mono hValid hExt env (id + 1) id hlt

/-- Fuel-sufficiency theorem: in a `ValidTable`, any fuel `> id` evaluates `id`
    to the exact same value. -/
theorem evalSymIdAux_fuel_irrel {tbl : SymTable} (hValid : ValidTable tbl) (env : SymEnv) :
    ∀ (bound id fuel₁ fuel₂ : Nat),
      id < bound →
      id < tbl.nodes.length →
      id < fuel₁ →
      id < fuel₂ →
      evalSymIdAux tbl env fuel₁ id = evalSymIdAux tbl env fuel₂ id
  | 0, _, _, _, hltB, _, _, _ => by omega
  | bound + 1, id, fuel₁, fuel₂, hltB, hltLen, hltF₁, hltF₂ => by
    cases fuel₁ with
    | zero => omega
    | succ f₁ =>
      cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        have hSome : tbl.nodes[id]? = some tbl.nodes[id] := List.getElem?_eq_getElem hltLen
        have hNodeValid : ValidNode id tbl.nodes[id] := hValid id tbl.nodes[id] hSome
        dsimp [evalSymIdAux]
        rw [hSome]
        dsimp
        cases hNode : tbl.nodes[id] with
        | const v => rfl
        | var idx => rfl
        | op1 op a =>
          rw [hNode] at hNodeValid
          have ha : a < id := hNodeValid
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound a f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
        | op2 op a b =>
          rw [hNode] at hNodeValid
          have ha : a < id := hNodeValid.1
          have hb : b < id := hNodeValid.2
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound a f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound b f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
        | ite c t e =>
          rw [hNode] at hNodeValid
          have hc : c < id := hNodeValid.1
          have ht : t < id := hNodeValid.2.1
          have he : e < id := hNodeValid.2.2
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound c f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound t f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound e f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]

theorem evalSymIdAux_eq_evalSymId {tbl : SymTable} (hValid : ValidTable tbl)
    (env : SymEnv) {id fuel : Nat} (hltLen : id < tbl.nodes.length) (hltFuel : id < fuel) :
    evalSymIdAux tbl env fuel id = evalSymId tbl env id :=
  evalSymIdAux_fuel_irrel hValid env (id + 1) id fuel (id + 1)
    (Nat.lt_succ_self id) hltLen hltFuel (Nat.lt_succ_self id)

/-- Unfolding equation for `evalSymId` at any valid index `id` in `tbl`. -/
theorem evalSymId_eq_evalSymNodeWith {tbl : SymTable} (hValid : ValidTable tbl)
    (env : SymEnv) {id : Nat} {node : SymNode}
    (hLookup : tbl.nodes[id]? = some node) :
    evalSymId tbl env id = evalSymNodeWith (evalSymId tbl env) env node := by
  have hltLen : id < tbl.nodes.length := by
    cases h : decide (id < tbl.nodes.length) with
    | true => exact of_decide_eq_true h
    | false =>
      rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false h))] at hLookup
      cases hLookup
  have hNodeValid : ValidNode id node := hValid id node hLookup
  change evalSymIdAux tbl env (id + 1) id = evalSymNodeWith (evalSymId tbl env) env node
  dsimp [evalSymIdAux]
  rw [hLookup]
  dsimp
  cases node with
  | const v => rfl
  | var idx => rfl
  | op1 op a =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid hltLen) hNodeValid]
  | op2 op a b =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.1 hltLen) hNodeValid.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2 hltLen) hNodeValid.2]
  | ite c t e =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.1 hltLen) hNodeValid.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2.1 hltLen) hNodeValid.2.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2.2 hltLen) hNodeValid.2.2]

theorem evalSymOp1_lt_word64 (op : SymOp1) {v : Nat} (hv : v < word64Modulus) :
    evalSymOp1 op v < word64Modulus := by
  cases op with
  | id => exact hv
  | boolNot =>
    dsimp only [evalSymOp1]
    split <;> decide
  | wrappingNeg64 => exact Nat.mod_lt _ (by decide)
  | maskLow32 =>
    dsimp only [evalSymOp1]
    have h := Nat.mod_lt v (show 4294967296 > 0 by decide)
    have h2 : (4294967296 : Nat) < word64Modulus := by decide
    omega
  | xorConst _ => exact wrap64_lt _
  | addConst _ => exact wrap64_lt _

theorem evalSymOp2_lt_word64 (op : SymOp2) (a b : Nat) : evalSymOp2 op a b < word64Modulus := by
  cases op <;> first
    | exact wrap64_lt _
    | (dsimp only [evalSymOp2]; split <;> decide)

/-- **`u64` Word Invariant (`evalSymId_lt_word64`)**: every `SymId` evaluates to a genuine
    64-bit word (`< 2^64`) in every table, environment and fuel. -/
theorem evalSymIdAux_lt_word64 (tbl : SymTable) (env : SymEnv) :
    ∀ (fuel : Nat) (id : SymId), evalSymIdAux tbl env fuel id < word64Modulus
  | 0, _ => by
    dsimp only [evalSymIdAux]
    decide
  | fuel + 1, id => by
    dsimp only [evalSymIdAux]
    split
    · decide
    · rename_i node _
      cases node with
      | const v => exact wrap64_lt v
      | var i => exact wrap64_lt (env i)
      | op1 op a => exact evalSymOp1_lt_word64 op (evalSymIdAux_lt_word64 tbl env fuel a)
      | op2 op a b => exact evalSymOp2_lt_word64 op _ _
      | ite c t e =>
        dsimp only [evalSymNodeWith]
        split
        · exact evalSymIdAux_lt_word64 tbl env fuel t
        · exact evalSymIdAux_lt_word64 tbl env fuel e

theorem evalSymId_lt_word64 (tbl : SymTable) (env : SymEnv) (id : SymId) :
    evalSymId tbl env id < word64Modulus :=
  evalSymIdAux_lt_word64 tbl env (id + 1) id

/-- Search `nodes` for an existing occurrence of `target`, returning its index if present. -/
def findNodeIdxAux (target : SymNode) (offset : Nat) : List SymNode → Option Nat
  | [] => none
  | n :: rest =>
    if n == target then
      some offset
    else
      findNodeIdxAux target (offset + 1) rest

def findNodeIdx (nodes : List SymNode) (target : SymNode) : Option Nat :=
  findNodeIdxAux target 0 nodes

theorem findNodeIdxAux_spec (target : SymNode) :
    ∀ (nodes : List SymNode) (offset idx : Nat),
      findNodeIdxAux target offset nodes = some idx →
      offset ≤ idx ∧ idx < offset + nodes.length ∧ nodes[idx - offset]? = some target
  | [], _, _, h => by cases h
  | n :: rest, offset, idx, h => by
    dsimp [findNodeIdxAux] at h
    split at h
    · rename_i hEq
      injection h with hIdx
      subst hIdx
      have hTarget : n = target := of_decide_eq_true hEq
      subst hTarget
      refine ⟨Nat.le_refl offset, by dsimp; omega, ?_⟩
      rw [Nat.sub_self]
      rfl
    · have ih := findNodeIdxAux_spec target rest (offset + 1) idx h
      refine ⟨by omega, by dsimp; omega, ?_⟩
      have hSub : idx - offset = (idx - (offset + 1)) + 1 := by omega
      rw [hSub]
      exact ih.2.2

theorem findNodeIdx_spec {nodes : List SymNode} {target : SymNode} {idx : Nat}
    (h : findNodeIdx nodes target = some idx) :
    idx < nodes.length ∧ nodes[idx]? = some target := by
  have hSpec := findNodeIdxAux_spec target nodes 0 idx h
  refine ⟨by omega, ?_⟩
  have hSub : idx - 0 = idx := Nat.sub_zero idx
  rw [← hSub]
  exact hSpec.2.2

theorem findNodeIdxAux_complete (target : SymNode) :
    ∀ (nodes : List SymNode) (offset i : Nat),
      nodes[i]? = some target →
      ∃ idx, findNodeIdxAux target offset nodes = some idx
  | [], _, _, h => by simp at h
  | n :: rest, offset, i, h => by
    dsimp [findNodeIdxAux]
    split
    · exact ⟨offset, rfl⟩
    · rename_i hNe
      cases i with
      | zero =>
        simp at h
        subst h
        exact False.elim (hNe (decide_eq_true rfl))
      | succ i' =>
        simp at h
        exact findNodeIdxAux_complete target rest (offset + 1) i' h

theorem findNodeIdx_complete {nodes : List SymNode} {target : SymNode} {i : Nat}
    (h : nodes[i]? = some target) :
    ∃ idx, findNodeIdx nodes target = some idx :=
  findNodeIdxAux_complete target nodes 0 i h

/-- Raw hash-consed interning without algebraic peephole rules: returns an existing
    `SymId` if `node` is already in `tbl.nodes`, or appends `node` at `tbl.nodes.length`. -/
def internRawNode (tbl : SymTable) (node : SymNode) : SymId × SymTable :=
  match findNodeIdx tbl.nodes node with
  | some idx => (idx, tbl)
  | none => (tbl.nodes.length, { nodes := tbl.nodes ++ [node] })

/-- Commutative binary operators: their operands are put in canonical `SymId` order before
    hash-consing, so `x + y` and `y + x` share one `SymId`. -/
def SymOp2.isComm : SymOp2 → Bool
  | .add | .mul | .bitAnd | .bitOr | .bitXor | .eq => true
  | _ => false

theorem evalSymOp2_comm {op : SymOp2} (hComm : op.isComm = true) (x y : Nat) :
    evalSymOp2 op x y = evalSymOp2 op y x := by
  cases op with
  | add => show wrap64 (x + y) = wrap64 (y + x); rw [Nat.add_comm]
  | mul => show wrap64 (x * y) = wrap64 (y * x); rw [Nat.mul_comm]
  | bitAnd =>
    show wrap64 (Nat.land x y) = wrap64 (Nat.land y x)
    rw [show Nat.land x y = Nat.land y x from Nat.and_comm x y]
  | bitOr =>
    show wrap64 (Nat.lor x y) = wrap64 (Nat.lor y x)
    rw [show Nat.lor x y = Nat.lor y x from Nat.or_comm x y]
  | bitXor =>
    show wrap64 (Nat.xor x y) = wrap64 (Nat.xor y x)
    rw [show Nat.xor x y = Nat.xor y x from Nat.xor_comm x y]
  | eq =>
    show (if decide (x = y) = true then 1 else 0) = (if decide (y = x) = true then 1 else 0)
    by_cases h : x = y
    · subst h
      rfl
    · rw [decide_eq_false h, decide_eq_false (Ne.symm h)]
  | sub => cases hComm
  | shl => cases hComm
  | shr => cases hComm
  | lt => cases hComm
  | le => cases hComm

/-- Table-independent algebraic peephole rewrite of a binary node (`peepholeOp2`):
    duplicate-operand folds `x & x ↦ x`, `x | x ↦ x`, `x ^ x ↦ 0`, `x - x ↦ 0`, `x < x ↦ 0`,
    `x == x ↦ 1`, `x ≤ x ↦ 1`, and canonical operand order for commutative operators.
    `.inl x` reuses an existing `SymId`; `.inr node'` hash-conses `node'`. -/
def peepholeOp2 (op : SymOp2) (a b : SymId) : SymId ⊕ SymNode :=
  if a = b then
    match op with
    | .bitAnd | .bitOr => .inl a
    | .bitXor | .sub | .lt => .inr (.const 0)
    | .eq | .le => .inr (.const 1)
    | _ => .inr (.op2 op a b)
  else if op.isComm && decide (b < a) then .inr (.op2 op b a)
  else .inr (.op2 op a b)

/-- **Peephole Soundness (`peepholeOp2_sound`)**: every rewrite preserves the `u64` value of the
    binary node for any child valuation `f` whose operand `a` is a 64-bit word. -/
theorem peepholeOp2_sound (op : SymOp2) (a b : SymId) (f : SymId → Nat) (env : SymEnv)
    (ha : f a < word64Modulus) :
    match peepholeOp2 op a b with
    | .inl x => f x = evalSymOp2 op (f a) (f b)
    | .inr node' => evalSymNodeWith f env node' = evalSymOp2 op (f a) (f b) := by
  unfold peepholeOp2
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left (rfl : a = a)]
    have hmod : f a % word64Modulus = f a := Nat.mod_eq_of_lt ha
    cases op with
    | add => rfl
    | mul => rfl
    | shl => rfl
    | shr => rfl
    | bitAnd =>
      show f a = wrap64 (Nat.land (f a) (f a))
      rw [show Nat.land (f a) (f a) = f a from Nat.and_self (f a)]
      exact hmod.symm
    | bitOr =>
      show f a = wrap64 (Nat.lor (f a) (f a))
      rw [show Nat.lor (f a) (f a) = f a from Nat.or_self (f a)]
      exact hmod.symm
    | bitXor =>
      show wrap64 0 = wrap64 (Nat.xor (f a) (f a))
      rw [show Nat.xor (f a) (f a) = 0 from Nat.xor_self (f a)]
    | sub =>
      show wrap64 0 = wrap64 (f a + (word64Modulus - f a % word64Modulus))
      rw [hmod, Nat.add_sub_cancel' (Nat.le_of_lt ha)]
      show 0 % word64Modulus = word64Modulus % word64Modulus
      rw [Nat.mod_self]
      rfl
    | lt =>
      show wrap64 0 = (if decide (f a < f a) = true then 1 else 0)
      rw [decide_eq_false (Nat.lt_irrefl (f a))]
      rfl
    | eq =>
      show wrap64 1 = (if decide (f a = f a) = true then 1 else 0)
      rw [decide_eq_true rfl]
      rfl
    | le =>
      show wrap64 1 = (if decide (f a ≤ f a) = true then 1 else 0)
      rw [decide_eq_true (Nat.le_refl (f a))]
      rfl
  · rw [ite_eq_right hab]
    by_cases hc : (op.isComm && decide (b < a)) = true
    · rw [ite_eq_left hc]
      have hComm : op.isComm = true := by
        cases h : op.isComm
        · rw [h] at hc
          cases hc
        · rfl
      exact evalSymOp2_comm hComm (f b) (f a)
    · rw [ite_eq_right hc]
      rfl

theorem peepholeOp2_valid {bound : Nat} {op : SymOp2} {a b : SymId}
    (h : ValidNode bound (.op2 op a b)) :
    match peepholeOp2 op a b with
    | .inl x => x < bound
    | .inr node' => ValidNode bound node' := by
  have ha : a < bound := h.1
  have hb : b < bound := h.2
  unfold peepholeOp2
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left (rfl : a = a)]
    cases op <;> first | exact ha | exact (⟨ha, ha⟩ : a < bound ∧ a < bound) | trivial
  · rw [ite_eq_right hab]
    by_cases hc : (op.isComm && decide (b < a)) = true
    · rw [ite_eq_left hc]
      exact (⟨hb, ha⟩ : b < bound ∧ a < bound)
    · rw [ite_eq_right hc]
      exact (⟨ha, hb⟩ : a < bound ∧ b < bound)

/-- Lookup-first binary interning: reuse an existing occurrence of the node verbatim, otherwise
    apply `peepholeOp2` and hash-cons the result. -/
def internOp2 (tbl : SymTable) (op : SymOp2) (a b : SymId) : SymId × SymTable :=
  match findNodeIdx tbl.nodes (.op2 op a b) with
  | some idx => (idx, tbl)
  | none =>
    match peepholeOp2 op a b with
    | .inl x => (x, tbl)
    | .inr node' => internRawNode tbl node'

theorem findNodeIdxAux_append_none (target x : SymNode) (hx : x ≠ target) :
    ∀ (nodes : List SymNode) (offset : Nat),
      findNodeIdxAux target offset nodes = none →
      findNodeIdxAux target offset (nodes ++ [x]) = none
  | [], offset, _ => by
    dsimp [findNodeIdxAux]
    have hne : (x == target) = false := by
      cases h : (x == target)
      · rfl
      · exact absurd (of_decide_eq_true h) hx
    rw [hne]
    rfl
  | n :: rest, offset, h => by
    dsimp [findNodeIdxAux] at h ⊢
    split at h
    · cases h
    · rename_i hn
      rw [ite_eq_right hn]
      exact findNodeIdxAux_append_none target x hx rest (offset + 1) h

theorem findNodeIdxAux_append_self (x : SymNode) :
    ∀ (nodes : List SymNode) (offset : Nat),
      findNodeIdxAux x offset nodes = none →
      findNodeIdxAux x offset (nodes ++ [x]) = some (offset + nodes.length)
  | [], offset, _ => by
    dsimp [findNodeIdxAux]
    rw [show (x == x) = true from decide_eq_true rfl]
    rfl
  | n :: rest, offset, h => by
    dsimp [findNodeIdxAux] at h ⊢
    split at h
    · cases h
    · rename_i hn
      rw [ite_eq_right hn, findNodeIdxAux_append_self x rest (offset + 1) h]
      congr 1
      omega

/-- Hash-consed GVN node interning with sound algebraic canonicalization:
    - Folds idempotent conditional branches `ite c x x ↦ x`, identity unary ops
      `op1 .id x ↦ x`, and zero-offset wrapping additions `op1 (.addConst 0) x ↦ x`
      (whose soundness in `internNode_eval` relies on the `u64` word bound
      `evalSymId_lt_word64 : evalSymId tbl env x < 2^64`) directly to existing `SymId` `x`
      without allocating a new node.
    - Interns binary nodes through `internOp2`: an existing occurrence is reused verbatim
      (lookup first), otherwise the table-independent `peepholeOp2` rewrite applies
      duplicate-operand folds (`x & x ↦ x`, `x | x ↦ x`, `x ^ x ↦ 0`, `x - x ↦ 0`,
      `x < x ↦ 0`, `x == x ↦ 1`, `x ≤ x ↦ 1`) and canonical commutative operand order.
    - Deduplicates any previously interned `SymNode` via `findNodeIdx`. -/
def internNode (tbl : SymTable) (node : SymNode) : SymId × SymTable :=
  match node with
  | .ite _ t e =>
    if t == e then
      (t, tbl)
    else
      internRawNode tbl node
  | .op1 .id a => (a, tbl)
  | .op1 (.xorConst mask) a =>
    if mask == 0 then
      (a, tbl)
    else
      internRawNode tbl node
  | .op1 (.addConst delta) a =>
    if delta == 0 then
      (a, tbl)
    else
      internRawNode tbl node
  | .op2 op a b => internOp2 tbl op a b
  | _ => internRawNode tbl node

theorem internRawNode_extends (tbl : SymTable) (node : SymNode) :
    tbl.Extends (internRawNode tbl node).2 := by
  dsimp [internRawNode]
  cases findNodeIdx tbl.nodes node with
  | some _ => exact SymTable.Extends.refl tbl
  | none => exact SymTable.extends_append tbl [node]

theorem internOp2_extends (tbl : SymTable) (op : SymOp2) (a b : SymId) :
    tbl.Extends (internOp2 tbl op a b).2 := by
  unfold internOp2
  split
  · exact SymTable.Extends.refl tbl
  · split
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl _

/-- **Monotone Extension Theorem (`internNode_extends`)**:
    `internNode` only appends to `tbl` (or leaves `tbl` unchanged on a GVN hit / fold). -/
theorem internNode_extends (tbl : SymTable) (node : SymNode) :
    tbl.Extends (internNode tbl node).2 := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp
    split
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl (.ite c t e)
  | op1 op a =>
    cases op <;> dsimp
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl (.op1 .boolNot a)
    · exact internRawNode_extends tbl (.op1 .wrappingNeg64 a)
    · exact internRawNode_extends tbl (.op1 .maskLow32 a)
    · rename_i mask
      split
      · exact SymTable.Extends.refl tbl
      · exact internRawNode_extends tbl (.op1 (.xorConst mask) a)
    · rename_i delta
      split
      · exact SymTable.Extends.refl tbl
      · exact internRawNode_extends tbl (.op1 (.addConst delta) a)
  | const v => exact internRawNode_extends tbl (.const v)
  | var idx => exact internRawNode_extends tbl (.var idx)
  | op2 op a b => exact internOp2_extends tbl op a b

theorem internRawNode_valid {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internRawNode tbl node).2 ∧
      (internRawNode tbl node).1 < (internRawNode tbl node).2.nodes.length := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    exact ⟨hValid, hSpec.1⟩
  | none =>
    refine ⟨?_, ?_⟩
    · intro idx n hGet
      cases hlt : decide (idx < tbl.nodes.length) with
      | true =>
        have hlt' : idx < tbl.nodes.length := of_decide_eq_true hlt
        rw [List.getElem?_append_left hlt'] at hGet
        exact hValid idx n hGet
      | false =>
        have hge : tbl.nodes.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt)
        rw [List.getElem?_append_right hge] at hGet
        cases hDiff : idx - tbl.nodes.length with
        | zero =>
          rw [hDiff] at hGet
          simp at hGet
          subst hGet
          have hIdxEq : idx = tbl.nodes.length := by omega
          rw [hIdxEq]
          exact hNode
        | succ k =>
          rw [hDiff] at hGet
          simp at hGet
    · simp

theorem internOp2_valid {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length (.op2 op a b)) :
    ValidTable (internOp2 tbl op a b).2 ∧
      (internOp2 tbl op a b).1 < (internOp2 tbl op a b).2.nodes.length := by
  unfold internOp2
  split
  · rename_i idx hFind
    exact ⟨hValid, (findNodeIdx_spec hFind).1⟩
  · have hPV := peepholeOp2_valid hNode
    split
    · rename_i x hP
      rw [hP] at hPV
      exact ⟨hValid, hPV⟩
    · rename_i node' hP
      rw [hP] at hPV
      exact internRawNode_valid hValid hPV

/-- **Table Validity Preservation (`internNode_valid`)**:
    Interning any node whose children are `< tbl.nodes.length` preserves `ValidTable`
    and returns a valid `SymId < tbl'.nodes.length`. -/
theorem internNode_valid {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internNode tbl node).2 ∧
      (internNode tbl node).1 < (internNode tbl node).2.nodes.length := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp [ValidNode] at hNode
    dsimp
    split
    · exact ⟨hValid, hNode.2.1⟩
    · exact internRawNode_valid hValid hNode
  | op1 op a =>
    dsimp [ValidNode] at hNode
    cases op <;> dsimp
    · exact ⟨hValid, hNode⟩
    · exact internRawNode_valid hValid hNode
    · exact internRawNode_valid hValid hNode
    · exact internRawNode_valid hValid hNode
    · split
      · exact ⟨hValid, hNode⟩
      · exact internRawNode_valid hValid hNode
    · split
      · exact ⟨hValid, hNode⟩
      · exact internRawNode_valid hValid hNode
  | const v => exact internRawNode_valid hValid hNode
  | var idx => exact internRawNode_valid hValid hNode
  | op2 op a b => exact internOp2_valid hValid hNode

theorem internRawNode_eval {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) (env : SymEnv) :
    let res := internRawNode tbl node
    evalSymId res.2 env res.1 = evalSymNodeWith (evalSymId tbl env) env node := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    exact evalSymId_eq_evalSymNodeWith hValid env hSpec.2
  | none =>
    have hValid' := (internRawNode_valid hValid hNode).1
    dsimp [internRawNode] at hValid'
    rw [hFind] at hValid'
    dsimp at hValid'
    have hExt : tbl.Extends { nodes := tbl.nodes ++ [node] } := SymTable.extends_append tbl [node]
    have hLookupNew : (tbl.nodes ++ [node])[tbl.nodes.length]? = some node := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [evalSymId_eq_evalSymNodeWith hValid' env hLookupNew]
    cases node with
    | const v => rfl
    | var idx => rfl
    | op1 op a =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode]
    | op2 op a b =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode.1]
      rw [← evalSymId_mono hValid hExt env hNode.2]
    | ite c t e =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode.1]
      rw [← evalSymId_mono hValid hExt env hNode.2.1]
      rw [← evalSymId_mono hValid hExt env hNode.2.2]

theorem internOp2_eval {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length (.op2 op a b)) (env : SymEnv) :
    evalSymId (internOp2 tbl op a b).2 env (internOp2 tbl op a b).1 =
      evalSymOp2 op (evalSymId tbl env a) (evalSymId tbl env b) := by
  unfold internOp2
  split
  · rename_i idx hFind
    exact evalSymId_eq_evalSymNodeWith hValid env (findNodeIdx_spec hFind).2
  · have hPS := peepholeOp2_sound op a b (evalSymId tbl env) env (evalSymId_lt_word64 tbl env a)
    have hPV := peepholeOp2_valid hNode
    split
    · rename_i x hP
      rw [hP] at hPS
      exact hPS
    · rename_i node' hP
      rw [hP] at hPS hPV
      rw [internRawNode_eval hValid hPV env]
      exact hPS

/-- **Evaluation Soundness of `internNode` (`internNode_eval`)**:
    Evaluating the `SymId` returned by `internNode tbl node` in the resulting table
    equals evaluating `node` over `evalSymId tbl env` (including when `ite c x x ↦ x`
    or `op1 .id x ↦ x` folds to an existing `SymId`). -/
theorem internNode_eval {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) (env : SymEnv) :
    let res := internNode tbl node
    evalSymId res.2 env res.1 = evalSymNodeWith (evalSymId tbl env) env node := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp
    split
    · rename_i hCond
      have hEqTE : t = e := of_decide_eq_true hCond
      subst hEqTE
      dsimp [evalSymNodeWith]
      cases (evalSymId tbl env c != 0) <;> rfl
    · exact internRawNode_eval hValid hNode env
  | op1 op a =>
    cases op <;> dsimp
    · dsimp [evalSymNodeWith, evalSymOp1]
    · exact internRawNode_eval hValid hNode env
    · exact internRawNode_eval hValid hNode env
    · exact internRawNode_eval hValid hNode env
    · rename_i mask
      split
      · rename_i hZero
        have hMask : mask = 0 := of_decide_eq_true hZero
        subst hMask
        dsimp [evalSymNodeWith, evalSymOp1, wrap64]
        rw [Nat.xor_zero]
        exact (Nat.mod_eq_of_lt (evalSymId_lt_word64 tbl env a)).symm
      · exact internRawNode_eval hValid hNode env
    · rename_i delta
      split
      · rename_i hZero
        have hDelta : delta = 0 := of_decide_eq_true hZero
        subst hDelta
        dsimp [evalSymNodeWith, evalSymOp1, wrap64]
        exact (Nat.mod_eq_of_lt (evalSymId_lt_word64 tbl env a)).symm
      · exact internRawNode_eval hValid hNode env
  | const v => exact internRawNode_eval hValid hNode env
  | var idx => exact internRawNode_eval hValid hNode env
  | op2 op a b => exact internOp2_eval hValid hNode env

/-- Non-vacuity witness for `addConst 0` and `xorConst 0` peephole folding: interning
    `.op1 (.addConst 0) 0` and `.op1 (.xorConst 0) 0` folds directly to `SymId 0` without
    growing `tbl.nodes`, relying on `evalSymId_lt_word64` for `wrap64` soundness. -/
theorem internNode_addConst0_peephole_witness :
    internNode { nodes := [.var 0] } (.op1 (.addConst 0) 0) = (0, { nodes := [.var 0] }) ∧
      internNode { nodes := [.var 0] } (.op1 (.xorConst 0) 0) = (0, { nodes := [.var 0] }) :=
  ⟨rfl, rfl⟩

/-- **GVN Deduplication Theorem (`internNode_dedup`)**:
    Re-interning a `node` that was just interned returns the exact same `SymId`
    and leaves `tbl` (and `tbl.nodes.length`) completely unchanged. -/
theorem internRawNode_dedup (tbl : SymTable) (node : SymNode) :
    let res₁ := internRawNode tbl node
    internRawNode res₁.2 node = res₁ ∧
      (internRawNode res₁.2 node).2.nodes.length = res₁.2.nodes.length := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    dsimp
    rw [hFind]
    exact ⟨rfl, rfl⟩
  | none =>
    dsimp
    have hLookupApp : (tbl.nodes ++ [node])[tbl.nodes.length]? = some node := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rcases findNodeIdx_complete hLookupApp with ⟨idx, hFindApp⟩
    have hSpec := findNodeIdx_spec hFindApp
    rw [hFindApp]
    have hIdxEq : idx = tbl.nodes.length := by
      cases hlt : decide (idx < tbl.nodes.length) with
      | true =>
        have hlt' : idx < tbl.nodes.length := of_decide_eq_true hlt
        have hInOld : tbl.nodes[idx]? = some node := by
          have hGet := hSpec.2
          rw [List.getElem?_append_left hlt'] at hGet
          exact hGet
        rcases findNodeIdx_complete hInOld with ⟨idx₀, hFind₀⟩
        rw [hFind] at hFind₀
        cases hFind₀
      | false =>
        have hge : tbl.nodes.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt)
        have hLen : (tbl.nodes ++ [node]).length = tbl.nodes.length + 1 := by simp
        have hlt' := hSpec.1
        omega
    subst hIdxEq
    exact ⟨rfl, rfl⟩

theorem internOp2_dedup (tbl : SymTable) (op : SymOp2) (a b : SymId) :
    internOp2 (internOp2 tbl op a b).2 op a b = internOp2 tbl op a b := by
  cases hFind : findNodeIdx tbl.nodes (.op2 op a b) with
  | some idx =>
    have h1 : internOp2 tbl op a b = (idx, tbl) := by
      unfold internOp2
      rw [hFind]
    rw [h1]
    exact h1
  | none =>
    cases hP : peepholeOp2 op a b with
    | inl x =>
      have h1 : internOp2 tbl op a b = (x, tbl) := by
        unfold internOp2
        rw [hFind, hP]
      rw [h1]
      exact h1
    | inr node' =>
      have h1 : internOp2 tbl op a b = internRawNode tbl node' := by
        unfold internOp2
        rw [hFind, hP]
      rw [h1]
      cases hRaw : findNodeIdx tbl.nodes node' with
      | some j =>
        have hR : internRawNode tbl node' = (j, tbl) := by
          unfold internRawNode
          rw [hRaw]
        rw [hR]
        show internOp2 tbl op a b = (j, tbl)
        rw [h1, hR]
      | none =>
        have hR : internRawNode tbl node' =
            (tbl.nodes.length, { nodes := tbl.nodes ++ [node'] }) := by
          unfold internRawNode
          rw [hRaw]
        rw [hR]
        by_cases hEq : node' = .op2 op a b
        · subst hEq
          have hSelf := findNodeIdxAux_append_self (.op2 op a b) tbl.nodes 0 hFind
          unfold internOp2
          dsimp only
          rw [show findNodeIdx (tbl.nodes ++ [SymNode.op2 op a b]) (.op2 op a b) =
            some tbl.nodes.length from by
              unfold findNodeIdx
              rw [hSelf, Nat.zero_add]]
        · have hNone := findNodeIdxAux_append_none (.op2 op a b) node' hEq tbl.nodes 0 hFind
          unfold internOp2
          dsimp only
          rw [show findNodeIdx (tbl.nodes ++ [node']) (.op2 op a b) = none from hNone, hP]
          have hD := (internRawNode_dedup tbl node').1
          rw [hR] at hD
          exact hD

theorem internNode_dedup (tbl : SymTable) (node : SymNode) :
    let res₁ := internNode tbl node
    internNode res₁.2 node = res₁ ∧
      (internNode res₁.2 node).2.nodes.length = res₁.2.nodes.length := by
  dsimp
  cases node with
  | ite c t e =>
    cases hEq : (t == e) with
    | true =>
      have hStep : internNode tbl (.ite c t e) = (t, tbl) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      rw [hStep]
      dsimp
      rw [hStep]
      exact ⟨rfl, rfl⟩
    | false =>
      have hStep₁ : internNode tbl (.ite c t e) = internRawNode tbl (.ite c t e) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      have hStep₂ : internNode (internRawNode tbl (.ite c t e)).2 (.ite c t e) =
          internRawNode (internRawNode tbl (.ite c t e)).2 (.ite c t e) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      rw [hStep₁, hStep₂]
      exact internRawNode_dedup tbl (.ite c t e)
  | op1 op a =>
    cases op <;> dsimp [internNode]
    · exact ⟨rfl, rfl⟩
    · exact internRawNode_dedup tbl (.op1 .boolNot a)
    · exact internRawNode_dedup tbl (.op1 .wrappingNeg64 a)
    · exact internRawNode_dedup tbl (.op1 .maskLow32 a)
    · rename_i mask
      cases hZero : (mask == 0) with
      | true => exact ⟨rfl, rfl⟩
      | false => exact internRawNode_dedup tbl (.op1 (.xorConst mask) a)
    · rename_i delta
      cases hZero : (delta == 0) with
      | true => exact ⟨rfl, rfl⟩
      | false => exact internRawNode_dedup tbl (.op1 (.addConst delta) a)
  | const v => exact internRawNode_dedup tbl (.const v)
  | var idx => exact internRawNode_dedup tbl (.var idx)
  | op2 op a b =>
    exact ⟨internOp2_dedup tbl op a b,
      congrArg (fun r => r.2.nodes.length) (internOp2_dedup tbl op a b)⟩

theorem internRawNode_tbl_of_mem {tbl : SymTable} {node : SymNode} {i : Nat}
    (hAt : tbl.nodes[i]? = some node) : (internRawNode tbl node).2 = tbl := by
  rcases findNodeIdx_complete hAt with ⟨idx, hFind⟩
  dsimp only [internRawNode]
  rw [hFind]

theorem internOp2_tbl_of_mem {tbl : SymTable} {op : SymOp2} {a b : SymId} {i : Nat}
    (hAt : tbl.nodes[i]? = some (.op2 op a b)) : (internOp2 tbl op a b).2 = tbl := by
  rcases findNodeIdx_complete hAt with ⟨idx, hFind⟩
  unfold internOp2
  rw [hFind]

theorem internNode_tbl_of_mem {tbl : SymTable} {node : SymNode} {i : Nat}
    (hAt : tbl.nodes[i]? = some node) : (internNode tbl node).2 = tbl := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp only
    split
    · rfl
    · exact internRawNode_tbl_of_mem hAt
  | op1 op a =>
    cases op <;> dsimp only <;>
      first | rfl | exact internRawNode_tbl_of_mem hAt |
        (split <;> first | rfl | exact internRawNode_tbl_of_mem hAt)
  | const v => exact internRawNode_tbl_of_mem hAt
  | var idx => exact internRawNode_tbl_of_mem hAt
  | op2 op a b => exact internOp2_tbl_of_mem hAt

/-- **Strong GVN Deduplication (`internNode_dedup_existing`)**: interning ANY node that already
    occurs anywhere in a valid table (not just the most recently interned one) leaves the
    table — hence `tbl.nodes.length` — unchanged and returns a `SymId` that denotes the same
    value as the existing occurrence under every `env`. -/
theorem internNode_dedup_existing {tbl : SymTable} {node : SymNode} {i : Nat}
    (hValid : ValidTable tbl) (hAt : tbl.nodes[i]? = some node) :
    (internNode tbl node).2 = tbl ∧
      ∀ env, evalSymId tbl env (internNode tbl node).1 = evalSymId tbl env i := by
  have hLt : i < tbl.nodes.length := by
    cases h : decide (i < tbl.nodes.length) with
    | true => exact of_decide_eq_true h
    | false =>
      rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false h))] at hAt
      cases hAt
  have hNode : ValidNode tbl.nodes.length node := (hValid i node hAt).mono (Nat.le_of_lt hLt)
  have hTbl := internNode_tbl_of_mem hAt
  refine ⟨hTbl, fun env => ?_⟩
  have h1 := internNode_eval hValid hNode env
  dsimp only at h1
  rw [hTbl] at h1
  rw [h1, evalSymId_eq_evalSymNodeWith hValid env hAt]

/-- Six interning steps over `[x₀, x₁]` exercising every peephole class. -/
def peepholeDemo : List SymId × SymTable :=
  let t₀ : SymTable := { nodes := [.var 0, .var 1] }
  let r₁ := internNode t₀ (.op2 .add 1 0)
  let r₂ := internNode r₁.2 (.op2 .add 0 1)
  let r₃ := internNode r₂.2 (.op2 .bitXor 0 0)
  let r₄ := internNode r₃.2 (.op2 .sub 0 0)
  let r₅ := internNode r₄.2 (.op2 .bitAnd 1 1)
  let r₆ := internNode r₅.2 (.op2 .eq 0 0)
  ([r₁.1, r₂.1, r₃.1, r₄.1, r₅.1, r₆.1], r₆.2)

/-- **Peephole GVN Witness (`peepholeOp2_witness`)**: `x₁ + x₀` and `x₀ + x₁` share one
    `SymId` (canonical commutative order); `x₀ ^ x₀` and `x₀ - x₀` fold to one shared constant
    `0`; `x₁ & x₁` folds to `x₁` without allocating; `x₀ == x₀` folds to the constant `1`. -/
theorem peepholeOp2_witness :
    peepholeDemo = ([2, 2, 3, 3, 1, 4],
      { nodes := [.var 0, .var 1, .op2 .add 0 1, .const 0, .const 1] }) := by
  decide +kernel

/-- Key structural freshness lemma: in any `ValidTable tbl`, every existing node at
    `idx < tbl.nodes.length` satisfies `ValidNode (tbl.nodes.length - 1) node`.
    Therefore, any node that references the newest `SymId` (`last = tbl.nodes.length - 1`)
    cannot already appear anywhere in `tbl.nodes`! -/
theorem findNodeIdx_eq_none_of_not_valid_last {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl)
    (hNotValid : ¬ ValidNode (tbl.nodes.length - 1) node) :
    findNodeIdx tbl.nodes node = none := by
  cases hFind : findNodeIdx tbl.nodes node with
  | none => rfl
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    have hNodeValid : ValidNode idx node := hValid idx node hSpec.2
    have hLe : idx ≤ tbl.nodes.length - 1 := by omega
    exact False.elim (hNotValid (hNodeValid.mono hLe))

/-!
### 1.1 $k$-Step Diamond Expression Scaling (`2 * k + 1` DAG Nodes vs. `4 * 2^k - 3` Tree Nodes)
-/

/-- Naive unshared symbolic expression AST produced by direct substitution without GVN. -/
inductive ExprTree where
  | const (val : Nat)
  | var (inputIdx : Nat)
  | op1 (op : SymOp1) (arg : ExprTree)
  | op2 (op : SymOp2) (lhs rhs : ExprTree)
  | ite (cond thenBr elseBr : ExprTree)
  deriving DecidableEq

/-- Concrete evaluation of a `ExprTree`. -/
def ExprTree.eval (env : SymEnv) : ExprTree → Nat
  | .const v => wrap64 v
  | .var idx => wrap64 (env idx)
  | .op1 op a => evalSymOp1 op (a.eval env)
  | .op2 op a b => evalSymOp2 op (a.eval env) (b.eval env)
  | .ite c t e => if c.eval env != 0 then t.eval env else e.eval env

/-- Total AST node count of a `ExprTree`. -/
def ExprTree.nodeCount : ExprTree → Nat
  | .const _ => 1
  | .var _ => 1
  | .op1 _ a => 1 + a.nodeCount
  | .op2 _ a b => 1 + a.nodeCount + b.nodeCount
  | .ite c t e => 1 + c.nodeCount + t.nodeCount + e.nodeCount

/-- Build the $k$-step diamond expression `x_{i+1} = add(xor(x_i, i+1), xor(x_i, i+1))`
    by naive tree substitution (`ExprTree`), duplicating `x_i` across both arms at each step. -/
def buildDiamondTree : Nat → ExprTree
  | 0 => .var 0
  | i + 1 =>
    let prev := buildDiamondTree i
    let br := ExprTree.op1 (.xorConst (i + 1)) prev
    ExprTree.op2 .add br br

/-- Build the exact same $k$-step diamond expression via `SymTable` GVN (`internNode`),
    where both branches of diamond `i + 1` intern `.op1 (.xorConst (i + 1)) prevId` and
    join via `.op2 .add leftId rightId`. -/
def buildDiamondGvn : Nat → Nat × SymTable
  | 0 => (0, { nodes := [.var 0] })
  | i + 1 =>
    let (prevId, tbl₀) := buildDiamondGvn i
    let xorNode := SymNode.op1 (.xorConst (i + 1)) prevId
    let (leftId, tbl₁) := internNode tbl₀ xorNode
    let (rightId, tbl₂) := internNode tbl₁ xorNode
    internNode tbl₂ (.op2 .add leftId rightId)

/-- Exponential $O(2^k)$ node blowup of naive tree substitution:
    `(buildDiamondTree k).nodeCount + 3 = 4 * 2^k`. -/
theorem buildDiamondTree_nodeCount (k : Nat) :
    (buildDiamondTree k).nodeCount + 3 = 4 * (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ i ih =>
    dsimp [buildDiamondTree, ExprTree.nodeCount]
    rw [Nat.pow_succ]
    omega

/-- **Universal $k$-Step Diamond GVN Theorem (`buildDiamondGvn_spec`)**:
    For every `k : Nat`, `buildDiamondGvn k` produces a valid `SymTable` with:
    1. Root `SymId = 2 * k`,
    2. Exact linear table size `2 * k + 1` (vs. `4 * 2^k - 3` for `buildDiamondTree k`), and
    3. Identical concrete evaluation `evalSymId tbl env rootId = (buildDiamondTree k).eval env`
       for all input environments `env : SymEnv`. -/
theorem buildDiamondGvn_spec (k : Nat) :
    let (rootId, tbl) := buildDiamondGvn k
    ValidTable tbl ∧
      rootId = 2 * k ∧
      tbl.nodes.length = 2 * k + 1 ∧
      ∀ env : SymEnv, evalSymId tbl env rootId = (buildDiamondTree k).eval env := by
  induction k with
  | zero =>
    refine ⟨?_, rfl, rfl, fun _ => rfl⟩
    intro idx node hGet
    cases idx with
    | zero =>
      dsimp [buildDiamondGvn] at hGet
      injection hGet with hEq
      subst hEq
      trivial
    | succ k' =>
      dsimp [buildDiamondGvn] at hGet
      cases hGet
  | succ i ih =>
    rcases hPrev : buildDiamondGvn i with ⟨prevId, tbl₀⟩
    rw [hPrev] at ih
    rcases ih with ⟨hValid₀, hPrevId, hLen₀, hEval₀⟩
    dsimp [buildDiamondGvn]
    rw [hPrev]
    dsimp
    let xorNode := SymNode.op1 (.xorConst (i + 1)) prevId
    have hXorValid₀ : ValidNode tbl₀.nodes.length xorNode := by
      dsimp [ValidNode, xorNode]
      omega
    have hXorNotValidLast : ¬ ValidNode (tbl₀.nodes.length - 1) xorNode := by
      dsimp [ValidNode, xorNode]
      intro hContra
      omega
    have hFindXor : findNodeIdx tbl₀.nodes xorNode = none :=
      findNodeIdx_eq_none_of_not_valid_last hValid₀ hXorNotValidLast
    have hStep₁ : internNode tbl₀ xorNode = (tbl₀.nodes.length, { nodes := tbl₀.nodes ++ [xorNode] }) := by
      dsimp [internNode, xorNode, internRawNode]
      rw [hFindXor]
    have hDedup := (internNode_dedup tbl₀ xorNode).1
    have hValid₁ : ValidTable (internNode tbl₀ xorNode).2 :=
      (internNode_valid hValid₀ hXorValid₀).1
    have hEval₁ : ∀ env, evalSymId (internNode tbl₀ xorNode).2 env (internNode tbl₀ xorNode).1 =
        evalSymOp1 (.xorConst (i + 1)) (evalSymId tbl₀ env prevId) := by
      intro env
      exact internNode_eval hValid₀ hXorValid₀ env
    rw [hDedup]
    rw [hStep₁] at hValid₁ hEval₁ ⊢
    dsimp at hValid₁ hEval₁ ⊢
    let leftId := tbl₀.nodes.length
    let tbl₁ : SymTable := { nodes := tbl₀.nodes ++ [xorNode] }
    have hLen₁ : tbl₁.nodes.length = 2 * i + 2 := by
      dsimp [tbl₁]
      rw [List.length_append, hLen₀]
      rfl
    let addNode := SymNode.op2 .add leftId leftId
    have hAddValid₁ : ValidNode tbl₁.nodes.length addNode := by
      dsimp [ValidNode, addNode, leftId]
      exact ⟨by omega, by omega⟩
    have hAddNotValidLast : ¬ ValidNode (tbl₁.nodes.length - 1) addNode := by
      dsimp [ValidNode, addNode, leftId]
      intro hContra
      have hContra₁ := hContra.1
      omega
    have hFindAdd : findNodeIdx tbl₁.nodes addNode = none :=
      findNodeIdx_eq_none_of_not_valid_last hValid₁ hAddNotValidLast
    have hStep₃ : internNode tbl₁ addNode = (tbl₁.nodes.length, { nodes := tbl₁.nodes ++ [addNode] }) := by
      show internOp2 tbl₁ .add leftId leftId = _
      unfold internOp2
      rw [hFindAdd]
      dsimp only [peepholeOp2]
      rw [ite_eq_left (rfl : leftId = leftId)]
      dsimp only
      unfold internRawNode
      rw [hFindAdd]
    have hValid₃ : ValidTable (internNode tbl₁ addNode).2 :=
      (internNode_valid hValid₁ hAddValid₁).1
    have hEval₃ : ∀ env, evalSymId (internNode tbl₁ addNode).2 env (internNode tbl₁ addNode).1 =
        evalSymOp2 .add (evalSymId tbl₁ env leftId) (evalSymId tbl₁ env leftId) := by
      intro env
      exact internNode_eval hValid₁ hAddValid₁ env
    rw [hStep₃] at hValid₃ hEval₃ ⊢
    dsimp at hValid₃ hEval₃ ⊢
    refine ⟨hValid₃, by omega, ?_, ?_⟩
    · rw [List.length_append, hLen₁]
      dsimp
      omega
    · intro env
      rw [hEval₃ env]
      rw [hEval₁ env]
      rw [hEval₀ env]
      rfl

/-- Concrete non-vacuity witness for `k = 6` diamond steps:
    `SymTable` GVN uses `13` nodes (`2 * 6 + 1`) whereas `ExprTree` uses `253` nodes
    (`4 * 2^6 - 3`), and both evaluate to the exact same value on input `x₀ = 42`. -/
theorem diamond6_gvn_vs_tree_witness :
    (buildDiamondGvn 6).2.nodes.length = 13 ∧
      (buildDiamondTree 6).nodeCount = 253 ∧
      evalSymId (buildDiamondGvn 6).2 (fun _ => 42) (buildDiamondGvn 6).1 =
        (buildDiamondTree 6).eval (fun _ => 42) :=
  ⟨rfl, rfl, rfl⟩

/-- GVN-intern a naive `ExprTree` into `tbl` bottom-up (hash-consing every subtree). -/
def internTree : SymTable → ExprTree → SymId × SymTable
  | tbl, .const v => internNode tbl (.const v)
  | tbl, .var i => internNode tbl (.var i)
  | tbl, .op1 op a =>
    match internTree tbl a with
    | (ia, t₁) => internNode t₁ (.op1 op ia)
  | tbl, .op2 op a b =>
    match internTree tbl a with
    | (ia, t₁) =>
      match internTree t₁ b with
      | (ib, t₂) => internNode t₂ (.op2 op ia ib)
  | tbl, .ite c t e =>
    match internTree tbl c with
    | (ic, t₁) =>
      match internTree t₁ t with
      | (it, t₂) =>
        match internTree t₂ e with
        | (ie, t₃) => internNode t₃ (.ite ic it ie)

theorem internNode_spec {tbl : SymTable} {node : SymNode} (hValid : ValidTable tbl)
    (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internNode tbl node).2 ∧ tbl.Extends (internNode tbl node).2 ∧
      (internNode tbl node).1 < (internNode tbl node).2.nodes.length ∧
      ∀ env, evalSymId (internNode tbl node).2 env (internNode tbl node).1 =
        evalSymNodeWith (evalSymId tbl env) env node :=
  ⟨(internNode_valid hValid hNode).1, internNode_extends tbl node,
    (internNode_valid hValid hNode).2, fun env => internNode_eval hValid hNode env⟩

/-- **Tree Interning Soundness (`internTree_spec`)**: GVN-interning ANY `ExprTree` preserves
    `ValidTable`, only extends the table, and yields a `SymId` denoting exactly the tree. -/
theorem internTree_spec : ∀ (t : ExprTree) (tbl : SymTable), ValidTable tbl →
    ValidTable (internTree tbl t).2 ∧ tbl.Extends (internTree tbl t).2 ∧
      (internTree tbl t).1 < (internTree tbl t).2.nodes.length ∧
      ∀ env, evalSymId (internTree tbl t).2 env (internTree tbl t).1 = t.eval env
  | .const v, tbl, hValid => by
    rcases internNode_spec (node := .const v) hValid trivial with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun env => h4 env⟩
  | .var i, tbl, hValid => by
    rcases internNode_spec (node := .var i) hValid trivial with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun env => h4 env⟩
  | .op1 op a, tbl, hValid => by
    rcases internTree_spec a tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hA : internTree tbl a with ⟨ia, t₁⟩
    rw [hA] at hV₁ hE₁ hLt₁ hEv₁
    rcases internNode_spec (node := .op1 op ia) hV₁ hLt₁ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hA]
    refine ⟨h1, hE₁.trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval, hEv₁ env]
  | .op2 op a b, tbl, hValid => by
    rcases internTree_spec a tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hA : internTree tbl a with ⟨ia, t₁⟩
    rw [hA] at hV₁ hE₁ hLt₁ hEv₁
    rcases internTree_spec b t₁ hV₁ with ⟨hV₂, hE₂, hLt₂, hEv₂⟩
    rcases hB : internTree t₁ b with ⟨ib, t₂⟩
    rw [hB] at hV₂ hE₂ hLt₂ hEv₂
    have hIa : ia < t₂.nodes.length := Nat.lt_of_lt_of_le hLt₁ hE₂.length_le
    rcases internNode_spec (node := .op2 op ia ib) hV₂ ⟨hIa, hLt₂⟩ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hA, hB]
    refine ⟨h1, (hE₁.trans hE₂).trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval]
    rw [← evalSymId_mono hV₁ hE₂ env hLt₁, hEv₁ env, hEv₂ env]
  | .ite c t e, tbl, hValid => by
    rcases internTree_spec c tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hC : internTree tbl c with ⟨ic, t₁⟩
    rw [hC] at hV₁ hE₁ hLt₁ hEv₁
    rcases internTree_spec t t₁ hV₁ with ⟨hV₂, hE₂, hLt₂, hEv₂⟩
    rcases hT : internTree t₁ t with ⟨it, t₂⟩
    rw [hT] at hV₂ hE₂ hLt₂ hEv₂
    rcases internTree_spec e t₂ hV₂ with ⟨hV₃, hE₃, hLt₃, hEv₃⟩
    rcases hE : internTree t₂ e with ⟨ie, t₃⟩
    rw [hE] at hV₃ hE₃ hLt₃ hEv₃
    have hIc : ic < t₃.nodes.length :=
      Nat.lt_of_lt_of_le hLt₁ (Nat.le_trans hE₂.length_le hE₃.length_le)
    have hIt : it < t₃.nodes.length := Nat.lt_of_lt_of_le hLt₂ hE₃.length_le
    rcases internNode_spec (node := .ite ic it ie) hV₃ ⟨hIc, hIt, hLt₃⟩ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hC, hT, hE]
    refine ⟨h1, ((hE₁.trans hE₂).trans hE₃).trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval]
    rw [← evalSymId_mono hV₁ (hE₂.trans hE₃) env hLt₁, ← evalSymId_mono hV₂ hE₃ env hLt₂,
      hEv₁ env, hEv₂ env, hEv₃ env]

/-!
## Section 2 — Raw vs. Canonical MIR State (`CanonLocals` + Borrow-Dirtied Generations) & Spine Forcing
-/

/-- Local variable index in a MIR body. -/
abbrev LocalId := Nat

/-- Polymorphic MIR local slot parameterized by the payload type `Val` (`Nat` for
    concrete values or `SymId` for symbolic GVN value references):
    - `.dead gen`: storage is dead; `gen` is the next generation counter to assign.
    - `.uninit gen`: storage is live (`StorageLive`), value not yet initialized.
    - `.live val gen borrowed loanTarget`: holds initialized value `val` at generation
      `gen`, where `borrowed == true` iff a reference (`Rvalue.ref` / `retagBorrow`) has
      been taken to this incarnation, and `loanTarget` optionally tracks `(targetLocal,
      expectedGen)` when this local itself holds a reference. -/
inductive Slot (Val : Type) where
  | dead (gen : Nat := 0)
  | uninit (gen : Nat := 0)
  | live (val : Val) (gen : Nat := 0) (borrowed : Bool := false)
      (loanTarget : Option (LocalId × Nat) := none)
  deriving DecidableEq

/-- Extract the generation counter of a `Slot`. -/
def Slot.gen {Val : Type} : Slot Val → Nat
  | .dead g => g
  | .uninit g => g
  | .live _ g _ _ => g

/-- Borrow-dirtied generation transition (`c19b8fce8`): ending or restarting a slot's
    storage lifetime increments `gen` **if and only if** the current incarnation was
    borrowed (`borrowed == true`). Unborrowed temporaries preserve `gen` unchanged! -/
def Slot.nextGenOnEnd {Val : Type} : Slot Val → Nat
  | .dead g => g
  | .uninit g => g
  | .live _ g false _ => g
  | .live _ g true _ => g + 1

/-- `StorageDead` transition on a single slot. -/
def Slot.kill {Val : Type} (s : Slot Val) : Slot Val :=
  .dead s.nextGenOnEnd

/-- `StorageLive` transition on a single slot. -/
def Slot.reborn {Val : Type} (s : Slot Val) : Slot Val :=
  .uninit s.nextGenOnEnd

/-- Assign a scalar/symbolic value `v` (with optional loan metadata) into a slot,
    preserving its current `gen` and `borrowed` flag if already live. -/
def Slot.writeVal {Val : Type} (s : Slot Val) (v : Val)
    (loanTarget : Option (LocalId × Nat) := none) : Slot Val :=
  match s with
  | .live _ g b _ => .live v g b loanTarget
  | .uninit g | .dead g => .live v g false loanTarget

/-- Universal temporal safety lemma: killing or rebirthing a borrowed slot
    (`.live v g true loan`) strictly advances its generation to `g + 1`. -/
theorem Slot.kill_or_reborn_borrowed_bumps_gen {Val : Type} (v : Val) (g : Nat)
    (loan : Option (LocalId × Nat)) :
    (Slot.live v g true loan).kill.gen = g + 1 ∧
      (Slot.live v g true loan).reborn.gen = g + 1 :=
  ⟨rfl, rfl⟩

/-- Universal unborrowed temporary round-trip identity: `StorageLive -> Assign ->
    StorageDead` on any unborrowed `.dead g` slot returns to `.dead g` by `rfl`. -/
theorem Slot.unborrowed_roundtrip_rfl {Val : Type} (v : Val) (g : Nat) :
    (((Slot.dead g).reborn).writeVal v none).kill = Slot.dead g :=
  rfl

/-- `Slot.kill` is idempotent on all slots. -/
theorem Slot.kill_idempotent {Val : Type} (s : Slot Val) :
    s.kill.kill = s.kill := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live v g b loan =>
    cases b <;> rfl

/-- Normalize a slot against a join-point liveness bit `isLive`: live locals keep their
    slot unchanged; dead locals (`isLive = false`) are killed via `Slot.kill` (which
    preserves their borrow-dirtied generation counter while pruning dead values). -/
def normalizeSlotForMask {Val : Type} (isLive : Bool) (s : Slot Val) : Slot Val :=
  if isLive then s else s.kill

theorem normalizeSlotForMask_idempotent {Val : Type} (isLive : Bool) (s : Slot Val) :
    normalizeSlotForMask isLive (normalizeSlotForMask isLive s) =
      normalizeSlotForMask isLive s := by
  cases isLive with
  | true => rfl
  | false => exact Slot.kill_idempotent s

/-- History-dependent `RawState`: models an uncanonicalized association-list write log
    where out-of-order updates and branch-local `StorageLive`/`StorageDead` events
    leave path-dependent history in `writeLog`. -/
structure RawState (Val : Type) where
  numLocals : Nat
  writeLog : List (LocalId × Slot Val) := []
  deriving DecidableEq

/-- Look up the most recent slot for `loc` in a `RawState` write log. -/
def RawState.getSlot {Val : Type} (st : RawState Val) (loc : LocalId) : Slot Val :=
  match st.writeLog.find? (fun entry => entry.1 == loc) with
  | some (_, s) => s
  | none => .dead 0

def RawState.putSlot {Val : Type} (st : RawState Val) (loc : LocalId) (s : Slot Val) : RawState Val :=
  { st with writeLog := (loc, s) :: st.writeLog }

def RawState.storageLive {Val : Type} (st : RawState Val) (loc : LocalId) : RawState Val :=
  st.putSlot loc (st.getSlot loc).reborn

def RawState.storageDead {Val : Type} (st : RawState Val) (loc : LocalId) : RawState Val :=
  st.putSlot loc (st.getSlot loc).kill

def RawState.assign {Val : Type} (st : RawState Val) (loc : LocalId) (v : Val) : RawState Val :=
  st.putSlot loc ((st.getSlot loc).writeVal v none)

/-- Write-log well-formedness: every logged write targets an in-bounds local `< numLocals`. -/
def RawWriteLogWF {Val : Type} : Nat → List (LocalId × Slot Val) → Prop
  | _, [] => True
  | n, (loc, _) :: rest => loc < n ∧ RawWriteLogWF n rest

/-- A `RawState` is well-formed (`RawState.WF`) when all entries in `writeLog` satisfy
    `loc < st.numLocals`. -/
def RawState.WF {Val : Type} (st : RawState Val) : Prop :=
  RawWriteLogWF st.numLocals st.writeLog

theorem RawState.putSlot_wf {Val : Type} {st : RawState Val} {loc : LocalId} {s : Slot Val}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.putSlot loc s).WF :=
  ⟨hLt, hWF⟩

theorem RawState.storageLive_wf {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.storageLive loc).WF :=
  ⟨hLt, hWF⟩

theorem RawState.storageDead_wf {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.storageDead loc).WF :=
  ⟨hLt, hWF⟩

theorem RawState.assign_wf {Val : Type} {st : RawState Val} {loc : LocalId} {v : Val}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.assign loc v).WF :=
  ⟨hLt, hWF⟩

theorem find?_eq_none_of_rawWriteLogWF {Val : Type} (n loc : Nat) (hGe : n ≤ loc) :
    ∀ (log : List (LocalId × Slot Val)),
      RawWriteLogWF n log →
      log.find? (fun entry => entry.1 == loc) = none
  | [], _ => rfl
  | (l, _) :: rest, ⟨hLt, hRest⟩ => by
    have hNe : (l == loc) = false :=
      beq_eq_false_iff_ne.2 (Nat.ne_of_lt (Nat.lt_of_lt_of_le hLt hGe))
    dsimp [List.find?]
    rw [hNe]
    exact find?_eq_none_of_rawWriteLogWF n loc hGe rest hRest

/-- Any well-formed `RawState` returns `.dead 0` for every out-of-bounds local `loc ≥ numLocals`. -/
theorem RawState.getSlot_of_ge_numLocals {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hGe : st.numLocals ≤ loc) :
    st.getSlot loc = .dead 0 := by
  dsimp [RawState.getSlot]
  rw [find?_eq_none_of_rawWriteLogWF st.numLocals loc hGe st.writeLog hWF]

/-- Canonical MIR local state (`CanonState` / `CanonLocals`): a dense, strictly index-ordered
    list of `Slot Val` entries (where index `i` is local `i`) with dead locals pruned to
    `.dead gen`. -/
structure CanonState (Val : Type) where
  slots : List (Slot Val)
  deriving DecidableEq

/-- Canonical MIR local store alias (`CanonLocals`). -/
abbrev CanonLocals (Val : Type) := CanonState Val

/-- Spine-preserving list update at index `idx`. -/
def setSlotAt {Val : Type} : List (Slot Val) → Nat → Slot Val → List (Slot Val)
  | [], _, _ => []
  | _ :: xs, 0, s => s :: xs
  | x :: xs, i + 1, s => x :: setSlotAt xs i s

/-- Total slot lookup in a canonical slot list. -/
def getSlotAt {Val : Type} : List (Slot Val) → Nat → Slot Val
  | [], _ => .dead 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getSlotAt xs i

def CanonState.getSlot {Val : Type} (st : CanonState Val) (loc : LocalId) : Slot Val :=
  getSlotAt st.slots loc

def CanonState.setSlot {Val : Type} (st : CanonState Val) (loc : LocalId) (s : Slot Val) :
    CanonState Val :=
  { slots := setSlotAt st.slots loc s }

theorem getSlotAt_eq_getElem? {Val : Type} :
    ∀ (slots : List (Slot Val)) (i : Nat),
      i < slots.length →
      slots[i]? = some (getSlotAt slots i)
  | [], _, hlt => by simp at hlt
  | x :: _, 0, _ => rfl
  | _ :: xs, i + 1, hlt => by
    dsimp [getSlotAt]
    exact getSlotAt_eq_getElem? xs i (by dsimp at hlt; omega)

/-- Build the canonical slot list for indices `offset .. offset + mask.length - 1`
    from a slot lookup function `lookup`. -/
def buildCanonSlotsAux {Val : Type} (lookup : LocalId → Slot Val) (offset : Nat) :
    List Bool → List (Slot Val)
  | [] => []
  | isLive :: rest =>
    normalizeSlotForMask isLive (lookup offset) ::
      buildCanonSlotsAux lookup (offset + 1) rest

/-- Canonicalize a `RawState` against a join-point `liveMask : List Bool`. -/
def canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val) : CanonState Val :=
  { slots := buildCanonSlotsAux raw.getSlot 0 liveMask }

/-- Re-canonicalize an already-canonical `CanonState` against `liveMask`. -/
def canonicalizeCanon {Val : Type} (liveMask : List Bool) (st : CanonState Val) : CanonState Val :=
  { slots := buildCanonSlotsAux st.getSlot 0 liveMask }

/-- Live-restricted denotation of a `RawState` under `liveMask`. -/
def denoteRaw {Val : Type} (liveMask : List Bool) (raw : RawState Val) (loc : LocalId) : Slot Val :=
  match liveMask[loc]? with
  | some isLive => normalizeSlotForMask isLive (raw.getSlot loc)
  | none => .dead 0

/-- Live-restricted denotation of a `CanonState` under `liveMask`. -/
def denoteCanon {Val : Type} (liveMask : List Bool) (st : CanonState Val) (loc : LocalId) : Slot Val :=
  match liveMask[loc]? with
  | some isLive => normalizeSlotForMask isLive (st.getSlot loc)
  | none => .dead 0

/-- Two `RawState`s are live-equivalent at `liveMask` when every in-bounds local `i` has
    (1) the **identical slot** (value, generation, borrow flag, loan) when `liveMask[i] = true`,
    and (2) the **identical borrow-dirtied post-generation** `nextGenOnEnd` when
    `liveMask[i] = false` — values, initialization status and write history of dead locals are
    ignored. (Stated semantically, independently of `normalizeSlotForMask`/`canonicalize`.) -/
def LiveEquiv {Val : Type} (liveMask : List Bool) (raw₁ raw₂ : RawState Val) : Prop :=
  ∀ i isLive, liveMask[i]? = some isLive →
    (isLive = true → raw₁.getSlot i = raw₂.getSlot i) ∧
      (isLive = false → (raw₁.getSlot i).nextGenOnEnd = (raw₂.getSlot i).nextGenOnEnd)

/-- Normalized slots agree iff they agree as live slots (live) or agree on their
    borrow-dirtied post-generation (dead). -/
theorem normalizeSlotForMask_eq_iff {Val : Type} (isLive : Bool) (s₁ s₂ : Slot Val) :
    normalizeSlotForMask isLive s₁ = normalizeSlotForMask isLive s₂ ↔
      ((isLive = true → s₁ = s₂) ∧
        (isLive = false → s₁.nextGenOnEnd = s₂.nextGenOnEnd)) := by
  cases isLive with
  | true =>
    constructor
    · intro h
      exact ⟨(fun _ => h), (fun h' => by cases h')⟩
    · intro h
      exact h.1 rfl
  | false =>
    constructor
    · intro h
      refine ⟨(fun h' => by cases h'), (fun _ => ?_)⟩
      have h' : Slot.dead s₁.nextGenOnEnd = Slot.dead s₂.nextGenOnEnd := h
      injection h'
    · intro h
      show Slot.dead s₁.nextGenOnEnd = Slot.dead s₂.nextGenOnEnd
      rw [h.2 rfl]

theorem buildCanonSlotsAux_length {Val : Type} (lookup : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset : Nat),
      (buildCanonSlotsAux lookup offset mask).length = mask.length
  | [], _ => rfl
  | _ :: rest, offset => by
    dsimp [buildCanonSlotsAux]
    rw [buildCanonSlotsAux_length lookup rest (offset + 1)]

theorem getSlotAt_buildCanonSlotsAux {Val : Type} (lookup : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset idx : Nat) (isLive : Bool),
      mask[idx]? = some isLive →
      getSlotAt (buildCanonSlotsAux lookup offset mask) idx =
        normalizeSlotForMask isLive (lookup (offset + idx))
  | [], _, _, _, h => by simp at h
  | b :: rest, offset, 0, isLive, h => by
    simp at h
    subst h
    rfl
  | b :: rest, offset, idx + 1, isLive, h => by
    simp at h
    dsimp [buildCanonSlotsAux, getSlotAt]
    rw [getSlotAt_buildCanonSlotsAux lookup rest (offset + 1) idx isLive h]
    have hAdd : offset + 1 + idx = offset + (idx + 1) := by omega
    rw [hAdd]

theorem getSlot_canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val)
    {loc : LocalId} {isLive : Bool} (hMask : liveMask[loc]? = some isLive) :
    (canonicalize liveMask raw).getSlot loc =
      normalizeSlotForMask isLive (raw.getSlot loc) := by
  dsimp [canonicalize, CanonState.getSlot]
  rw [getSlotAt_buildCanonSlotsAux raw.getSlot liveMask 0 loc isLive hMask]
  rw [Nat.zero_add]

/-- **Canonical Denotation Soundness (`denoteCanon_canonicalize`)**:
    Canonicalizing `raw` under `liveMask` preserves its exact live-restricted denotation
    at every local variable `loc : LocalId`. -/
theorem denoteCanon_canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val)
    (loc : LocalId) :
    denoteCanon liveMask (canonicalize liveMask raw) loc =
      denoteRaw liveMask raw loc := by
  dsimp [denoteCanon, denoteRaw]
  cases hMask : liveMask[loc]? with
  | none => rfl
  | some isLive =>
    rw [getSlot_canonicalize liveMask raw hMask]
    exact normalizeSlotForMask_idempotent isLive (raw.getSlot loc)

theorem buildCanonSlotsAux_congr {Val : Type} (f₁ f₂ : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset : Nat),
      (∀ i isLive, mask[i]? = some isLive →
        normalizeSlotForMask isLive (f₁ (offset + i)) =
          normalizeSlotForMask isLive (f₂ (offset + i))) →
      buildCanonSlotsAux f₁ offset mask = buildCanonSlotsAux f₂ offset mask
  | [], _, _ => rfl
  | isLive :: rest, offset, hEq => by
    dsimp [buildCanonSlotsAux]
    have hHead : normalizeSlotForMask isLive (f₁ offset) =
        normalizeSlotForMask isLive (f₂ offset) := by
      have h0 := hEq 0 isLive rfl
      rw [Nat.add_zero] at h0
      exact h0
    rw [hHead]
    congr 1
    apply buildCanonSlotsAux_congr f₁ f₂ rest (offset + 1)
    intro i b hRest
    have hSucc := hEq (i + 1) b hRest
    have hAdd : offset + 1 + i = offset + (i + 1) := by omega
    rw [hAdd]
    exact hSucc

/-- **Canonicalization Idempotence (`canonicalize_idempotent`)**:
    Re-canonicalizing an already-canonicalized state under `liveMask` is a no-op. -/
theorem canonicalize_idempotent {Val : Type} (liveMask : List Bool) (raw : RawState Val) :
    canonicalizeCanon liveMask (canonicalize liveMask raw) =
      canonicalize liveMask raw := by
  dsimp [canonicalizeCanon, canonicalize]
  congr 1
  apply buildCanonSlotsAux_congr _ raw.getSlot liveMask 0
  intro i isLive hMask
  rw [Nat.zero_add]
  change normalizeSlotForMask isLive ((canonicalize liveMask raw).getSlot i) =
    normalizeSlotForMask isLive (raw.getSlot i)
  rw [getSlot_canonicalize liveMask raw hMask]
  exact normalizeSlotForMask_idempotent isLive (raw.getSlot i)

/-- **Canonical Completeness & Soundness (`canonicalize_eq_iff_live_equiv`)**:
    Two `RawState`s canonicalize to the **exact same syntactic `CanonState`** if and only
    if they are `LiveEquiv` under `liveMask`. -/
theorem canonicalize_eq_of_live_equiv {Val : Type} {liveMask : List Bool}
    {raw₁ raw₂ : RawState Val} (hEquiv : LiveEquiv liveMask raw₁ raw₂) :
    canonicalize liveMask raw₁ = canonicalize liveMask raw₂ := by
  dsimp [canonicalize]
  congr 1
  apply buildCanonSlotsAux_congr raw₁.getSlot raw₂.getSlot liveMask 0
  intro i isLive hMask
  rw [Nat.zero_add]
  exact (normalizeSlotForMask_eq_iff isLive _ _).2 (hEquiv i isLive hMask)

theorem live_equiv_of_canonicalize_eq {Val : Type} {liveMask : List Bool}
    {raw₁ raw₂ : RawState Val}
    (hEq : canonicalize liveMask raw₁ = canonicalize liveMask raw₂) :
    LiveEquiv liveMask raw₁ raw₂ := by
  intro i isLive hMask
  refine (normalizeSlotForMask_eq_iff isLive _ _).1 ?_
  have h1 := getSlot_canonicalize liveMask raw₁ hMask
  have h2 := getSlot_canonicalize liveMask raw₂ hMask
  rw [hEq] at h1
  rw [← h1, ← h2]

theorem canonicalize_eq_iff_live_equiv {Val : Type} (liveMask : List Bool)
    (raw₁ raw₂ : RawState Val) :
    canonicalize liveMask raw₁ = canonicalize liveMask raw₂ ↔
      LiveEquiv liveMask raw₁ raw₂ :=
  ⟨live_equiv_of_canonicalize_eq, canonicalize_eq_of_live_equiv⟩


/-!
### 2.1 Negative Theorem: Asymmetric Diamond Branches Defeat Raw State Syntactic Join
-/

/-- Initial raw state for a 3-local MIR body (`_0` return, `_1` live accum, `_2` branch-local temp):
    `_0` and `_1` start `.live 10 0 false none`, `_2` starts `.dead 0`. -/
def diamondRawInit : RawState Nat :=
  ((({ numLocals := 3, writeLog := [] } : RawState Nat).assign 0 10).assign 1 20)

/-- Left diamond branch: writes `_0 := 100`, then `_1 := 200`, and uses temporary `_2`
    (`StorageLive(_2); _2 := 999; StorageDead(_2)`). -/
def rawAfterLeft : RawState Nat :=
  let st₁ := (diamondRawInit.assign 0 100).assign 1 200
  (((st₁.storageLive 2).assign 2 999).storageDead 2)

/-- Right diamond branch: writes `_1 := 200` first, then `_0 := 100`, without touching `_2`. -/
def rawAfterRight : RawState Nat :=
  (diamondRawInit.assign 1 200).assign 0 100

/-- Join-point liveness mask at the diamond merge: `_0` and `_1` are live, `_2` is dead. -/
def diamondLiveMask : List Bool := [true, true, false]

/-- **Negative Theorem (`raw_asymmetric_diamond_Syntactic_ne_yet_canon_eq`)**:
    Asymmetric `if/else` diamond branches (out-of-order writes to live locals `_0, _1`
    plus a branch-local unborrowed temporary `_2` in the left branch) produce:
    1. Syntactically **distinct** raw states (`rawAfterLeft ≠ rawAfterRight`), which
       defeats any join cache or structural equality check on raw history-dependent states,
    2. Yet **identical** live-restricted denotations (`denoteRaw diamondLiveMask rawAfterLeft =
       denoteRaw diamondLiveMask rawAfterRight`), and
    3. Syntactically **identical** canonical states (`canonicalize diamondLiveMask rawAfterLeft =
       canonicalize diamondLiveMask rawAfterRight`)! -/
theorem raw_asymmetric_diamond_syntactic_ne_yet_canon_eq :
    rawAfterLeft ≠ rawAfterRight ∧
      (∀ loc, denoteRaw diamondLiveMask rawAfterLeft loc =
        denoteRaw diamondLiveMask rawAfterRight loc) ∧
      canonicalize diamondLiveMask rawAfterLeft =
        canonicalize diamondLiveMask rawAfterRight := by
  refine ⟨by decide, ?_, rfl⟩
  · intro loc
    rw [← denoteCanon_canonicalize diamondLiveMask rawAfterLeft loc]
    rw [← denoteCanon_canonicalize diamondLiveMask rawAfterRight loc]
    rfl

/-- Strengthened negative witness: the two raw states are **observationally identical on every
    local** (including the dead temporary `_2` and all out-of-range locals) — the
    `rawAfterLeft ≠ rawAfterRight` failure is purely syntactic write-history. -/
theorem raw_asymmetric_diamond_pointwise_eq (loc : LocalId) :
    rawAfterLeft.getSlot loc = rawAfterRight.getSlot loc := by
  rcases loc with _ | _ | _ | n <;> rfl

/-- All three diamond raw states (`diamondRawInit`, `rawAfterLeft`, `rawAfterRight`) satisfy
    `RawState.WF` (`loc < numLocals = 3` for every entry in `writeLog`). -/
theorem diamondRawStates_wf :
    diamondRawInit.WF ∧ rawAfterLeft.WF ∧ rawAfterRight.WF := by
  dsimp [diamondRawInit, rawAfterLeft, rawAfterRight, RawState.WF, RawWriteLogWF,
    RawState.assign, RawState.storageLive, RawState.storageDead, RawState.putSlot]
  repeat first | refine ⟨?_, ?_⟩ | decide | trivial


/-!
### 2.2 CPS Spine Forcing (`forceList`, `forceCanonState`)
-/

/-- Continuation-passing **spine** evaluator (`c19b8fce8` `forceList`): pattern-matches every
    cons cell of the list before invoking continuation `k` on the reconstructed spine
    (elements are passed through untouched; see `forceSlotsAux` for element forcing). -/
def forceListAux {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k =>
    forceListAux xs (fun xs' => k (x :: xs'))

def forceList {α : Type} (xs : List α) : List α :=
  forceListAux xs (fun ys => ys)

/-- CPS constructor forcing of a single slot: matches the slot's head constructor (and
    re-binds its fields) before invoking `k`, so `k` never receives a pending slot thunk. -/
def forceSlot {Val β : Type} (s : Slot Val) (k : Slot Val → β) : β :=
  match s with
  | .dead g => k (.dead g)
  | .uninit g => k (.uninit g)
  | .live v g b loan => k (.live v g b loan)

/-- Spine **and element** CPS forcing of a slot list (`c19b8fce8` `forceLocals` analogue):
    every cons cell and every slot's head constructor is matched before `k` runs on the
    reconstructed list, so no `setSlotAt` / `buildCanonSlotsAux` redex survives into `k`. -/
def forceSlotsAux {Val β : Type} : List (Slot Val) → (List (Slot Val) → β) → β
  | [], k => k []
  | s :: rest, k => forceSlot s (fun s' => forceSlotsAux rest (fun rest' => k (s' :: rest')))

/-- Force the slot spine and every slot constructor of a `CanonState` before invoking `k`.
    Applied by `symEvalCfgGvn` at every block boundary and by `mergeJoinStates` after every
    join. (With closed `SymId` payloads the symbolic states never contain free variables, so
    this is defence-in-depth against the `hasFVar` WHNF-cache bypass rather than a
    load-bearing optimization in this prototype.) -/
def forceCanonState {Val β : Type} (st : CanonState Val) (k : CanonState Val → β) : β :=
  forceSlotsAux st.slots (fun slots' => k { slots := slots' })

/-- **CPS Spine-Forcing Equivalence (`forceListAux_eq`)**:
    `forceListAux xs k` is propositionally equal to `k xs` for every list `xs` and
    continuation `k`. -/
theorem forceListAux_eq {α β : Type} :
    ∀ (xs : List α) (k : List α → β),
      forceListAux xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    dsimp [forceListAux]
    rw [forceListAux_eq xs (fun xs' => k (x :: xs'))]

theorem forceList_eq {α : Type} (xs : List α) :
    forceList xs = xs :=
  forceListAux_eq xs (fun ys => ys)

theorem forceSlot_eq {Val β : Type} (s : Slot Val) (k : Slot Val → β) :
    forceSlot s k = k s := by
  cases s <;> rfl

theorem forceSlotsAux_eq {Val β : Type} :
    ∀ (ss : List (Slot Val)) (k : List (Slot Val) → β), forceSlotsAux ss k = k ss
  | [], _ => rfl
  | s :: rest, k => by
    dsimp only [forceSlotsAux]
    rw [forceSlot_eq]
    exact forceSlotsAux_eq rest (fun rest' => k (s :: rest'))

theorem forceCanonState_eq {Val β : Type} (st : CanonState Val) (k : CanonState Val → β) :
    forceCanonState st k = k st := by
  dsimp [forceCanonState]
  rw [forceSlotsAux_eq st.slots (fun slots' => k { slots := slots' })]

end Anneal.Rustc.V2026_06_01.SymbolicEval
