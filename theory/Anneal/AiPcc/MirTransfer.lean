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
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Anneal.Firewall
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct
import Anneal.AiPcc.MirBridge

namespace Anneal.AiPcc

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# Single-Step MIR Abstract Transfer and Soundness (`Anneal.AiPcc.MirTransfer`)

Computable abstract transfer functions for MIR constants (`evalConstLitAbs`),
operands (`evalOperandAbs`), rvalues (`evalRvalueAbs`), statements
(`stepStmtAbs`), and terminators (`stepTermAbs`) over `MirAbsEnv`, together
with kernel-checked one-step fault-freedom and soundness theorems stated
directly against `evalOperand`, `evalRvalue`, `evalStmt`, and `evalTerminator`
of `Trusted.Rustc.V2026_06_01.MirSemantics`.

Supported fragment (everything else has no abstract successor, so no
certificate passes if a reachable block uses it):

* integer (`UintTy`), `bool`, and `()` constants; `Copy` / `Move` of
  unprojected scalar/bool/unit/`(u, bool)` locals (`Move` leaves the source
  `LocalSlot.uninit` and clears guards mentioning it); and `.field 0` /
  `.field 1` projections on initialized `(u, bool)` checked-arithmetic tuples;
* signed (`IntTy`) constants, locals, copy aliases, sign-agnostic arithmetic,
  mixed-width/mixed-signedness shifts (exact `shr` on non-negative or exact
  values), `UnOp.not` (`AbsVal.bitNot`), wrapping `UnOp.neg`, exact biased
  widening `intToInt` casts (`sintCastAbs`), and checked (`*WithOverflow`
  `(i, bool)` tuples, with `.sgtConst`/`.sleConst` overflow relational guards
  on constant-operand signed add/sub) arithmetic. Signed ranges are decided
  in the order-preserving biased coordinate
  `signedBias w x = (x + 2^(w-1)) mod 2^w`
  of `Anneal.AiPcc.ReducedProduct`:
  * `addUnchecked` / `subUnchecked` are accepted when
    `AbsVal.noSignedOverflowAdd` / `AbsVal.noSignedOverflowSub` hold (so
    sign-straddling ranges such as `[-100, 100] + 10` verify), and `div` /
    `rem` when `AbsVal.safeSignedDiv` excludes `/ 0` and `INT_MIN / -1`;
    `mulUnchecked` is accepted on a zero operand, on non-negative operands
    with a small product, on two exact operands whose product fits, and on
    bounded signed intervals (including sign-straddling and opposite-sign
    `INT_MIN` boundary products) via `sintNoOverflowMulBiased` (`sintMulOk`);
  * `<`, `<=`, `>`, `>=`, `==`, `!=` fold through `AbsVal.decideSlt?` /
    `AbsVal.decideSle?` / `AbsVal.decideEq?` and synthesize
    arbitrary-constant `.sleConst` / `.sgtConst` / `.seqConst` / `.sneConst`
    guards (`x < c` is `x <= c - 1`, with `x < INT_MIN` folded to `false`),
    keeping register-register `.ueqReg` / `.uneReg` guards and same-sign
    unsigned order guards;
  * `CastKind.intToInt` supports every widening and narrowing cast among
    `uint` / `bool` / `sint` sources and `uint` / `sint` targets, folding
    exact negative widening constants with `signExtendBits`;
* integer `switchInt` discriminants of either signedness share one edge
  transfer (`intSwitchEdges`), refining with `.ueqConst` / `.uneConst` on
  unsigned and `.seqConst` / `.sneConst` on signed discriminants;
* unsigned wrapping, checked (`*WithOverflow`), unchecked (overflow-free), and
  `div` / `rem` (nonzero divisor) arithmetic, bitwise operations, shifts,
  boolean binary operations, comparisons recording `RelGuard`s, `UnOp.not`
  (`UnOp.neg` on an unsigned operand is rejected, as in Rust), tuple
  `(u, bool)` aggregates, and `copyForDeref`;
* `assign` to unprojected locals, `storageLive`, `storageDead`, `deinit`,
  `placeMention`, `retag` on tracked scalar/bool/unit/pair places,
  `intrinsic (.assume _)`, and no-op statements;
* `goto`, `switchInt` (with exact-match pruning, per-branch + `otherwise`
  refinement, and unreachable-branch elimination), `assert` (certified to
  pass), `drop` of live unprojected locals, and root-frame `return`.

Unoptimized `Runtime(PostCleanup)` MIR routes comparison operands through
temporaries (`_3 = copy _1; _4 = Lt(move _3, ..)`). An assignment
`_t = copy _src` therefore records the copy alias `.uintCopy u a src`, and
reading `_t` (by `Copy` or `Move`) reports `_src` as the source local, so the
synthesized `RelGuard` constrains `_src` itself; writes to `_src` drop the
alias (`setMirAbsSlot`).

The statement and terminator theorems assume the root-frame invariants
`activeProtectors = []` (and `callStack = []` for `return`), which every
supported step preserves. `stepMirFn_stmt_sound` / `stepMirFn_term_sound`
lift them to the machine coalgebra `stepMirFn` (root frame, supported phase),
and `entryEnv_sound` / `initMachineState_root` describe the initial state of
`initMachineState`, for the certificate checker in `Anneal.AiPcc.MirPcc`.

Proof engineering. Soundness proofs select operator-group lemmas by
unification (`exact hGo _ rfl h`) instead of trying every operator in turn,
open definitions with `unfold f at h; dsimp only at h` (one `eq_def` rewrite
and `iota`/`zeta` steps) rather than `simp only [f]` (which realizes one
equation lemma and one matcher splitter per constructor), state each trusted
evaluator arm once as a bridging lemma (`evalRvalue_binaryOp_scalar`,
`evalRvalue_cast_intToInt_scalar`, ...) whose proof head-normalizes the
evaluator with `conv => lhs; whnf` (stopping at the first stuck `match`
instead of simplifying every arm), and eliminate `ite` through the
`@Decidable.casesOn` eliminators of `Anneal.Firewall`.
-/

/-! ## 1. Abstract Operand Values -/

/-- Abstract evaluated operand, optionally remembering the copied source local
`srcReg?` (used to synthesize relational comparison guards). Signed values
(`.sint`) and checked signed tuples (`.sintBoolPair`) are tracked by their bit
pattern at width `uintWidth (intTwin i)`. -/
inductive MirAbsVal where
  | uint (u : UintTy) (a : AbsVal) (srcReg? : Option Nat)
  | bool (b : BoolAbs)
  | unit
  | uintBoolPair (u : UintTy) (a : AbsVal) (ov : BoolAbs)
  | sint (i : IntTy) (a : AbsVal) (srcReg? : Option Nat)
  | sintBoolPair (i : IntTy) (a : AbsVal) (ov : BoolAbs)

/-- Abstract terminator outcome: a verified root-frame `return` with
initialized `_0` slot, or a list of feasible `(target, refinedEnv)` edges. -/
inductive TermAbsOutcome where
  | ret (retSlot : MirAbsSlot)
  | edges (succs : List (Nat × MirAbsEnv))

/-- Integer type of a `switchInt` discriminant: unsigned (`UintTy`) or signed
(`IntTy`, tracked by bit pattern at its unsigned twin). -/
inductive SwitchIntTy where
  | unsigned (u : UintTy)
  | signed (i : IntTy)

/-- Four-constructor projection of the `RigidTy` kinds tracked by AI-PCC
(concentrates all 25-constructor `RigidTy` case analysis into one lemma). -/
inductive AiRigidTy where
  | uint (u : UintTy)
  | int (i : IntTy)
  | bool
  | tuple (ts : List RigidTy)

/-- Six-constructor projection of comparison operators (keeps proof case splits
to 6 branches instead of 26 over all `BinOp`s). -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge

/-- Four-constructor projection of shift operators (keeps shift soundness proofs
to 5 branches instead of 26 over all `BinOp`s). -/
inductive ShiftOp where
  | shl | shlUnchecked | shr | shrUnchecked

/-- Abstract slot stored by an assignment of `av` (a value copied from local
`r` records `.uintCopy u a r` or `.sintCopy i a r`). -/
def MirAbsVal.toSlot : MirAbsVal → MirAbsSlot
  | .uint u a none => .uint u a
  | .uint u a (some r) => .uintCopy u a r
  | .bool b => .bool b
  | .unit => .unit true
  | .uintBoolPair u a ov => .uintBoolPair u a ov
  | .sint i a none => .sint i a
  | .sint i a (some r) => .sintCopy i a r
  | .sintBoolPair i a ov => .sintBoolPair i a ov

/-- `av` has MIR type kind `k`. -/
def MirAbsVal.kindOk (av : MirAbsVal) (k : RigidTy) : Prop :=
  match av with
  | .uint u _ _ => k = .uint u
  | .bool _ => k = .bool
  | .unit => k = .tuple []
  | .uintBoolPair u _ _ => k = .tuple [.uint u, .bool]
  | .sint i _ _ => k = .int i
  | .sintBoolPair i _ _ => k = .tuple [.int i, .bool]

def rigidTyToAi? : RigidTy → Option AiRigidTy
  | .uint u => some (.uint u)
  | .int i => some (.int i)
  | .bool => some .bool
  | .tuple ts => some (.tuple ts)
  | _ => none

def AiRigidTy.toRigid : AiRigidTy → RigidTy
  | .uint u => .uint u
  | .int i => .int i
  | .bool => .bool
  | .tuple ts => .tuple ts

private theorem rigidTyToAi?_eq {k : RigidTy} {a : AiRigidTy}
    (h : rigidTyToAi? k = some a) : k = a.toRigid := by
  cases k with
  | uint u => cases h; rfl
  | int i => cases h; rfl
  | bool => cases h; rfl
  | tuple ts => cases h; rfl
  | _ => nomatch h

def rigidTyUint? (k : RigidTy) : Option UintTy :=
  match rigidTyToAi? k with
  | some (.uint u) => some u
  | _ => none

def rigidTyInt? (k : RigidTy) : Option IntTy :=
  match rigidTyToAi? k with
  | some (.int i) => some i
  | _ => none

def rigidTyIsBool (k : RigidTy) : Bool :=
  match rigidTyToAi? k with
  | some .bool => true
  | _ => false

def rigidTyIsUnit (k : RigidTy) : Bool :=
  match rigidTyToAi? k with
  | some (.tuple []) => true
  | _ => false

def rigidTyUintBoolPair? (k : RigidTy) : Option UintTy :=
  match rigidTyToAi? k with
  | some (.tuple [t0, t1]) =>
    match rigidTyUint? t0 with
    | some u =>
      match rigidTyIsBool t1 with
      | true => some u
      | false => none
    | none => none
  | _ => none

def rigidTyIntBoolPair? (k : RigidTy) : Option IntTy :=
  match rigidTyToAi? k with
  | some (.tuple [t0, t1]) =>
    match rigidTyInt? t0 with
    | some i =>
      match rigidTyIsBool t1 with
      | true => some i
      | false => none
    | none => none
  | _ => none

private theorem rigidTyUint?_eq {k : RigidTy} {u : UintTy}
    (h : rigidTyUint? k = some u) : k = .uint u := by
  unfold rigidTyUint? at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | uint u' => injection h with h; subst h; exact rigidTyToAi?_eq ha
    | _ => nomatch h

private theorem rigidTyInt?_eq {k : RigidTy} {i : IntTy}
    (h : rigidTyInt? k = some i) : k = .int i := by
  unfold rigidTyInt? at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | int i' => injection h with h; subst h; exact rigidTyToAi?_eq ha
    | _ => nomatch h

private theorem rigidTyIsBool_eq {k : RigidTy}
    (h : rigidTyIsBool k = true) : k = .bool := by
  unfold rigidTyIsBool at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | bool => exact rigidTyToAi?_eq ha
    | _ => nomatch h

private theorem rigidTyIsUnit_eq {k : RigidTy}
    (h : rigidTyIsUnit k = true) : k = .tuple [] := by
  unfold rigidTyIsUnit at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | tuple ts =>
      cases ts with
      | nil => exact rigidTyToAi?_eq ha
      | cons _ _ => nomatch h
    | _ => nomatch h

private theorem rigidTyUintBoolPair?_eq {k : RigidTy} {u : UintTy}
    (h : rigidTyUintBoolPair? k = some u) : k = .tuple [.uint u, .bool] := by
  unfold rigidTyUintBoolPair? at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | tuple ts =>
      cases ts with
      | nil => nomatch h
      | cons t0 rest =>
        cases rest with
        | nil => nomatch h
        | cons t1 rest2 =>
          cases rest2 with
          | cons _ _ => nomatch h
          | nil =>
            dsimp only at h
            cases hu : rigidTyUint? t0 with
            | none => rw [hu] at h; nomatch h
            | some u' =>
              rw [hu] at h; dsimp only at h
              cases hb : rigidTyIsBool t1 with
              | false => rw [hb] at h; nomatch h
              | true =>
                rw [hb] at h; cases h
                have hk := rigidTyToAi?_eq ha
                rw [rigidTyUint?_eq hu, rigidTyIsBool_eq hb] at hk
                exact hk
    | _ => nomatch h

private theorem rigidTyIntBoolPair?_eq {k : RigidTy} {i : IntTy}
    (h : rigidTyIntBoolPair? k = some i) : k = .tuple [.int i, .bool] := by
  unfold rigidTyIntBoolPair? at h
  cases ha : rigidTyToAi? k with
  | none => rw [ha] at h; nomatch h
  | some a =>
    rw [ha] at h
    cases a with
    | tuple ts =>
      cases ts with
      | nil => nomatch h
      | cons t0 rest =>
        cases rest with
        | nil => nomatch h
        | cons t1 rest2 =>
          cases rest2 with
          | cons _ _ => nomatch h
          | nil =>
            dsimp only at h
            cases hi : rigidTyInt? t0 with
            | none => rw [hi] at h; nomatch h
            | some i' =>
              rw [hi] at h; dsimp only at h
              cases hb : rigidTyIsBool t1 with
              | false => rw [hb] at h; nomatch h
              | true =>
                rw [hb] at h; cases h
                have hk := rigidTyToAi?_eq ha
                rw [rigidTyInt?_eq hi, rigidTyIsBool_eq hb] at hk
                exact hk
    | _ => nomatch h

/-- Decidable check that `av` has MIR type kind `k`. -/
def MirAbsVal.kindMatches (av : MirAbsVal) (k : RigidTy) : Bool :=
  match av with
  | .uint u _ _ =>
    match rigidTyUint? k with
    | some u' => uintTyBeq u u'
    | none => false
  | .bool _ => rigidTyIsBool k
  | .unit => rigidTyIsUnit k
  | .uintBoolPair u _ _ =>
    match rigidTyUintBoolPair? k with
    | some u' => uintTyBeq u u'
    | none => false
  | .sint i _ _ =>
    match rigidTyInt? k with
    | some i' => intTyBeq i i'
    | none => false
  | .sintBoolPair i _ _ =>
    match rigidTyIntBoolPair? k with
    | some i' => intTyBeq i i'
    | none => false

theorem mirAbsVal_kindOk_of_kindMatches {av : MirAbsVal} {k : RigidTy}
    (h : av.kindMatches k = true) : av.kindOk k := by
  cases av with
  | uint u a src =>
    unfold MirAbsVal.kindMatches at h
    cases hk : rigidTyUint? k with
    | none => rw [hk] at h; nomatch h
    | some u' =>
      rw [hk] at h
      exact Eq.trans (rigidTyUint?_eq hk)
        (congrArg RigidTy.uint (uintTy_eq_of_beq h).symm)
  | bool b => exact rigidTyIsBool_eq h
  | unit => exact rigidTyIsUnit_eq h
  | uintBoolPair u a ov =>
    unfold MirAbsVal.kindMatches at h
    cases hk : rigidTyUintBoolPair? k with
    | none => rw [hk] at h; nomatch h
    | some u' =>
      rw [hk] at h
      exact Eq.trans (rigidTyUintBoolPair?_eq hk)
        (congrArg (fun u => RigidTy.tuple [.uint u, .bool])
          (uintTy_eq_of_beq h).symm)
  | sint i a src =>
    unfold MirAbsVal.kindMatches at h
    cases hk : rigidTyInt? k with
    | none => rw [hk] at h; nomatch h
    | some i' =>
      rw [hk] at h
      exact Eq.trans (rigidTyInt?_eq hk)
        (congrArg RigidTy.int (intTy_eq_of_beq h).symm)
  | sintBoolPair i a ov =>
    unfold MirAbsVal.kindMatches at h
    cases hk : rigidTyIntBoolPair? k with
    | none => rw [hk] at h; nomatch h
    | some i' =>
      rw [hk] at h
      exact Eq.trans (rigidTyIntBoolPair?_eq hk)
        (congrArg (fun i => RigidTy.tuple [.int i, .bool])
          (intTy_eq_of_beq h).symm)

/-- Concrete denotation of an evaluated operand value `v` in frame `locals`. -/
def MirAbsVal.denote (locals : List LocalSlot) (av : MirAbsVal) (v : Value) :
    Prop :=
  match av with
  | .uint u a src =>
    a.isInit = true ∧
    match v with
    | .scalar sc =>
      sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
      match src with
      | none => True
      | some r => localUintNat? locals r u = some sc.bits
    | _ => False
  | .bool ba => ba.denote locals (some v)
  | .unit => v = .unit ∨ v = .aggregate 0 []
  | .uintBoolPair u a ov =>
    a.isInit = true ∧ ov.isInit = true ∧
    match v with
    | .aggregate 0 [.scalar sc, vb] =>
      sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
      ov.denote locals (some vb)
    | _ => False
  | .sint i a src =>
    a.isInit = true ∧
    match v with
    | .scalar sc =>
      sc.sizeBytes = uintBytes (intTwin i) ∧
      a.denote (uintWidth (intTwin i)) (some sc.bits) ∧
      match src with
      | none => True
      | some r => localUintNat? locals r (intTwin i) = some sc.bits
    | _ => False
  | .sintBoolPair i a ov =>
    a.isInit = true ∧ ov.isInit = true ∧
    match v with
    | .aggregate 0 [.scalar sc, vb] =>
      sc.sizeBytes = uintBytes (intTwin i) ∧
      a.denote (uintWidth (intTwin i)) (some sc.bits) ∧
      ov.denote locals (some vb)
    | _ => False

/-- A signed value denotes exactly what its unsigned twin denotes. -/
theorem mirAbsVal_sint_denote_iff {locals : List LocalSlot} {i : IntTy}
    {a : AbsVal} {src : Option Nat} {v : Value} :
    (MirAbsVal.sint i a src).denote locals v ↔
      (MirAbsVal.uint (intTwin i) a src).denote locals v := Iff.rfl

/-- An evaluated value of kind `ty.kind` denotes the assigned slot. -/
theorem mirAbsVal_toSlot_denote {ty : Ty} {locals : List LocalSlot}
    {av : MirAbsVal} {v : Value} (h : av.denote locals v)
    (hk : av.kindOk ty.kind) : av.toSlot.denote ty locals (.init v) := by
  cases av with
  | uint u a src =>
    cases v with
    | scalar sc =>
      cases src with
      | none => exact ⟨hk, h.2.1, h.2.2.1⟩
      | some r => exact ⟨hk, h.2.1, h.2.2.1, h.2.2.2⟩
    | _ => exact False.elim h.2
  | bool b => exact ⟨hk, h⟩
  | unit => exact ⟨hk, h⟩
  | uintBoolPair u a ov => exact ⟨hk, h.2.2⟩
  | sint i a src =>
    cases v with
    | scalar sc =>
      cases src with
      | none => exact ⟨hk, h.2.1, h.2.2.1⟩
      | some r => exact ⟨hk, h.2.1, h.2.2.1, h.2.2.2⟩
    | _ => exact False.elim h.2
  | sintBoolPair i a ov => exact ⟨hk, h.2.2⟩

theorem mirAbsVal_valueContainsUninit {locals : List LocalSlot}
    {av : MirAbsVal} {v : Value} (h : av.denote locals v) :
    valueContainsUninit v = false := by
  cases av with
  | uint u a src =>
    cases v with
    | scalar sc => rfl
    | _ => exact False.elim h.2
  | bool b =>
    cases boolAbs_denote_some h with
    | intro c hc => rw [hc.1]
  | unit =>
    cases h with
    | inl hv => rw [hv]
    | inr hv => rw [hv]
  | uintBoolPair u a ov =>
    cases v with
    | aggregate tag fs =>
      cases tag with
      | succ _ => exact False.elim h.2.2
      | zero =>
        cases fs with
        | nil => exact False.elim h.2.2
        | cons v0 rest =>
          cases v0 with
          | scalar sc =>
            cases rest with
            | nil => exact False.elim h.2.2
            | cons vb rest2 =>
              cases rest2 with
              | cons _ _ => exact False.elim h.2.2
              | nil =>
                cases boolAbs_denote_some h.2.2.2.2 with
                | intro c hc => rw [hc.1]
          | _ => exact False.elim h.2.2
    | _ => exact False.elim h.2.2
  | sint i a src =>
    cases v with
    | scalar sc => rfl
    | _ => exact False.elim h.2
  | sintBoolPair i a ov =>
    cases v with
    | aggregate tag fs =>
      cases tag with
      | succ _ => exact False.elim h.2.2
      | zero =>
        cases fs with
        | nil => exact False.elim h.2.2
        | cons v0 rest =>
          cases v0 with
          | scalar sc =>
            cases rest with
            | nil => exact False.elim h.2.2
            | cons vb rest2 =>
              cases rest2 with
              | cons _ _ => exact False.elim h.2.2
              | nil =>
                cases boolAbs_denote_some h.2.2.2.2 with
                | intro c hc => rw [hc.1]
          | _ => exact False.elim h.2.2
    | _ => exact False.elim h.2.2

/-- Local deinitialized by `op` when `op` is an unprojected `Move`, else
`none`. -/
def operandMovedLocal? : Operand → Option Nat
  | .move ⟨l, []⟩ => some l
  | _ => none

/-- `op` is an unprojected `Move` (the only supported operand that mutates
`locals`). -/
def operandIsMove (op : Operand) : Bool :=
  match operandMovedLocal? op with
  | some _ => true
  | none => false

theorem absVal_const_isInit {w x : Nat} (hw : validWidth w = true) :
    (AbsVal.const w x).isInit = true := by
  simp only [AbsVal.const, hw, AbsVal.isInit]

theorem absVal_const_denote_lt {w x : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) : (AbsVal.const w x).denote w (some x) := by
  have h := absVal_const_sound (w := w) (c := x) hw
  rw [wrapVal_of_lt hx] at h
  exact h

/-! ## 2. Constants -/

/-- Abstract constant evaluator for unsigned integer, signed integer, `bool`,
and `()` constants. -/
def evalConstLitAbs (c : ConstOperand) : Option MirAbsVal :=
  match c.val with
  | .scalar (.int sc) =>
    match rigidTyUint? c.ty.kind with
    | some u =>
      match Nat.beq sc.sizeBytes (uintBytes u) &&
          Nat.blt sc.bits (modPow2 (uintWidth u)) with
      | true => some (.uint u (AbsVal.const (uintWidth u) sc.bits) none)
      | false => none
    | none =>
      match rigidTyInt? c.ty.kind with
      | some i =>
        match Nat.beq sc.sizeBytes (uintBytes (intTwin i)) &&
            Nat.blt sc.bits (modPow2 (uintWidth (intTwin i))) with
        | true => some (.sint i (AbsVal.const (uintWidth (intTwin i)) sc.bits) none)
        | false => none
      | none =>
        match rigidTyIsBool c.ty.kind with
        | true =>
          match boolOfValue? (.scalar sc) with
          | some b => some (.bool (.exact b .none))
          | none => none
        | false => none
  | .zeroSized =>
    match rigidTyIsUnit c.ty.kind with
    | true => some .unit
    | false => none
  | _ => none

/-- Soundness of `evalConstLitAbs` against `evalOperand` on `.constant c`
(in every frame and context). -/
theorem evalConstLitAbs_sound {c : ConstOperand} {av : MirAbsVal}
    (h : evalConstLitAbs c = some av) :
    ∃ v,
      (∀ (locals : List LocalSlot) (borrows : List BorrowEntry)
        (globals : List CapturedAllocation) (layouts : LayoutTable)
        (callerLocals : List LocalSlot) (cdecls : List LocalDecl)
        (callStack : List SavedCallerFrame),
        evalOperand locals (.constant c) borrows globals layouts callerLocals
          cdecls callStack = .ok v locals) ∧
      (∀ locals, av.denote locals v) ∧ av.kindOk c.ty.kind := by
  cases c with
  | mk ty val =>
    cases val with
    | scalar cs =>
      cases cs with
      | int sc =>
        unfold evalConstLitAbs at h
        dsimp only at h
        cases hU : rigidTyUint? ty.kind with
        | some u =>
          rw [hU] at h; dsimp only at h
          cases hC : (Nat.beq sc.sizeBytes (uintBytes u) &&
              Nat.blt sc.bits (modPow2 (uintWidth u))) with
          | false => rw [hC] at h; nomatch h
          | true =>
            rw [hC] at h
            injection h with h
            subst h
            have hSz := Nat.eq_of_beq_eq_true (bool_and_true_left hC)
            have hLt := lt_of_blt_true (bool_and_true_right hC)
            exact ⟨.scalar sc, fun _ _ _ _ _ _ _ => rfl,
              fun _ => ⟨absVal_const_isInit (uintWidth_valid u), hSz,
                absVal_const_denote_lt (uintWidth_valid u) hLt, True.intro⟩,
              rigidTyUint?_eq hU⟩
        | none =>
          rw [hU] at h; dsimp only at h
          cases hI : rigidTyInt? ty.kind with
          | some i =>
            rw [hI] at h; dsimp only at h
            cases hC : (Nat.beq sc.sizeBytes (uintBytes (intTwin i)) &&
                Nat.blt sc.bits (modPow2 (uintWidth (intTwin i)))) with
            | false => rw [hC] at h; nomatch h
            | true =>
              rw [hC] at h
              injection h with h
              subst h
              have hSz := Nat.eq_of_beq_eq_true (bool_and_true_left hC)
              have hLt := lt_of_blt_true (bool_and_true_right hC)
              exact ⟨.scalar sc, fun _ _ _ _ _ _ _ => rfl,
                fun _ => ⟨absVal_const_isInit (uintWidth_valid (intTwin i)), hSz,
                  absVal_const_denote_lt (uintWidth_valid (intTwin i)) hLt,
                  True.intro⟩,
                rigidTyInt?_eq hI⟩
          | none =>
            rw [hI] at h; dsimp only at h
            cases hB : rigidTyIsBool ty.kind with
            | false => rw [hB] at h; nomatch h
            | true =>
              rw [hB] at h; dsimp only at h
              cases hBv : boolOfValue? (.scalar sc) with
              | none => rw [hBv] at h; nomatch h
              | some b =>
                rw [hBv] at h
                injection h with h
                subst h
                refine ⟨.scalar sc, fun _ _ _ _ _ _ _ => rfl, fun _ => ?_,
                  rigidTyIsBool_eq hB⟩
                unfold MirAbsVal.denote BoolAbs.denote
                dsimp only
                rw [hBv]
                exact ⟨rfl, True.intro⟩
      | ptr _ _ => nomatch h
    | zeroSized =>
      unfold evalConstLitAbs at h
      dsimp only at h
      cases hU : rigidTyIsUnit ty.kind with
      | false => rw [hU] at h; nomatch h
      | true =>
        rw [hU] at h
        injection h with h
        subst h
        exact ⟨.unit, fun _ _ _ _ _ _ _ => rfl, fun _ => Or.inl rfl,
          rigidTyIsUnit_eq hU⟩
    | slice _ _ => nomatch h
    | indirect _ _ => nomatch h
    | unevaluated _ => nomatch h

/-! ## 3. Operands -/

/-- Read field `idx` (`0` = integer scalar, `1` = overflow `bool`) from an
initialized `.uintBoolPair` or `.sintBoolPair` slot. -/
def evalPairFieldAbs (env : MirAbsEnv) (l idx : Nat) (fty : Ty) :
    Option (MirAbsVal × MirAbsEnv) :=
  match get? env l with
  | some (.uintBoolPair u a ov) =>
    match a.isInit && ov.isInit with
    | false => none
    | true =>
      match idx with
      | 0 =>
        match rigidTyUint? fty.kind with
        | some u' =>
          match uintTyBeq u u' with
          | true => some (.uint u a none, env)
          | false => none
        | none => none
      | 1 =>
        match rigidTyIsBool fty.kind with
        | true => some (.bool ov, env)
        | false => none
      | _ => none
  | some (.sintBoolPair i a ov) =>
    match a.isInit && ov.isInit with
    | false => none
    | true =>
      match idx with
      | 0 =>
        match rigidTyInt? fty.kind with
        | some i' =>
          match intTyBeq i i' with
          | true => some (.sint i a none, env)
          | false => none
        | none => none
      | 1 =>
        match rigidTyIsBool fty.kind with
        | true => some (.bool ov, env)
        | false => none
      | _ => none
  | _ => none

/-- Evaluate `copy _l` on a resolved slot `s` of `env`. -/
def evalCopyLocalSlot (l : Nat) (env : MirAbsEnv) :
    MirAbsSlot → Option (MirAbsVal × MirAbsEnv)
  | .uint u a =>
    match a.isInit with
    | true => some (.uint u a (some l), env)
    | false => none
  | .uintCopy u a src =>
    match a.isInit with
    | true => some (.uint u a (some src), env)
    | false => none
  | .sint i a =>
    match a.isInit with
    | true => some (.sint i a (some l), env)
    | false => none
  | .sintCopy i a src =>
    match a.isInit with
    | true => some (.sint i a (some src), env)
    | false => none
  | .bool ba =>
    match ba.isInit with
    | true => some (.bool ba, env)
    | false => none
  | .unit true => some (.unit, env)
  | .uintBoolPair u a ov =>
    match a.isInit && ov.isInit with
    | true => some (.uintBoolPair u a ov, env)
    | false => none
  | .sintBoolPair i a ov =>
    match a.isInit && ov.isInit with
    | true => some (.sintBoolPair i a ov, env)
    | false => none
  | _ => none

/-- Evaluate `move _l` on a resolved slot `s` of `env`. -/
def evalMoveLocalSlot (l : Nat) (env : MirAbsEnv) :
    MirAbsSlot → Option (MirAbsVal × MirAbsEnv)
  | .uint u a =>
    match a.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l (.uint u (AbsVal.uninit (uintWidth u))) env with
      | some env' => some (.uint u a none, env')
      | none => none
  | .uintCopy u a src =>
    match a.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l (.uint u (AbsVal.uninit (uintWidth u))) env with
      | none => none
      | some env' =>
        match Nat.beq src l with
        | true => some (.uint u a none, env')
        | false => some (.uint u a (some src), env')
  | .sint i a =>
    match a.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l (.sint i (AbsVal.uninit (uintWidth (intTwin i)))) env with
      | some env' => some (.sint i a none, env')
      | none => none
  | .sintCopy i a src =>
    match a.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l (.sint i (AbsVal.uninit (uintWidth (intTwin i)))) env with
      | none => none
      | some env' =>
        match Nat.beq src l with
        | true => some (.sint i a none, env')
        | false => some (.sint i a (some src), env')
  | .bool ba =>
    match ba.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l (.bool .uninit) env with
      | some env' => some (.bool (ba.clearGuardIf l), env')
      | none => none
  | .unit true =>
    match setMirAbsSlot l (.unit false) env with
    | some env' => some (.unit, env')
    | none => none
  | .uintBoolPair u a ov =>
    match a.isInit && ov.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l
          (.uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit) env with
      | some env' => some (.uintBoolPair u a (ov.clearGuardIf l), env')
      | none => none
  | .sintBoolPair i a ov =>
    match a.isInit && ov.isInit with
    | false => none
    | true =>
      match setMirAbsSlot l
          (.sintBoolPair i (AbsVal.uninit (uintWidth (intTwin i))) .uninit) env with
      | some env' => some (.sintBoolPair i a (ov.clearGuardIf l), env')
      | none => none
  | _ => none

/-- Abstract operand evaluation for constants, `Copy` / `Move` of unprojected
locals (including `(u, bool)` and `(i, bool)` pairs), and `.field 0` /
`.field 1` projections on initialized checked-arithmetic tuples. An unprojected
`Move` leaves the source slot uninitialized (clearing every guard mentioning
it), mirroring `evalOperand`'s `set? .. .uninit`. Reading a `.uintCopy` or
`.sintCopy` slot reports the alias root `src` as the source local. -/
def evalOperandAbs (env : MirAbsEnv) : Operand → Option (MirAbsVal × MirAbsEnv)
  | .copy p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some s => evalCopyLocalSlot p.local_ env s
      | none => none
    | [.field idx fty] => evalPairFieldAbs env p.local_ idx fty
    | _ => none
  | .move p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some s => evalMoveLocalSlot p.local_ env s
      | none => none
    | [.field idx fty] => evalPairFieldAbs env p.local_ idx fty
    | _ => none
  | .constant c =>
    match evalConstLitAbs c with
    | some av => some (av, env)
    | none => none

theorem operandTy_local {decls : List LocalDecl} {layouts : LayoutTable}
    {l : Nat} {d : LocalDecl} (hD : get? decls l = some d) :
    operandTy decls layouts (.copy ⟨l, []⟩) = some d.ty ∧
      operandTy decls layouts (.move ⟨l, []⟩) = some d.ty := by
  simp only [operandTy, placeTy, hD, resolveProjectedTy]
  exact ⟨trivial, trivial⟩

theorem operandTy_field {decls : List LocalDecl} {layouts : LayoutTable}
    {l idx : Nat} {d : LocalDecl} {fty : Ty} (hD : get? decls l = some d) :
    operandTy decls layouts (.copy ⟨l, [.field idx fty]⟩) = some fty ∧
      operandTy decls layouts (.move ⟨l, [.field idx fty]⟩) = some fty := by
  simp only [operandTy, placeTy, hD, resolveProjectedTy]
  exact ⟨trivial, trivial⟩

/-- `evalOperand` on `copy _l` of an initialized, fully-initialized local. -/
theorem evalOperand_copy_local {locals : List LocalSlot} {l : Nat} {v : Value}
    (hL : get? locals l = some (.init v)) (hU : valueContainsUninit v = false)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (cdecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals
      cdecls callStack = .ok v locals := by
  conv => lhs; whnf
  rw [hL]
  conv => lhs; whnf
  unfold readProjectedValue
  rw [hU]

/-- `evalOperand` on `move _l` of an initialized, fully-initialized local
(the source slot becomes `LocalSlot.uninit`). -/
theorem evalOperand_move_local {locals locals' : List LocalSlot} {l : Nat}
    {v : Value} (hL : get? locals l = some (.init v))
    (hU : valueContainsUninit v = false)
    (hSet : set? locals l .uninit = some locals')
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (cdecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals
      cdecls callStack = .ok v locals' := by
  conv => lhs; whnf
  rw [hL]
  conv => lhs; whnf
  unfold readProjectedValue
  rw [hU]
  conv => lhs; whnf
  rw [hSet]

/-- `evalOperand` on `copy _l.idx` / `move _l.idx` of a non-union local
(a field `move` does not deinitialize the root). -/
theorem evalOperand_field_local {locals : List LocalSlot} {l idx : Nat}
    {fty : Ty} {rootVal v : Value} {layouts : LayoutTable}
    {cdecls : List LocalDecl}
    (hL : get? locals l = some (.init rootVal))
    (hNoU : placeTouchesUnion cdecls layouts ⟨l, [.field idx fty]⟩ = false)
    (hRead : readProjectedValue locals rootVal [.field idx fty] = .ok v)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame) :
    evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals cdecls callStack = .ok v locals ∧
      evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals cdecls callStack = .ok v locals := by
  have hCopy : evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals
      layouts callerLocals cdecls callStack = .ok v locals := by
    conv => lhs; whnf
    rw [hL]
    conv => lhs; whnf
    rw [hNoU]
    conv => lhs; whnf
    rw [hRead]
  exact ⟨hCopy, hCopy⟩

private theorem evalPairFieldAbs_sound {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals : List LocalSlot} {l idx : Nat} {fty : Ty}
    {av : MirAbsVal} (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalPairFieldAbs env l idx fty = some (av, env')) :
    ∃ v d rootVal ts,
      get? decls l = some d ∧
      d.ty.kind = .tuple ts ∧
      get? locals l = some (.init rootVal) ∧
      readProjectedValue locals rootVal [.field idx fty] = .ok v ∧
      env' = env ∧ av.denote locals v ∧ av.kindOk fty.kind := by
  unfold evalPairFieldAbs at hAbs
  cases hS : get? env l with
  | none => rw [hS] at hAbs; nomatch hAbs
  | some s =>
    rw [hS] at hAbs
    cases mirAbsEnv_lookup hEnv hS with
    | intro d hd =>
      cases hd with
      | intro cs hcs =>
        cases s with
        | uintBoolPair u a ov =>
          dsimp only at hAbs
          cases hI : (a.isInit && ov.isInit) with
          | false => rw [hI] at hAbs; nomatch hAbs
          | true =>
            rw [hI] at hAbs; dsimp only at hAbs
            cases uintBoolPair_slot_extract hI hcs.2.2 with
            | intro sc hsc =>
              cases hsc with
              | intro vb hsc =>
                have hL : get? locals l =
                    some (.init (.aggregate 0 [.scalar sc, vb])) := by rw [hcs.2.1, hsc.1]
                cases idx with
                | zero =>
                  cases hFk : rigidTyUint? fty.kind with
                  | none => rw [hFk] at hAbs; nomatch hAbs
                  | some u' =>
                    rw [hFk] at hAbs; dsimp only at hAbs
                    cases hU : uintTyBeq u u' with
                    | false => rw [hU] at hAbs; nomatch hAbs
                    | true =>
                      rw [hU] at hAbs; cases hAbs
                      have hu := uintTy_eq_of_beq hU; subst hu
                      exact ⟨.scalar sc, d, _, _, hcs.1, hcs.2.2.1, hL, rfl, rfl,
                        ⟨bool_and_true_left hI, hsc.2.1, hsc.2.2.1, True.intro⟩,
                        rigidTyUint?_eq hFk⟩
                | succ idx' =>
                  cases idx' with
                  | zero =>
                    cases hFk : rigidTyIsBool fty.kind with
                    | false => rw [hFk] at hAbs; nomatch hAbs
                    | true =>
                      rw [hFk] at hAbs; cases hAbs
                      cases boolAbs_denote_some hsc.2.2.2 with
                      | intro b hb =>
                        have hvb := hb.1; subst hvb
                        exact ⟨_, d, _, _, hcs.1, hcs.2.2.1, hL, rfl, rfl,
                          hsc.2.2.2, rigidTyIsBool_eq hFk⟩
                  | succ _ => nomatch hAbs
        | sintBoolPair i a ov =>
          dsimp only at hAbs
          cases hI : (a.isInit && ov.isInit) with
          | false => rw [hI] at hAbs; nomatch hAbs
          | true =>
            rw [hI] at hAbs; dsimp only at hAbs
            cases sintBoolPair_slot_extract hI hcs.2.2 with
            | intro sc hsc =>
              cases hsc with
              | intro vb hsc =>
                have hL : get? locals l =
                    some (.init (.aggregate 0 [.scalar sc, vb])) := by rw [hcs.2.1, hsc.1]
                cases idx with
                | zero =>
                  cases hFk : rigidTyInt? fty.kind with
                  | none => rw [hFk] at hAbs; nomatch hAbs
                  | some i' =>
                    rw [hFk] at hAbs; dsimp only at hAbs
                    cases hIeq : intTyBeq i i' with
                    | false => rw [hIeq] at hAbs; nomatch hAbs
                    | true =>
                      rw [hIeq] at hAbs; cases hAbs
                      have hi := intTy_eq_of_beq hIeq; subst hi
                      exact ⟨.scalar sc, d, _, _, hcs.1, hcs.2.2.1, hL, rfl, rfl,
                        ⟨bool_and_true_left hI, hsc.2.1, hsc.2.2.1, True.intro⟩,
                        rigidTyInt?_eq hFk⟩
                | succ idx' =>
                  cases idx' with
                  | zero =>
                    cases hFk : rigidTyIsBool fty.kind with
                    | false => rw [hFk] at hAbs; nomatch hAbs
                    | true =>
                      rw [hFk] at hAbs; cases hAbs
                      cases boolAbs_denote_some hsc.2.2.2 with
                      | intro b hb =>
                        have hvb := hb.1; subst hvb
                        exact ⟨_, d, _, _, hcs.1, hcs.2.2.1, hL, rfl, rfl,
                          hsc.2.2.2, rigidTyIsBool_eq hFk⟩
                  | succ _ => nomatch hAbs
        | _ => nomatch hAbs

/-- Slot-level content of `copy _l`: the abstract value read from an
initialized slot denotes the concrete local. -/
private theorem evalCopyLocalSlot_sound {env env' : MirAbsEnv}
    {locals : List LocalSlot} {l : Nat}
    {d : LocalDecl} {cs : LocalSlot} {s : MirAbsSlot} {av : MirAbsVal}
    (hL : get? locals l = some cs)
    (hDenS : s.denote d.ty locals cs)
    (hAbs : evalCopyLocalSlot l env s = some (av, env')) :
    env' = env ∧ ∃ v, get? locals l = some (.init v) ∧
      valueContainsUninit v = false ∧ av.denote locals v ∧
      av.kindOk d.ty.kind := by
  cases s with
  | uint u a =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases uint_slot_extract hI hDenS with
      | intro sc hsc =>
        have hLoc : get? locals l = some (.init (.scalar sc)) := by rw [hL, hsc.1]
        exact ⟨rfl, _, hLoc, rfl,
          ⟨hI, hsc.2.1, hsc.2.2, localUintNat?_of_get? hLoc hsc.2.1⟩, hDenS.1⟩
  | uintCopy u a src =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases uint_slot_extract hI (uintCopy_denote_uint hDenS) with
      | intro sc hsc =>
        have hLoc : get? locals l = some (.init (.scalar sc)) := by rw [hL, hsc.1]
        have hDen := hDenS; rw [hsc.1] at hDen
        exact ⟨rfl, _, hLoc, rfl, ⟨hI, hsc.2.1, hsc.2.2, hDen.2.2.2⟩, hDenS.1⟩
  | sint i a =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases sint_slot_extract hI hDenS with
      | intro sc hsc =>
        have hLoc : get? locals l = some (.init (.scalar sc)) := by rw [hL, hsc.1]
        exact ⟨rfl, _, hLoc, rfl,
          ⟨hI, hsc.2.1, hsc.2.2, localUintNat?_of_get? hLoc hsc.2.1⟩, hDenS.1⟩
  | sintCopy i a src =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases sint_slot_extract hI (sintCopy_denote_sint hDenS) with
      | intro sc hsc =>
        have hLoc : get? locals l = some (.init (.scalar sc)) := by rw [hL, hsc.1]
        have hDen := hDenS; rw [hsc.1] at hDen
        exact ⟨rfl, _, hLoc, rfl, ⟨hI, hsc.2.1, hsc.2.2, hDen.2.2.2⟩, hDenS.1⟩
  | bool ba =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : ba.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases mirAbsSlot_init (s := .bool ba) hI hDenS with
      | intro v hv =>
        have hDen := hDenS; rw [hv.1] at hDen
        exact ⟨rfl, v, by rw [hL, hv.1], hv.2, hDen.2, hDenS.1⟩
  | unit i =>
    cases i with
    | false => nomatch hAbs
    | true =>
      cases hAbs
      cases mirAbsSlot_init (s := .unit true) rfl hDenS with
      | intro v hv =>
        have hDen := hDenS; rw [hv.1] at hDen
        exact ⟨rfl, v, by rw [hL, hv.1], hv.2, hDen.2, hDenS.1⟩
  | uintBoolPair u a ov =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : (a.isInit && ov.isInit) with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases mirAbsSlot_init (s := .uintBoolPair u a ov) hI hDenS with
      | intro v hv =>
        have hDen := hDenS; rw [hv.1] at hDen
        exact ⟨rfl, v, by rw [hL, hv.1], hv.2,
          ⟨bool_and_true_left hI, bool_and_true_right hI, hDen.2⟩, hDenS.1⟩
  | sintBoolPair i a ov =>
    dsimp only [evalCopyLocalSlot] at hAbs
    cases hI : (a.isInit && ov.isInit) with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; cases hAbs
      cases mirAbsSlot_init (s := .sintBoolPair i a ov) hI hDenS with
      | intro v hv =>
        have hDen := hDenS; rw [hv.1] at hDen
        exact ⟨rfl, v, by rw [hL, hv.1], hv.2,
          ⟨bool_and_true_left hI, bool_and_true_right hI, hDen.2⟩, hDenS.1⟩
  | top => nomatch hAbs
  | dead => nomatch hAbs

private theorem evalOperandAbs_copy_local_core {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals : List LocalSlot} {l : Nat}
    {av : MirAbsVal} (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalOperandAbs env (.copy ⟨l, []⟩) = some (av, env')) :
    env' = env ∧ ∃ v d, get? locals l = some (.init v) ∧
      valueContainsUninit v = false ∧ av.denote locals v ∧
      get? decls l = some d ∧ av.kindOk d.ty.kind := by
  dsimp only [evalOperandAbs] at hAbs
  cases hS : get? env l with
  | none => rw [hS] at hAbs; nomatch hAbs
  | some s =>
    rw [hS] at hAbs
    cases mirAbsEnv_lookup hEnv hS with
    | intro d hd =>
      cases hd with
      | intro cs hcs =>
        cases evalCopyLocalSlot_sound hcs.2.1 hcs.2.2 hAbs with
        | intro hEq hv =>
          cases hv with
          | intro v hv =>
            exact ⟨hEq, v, d, hv.1, hv.2.1, hv.2.2.1, hcs.1, hv.2.2.2⟩

/-- Slot-level content of `move _l`: the moved-out value denotes the abstract
value in the frame `locals'` whose slot `l` is `LocalSlot.uninit`, and the
updated abstract frame denotes `locals'`. -/
private theorem evalMoveLocalSlot_sound {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals locals' : List LocalSlot} {l : Nat}
    {d : LocalDecl} {cs : LocalSlot} {s : MirAbsSlot} {av : MirAbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hD : get? decls l = some d) (hL : get? locals l = some cs)
    (hDenS : s.denote d.ty locals cs)
    (hSetC : set? locals l .uninit = some locals')
    (hAbs : evalMoveLocalSlot l env s = some (av, env')) :
    ∃ v, get? locals l = some (.init v) ∧ valueContainsUninit v = false ∧
      av.denote locals' v ∧ mirAbsEnvDenote decls env' locals' ∧
      av.kindOk d.ty.kind := by
  cases s with
  | uint u a =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l (.uint u (AbsVal.uninit (uintWidth u))) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases uint_slot_extract hI hDenS with
        | intro sc hsc =>
          exact ⟨.scalar sc, by rw [hL, hsc.1], rfl,
            ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩,
            setMirAbsSlot_sound hEnv hD hSA hSetC
              ⟨hDenS.1, absVal_uninit_sound_none⟩, hDenS.1⟩
  | uintCopy u a src =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l (.uint u (AbsVal.uninit (uintWidth u))) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; dsimp only at hAbs
        cases uint_slot_extract hI (uintCopy_denote_uint hDenS) with
        | intro sc hsc =>
          have hDen := hDenS; rw [hsc.1] at hDen
          have hEnvM := setMirAbsSlot_sound hEnv hD hSA hSetC
            ⟨hDenS.1, absVal_uninit_sound_none⟩
          cases hB : Nat.beq src l with
          | true =>
            rw [hB] at hAbs; cases hAbs
            exact ⟨.scalar sc, by rw [hL, hsc.1], rfl,
              ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩, hEnvM, hDenS.1⟩
          | false =>
            rw [hB] at hAbs; cases hAbs
            refine ⟨.scalar sc, by rw [hL, hsc.1], rfl,
              ⟨hI, hsc.2.1, hsc.2.2, ?_⟩, hEnvM, hDenS.1⟩
            show localUintNat? locals' src u = some sc.bits
            rw [localUintNat?_set?_ne u hSetC
              (fun hE => nat_ne_of_beq_false hB hE.symm)]
            exact hDen.2.2.2
  | sint i a =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l
          (.sint i (AbsVal.uninit (uintWidth (intTwin i)))) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases sint_slot_extract hI hDenS with
        | intro sc hsc =>
          exact ⟨.scalar sc, by rw [hL, hsc.1], rfl,
            ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩,
            setMirAbsSlot_sound hEnv hD hSA hSetC
              ⟨hDenS.1, absVal_uninit_sound_none⟩, hDenS.1⟩
  | sintCopy i a src =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : a.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l
          (.sint i (AbsVal.uninit (uintWidth (intTwin i)))) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; dsimp only at hAbs
        cases sint_slot_extract hI (sintCopy_denote_sint hDenS) with
        | intro sc hsc =>
          have hDen := hDenS; rw [hsc.1] at hDen
          have hEnvM := setMirAbsSlot_sound hEnv hD hSA hSetC
            ⟨hDenS.1, absVal_uninit_sound_none⟩
          cases hB : Nat.beq src l with
          | true =>
            rw [hB] at hAbs; cases hAbs
            exact ⟨.scalar sc, by rw [hL, hsc.1], rfl,
              ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩, hEnvM, hDenS.1⟩
          | false =>
            rw [hB] at hAbs; cases hAbs
            refine ⟨.scalar sc, by rw [hL, hsc.1], rfl,
              ⟨hI, hsc.2.1, hsc.2.2, ?_⟩, hEnvM, hDenS.1⟩
            show localUintNat? locals' src (intTwin i) = some sc.bits
            rw [localUintNat?_set?_ne (intTwin i) hSetC
              (fun hE => nat_ne_of_beq_false hB hE.symm)]
            exact hDen.2.2.2
  | bool ba =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : ba.isInit with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l (.bool .uninit) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases mirAbsSlot_init (s := .bool ba) hI hDenS with
        | intro v hv =>
          have hDen := hDenS; rw [hv.1] at hDen
          exact ⟨v, by rw [hL, hv.1], hv.2,
            boolAbs_clearGuardIf_denote_update hSetC hDen.2,
            setMirAbsSlot_sound hEnv hD hSA hSetC ⟨hDenS.1, True.intro⟩, hDenS.1⟩
  | unit i =>
    cases i with
    | false => nomatch hAbs
    | true =>
      dsimp only [evalMoveLocalSlot] at hAbs
      cases hSA : setMirAbsSlot l (.unit false) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases mirAbsSlot_init (s := .unit true) rfl hDenS with
        | intro v hv =>
          have hDen := hDenS; rw [hv.1] at hDen
          exact ⟨v, by rw [hL, hv.1], hv.2, hDen.2,
            setMirAbsSlot_sound hEnv hD hSA hSetC ⟨hDenS.1, rfl⟩, hDenS.1⟩
  | uintBoolPair u a ov =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : (a.isInit && ov.isInit) with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l
          (.uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases mirAbsSlot_init (s := .uintBoolPair u a ov) hI hDenS with
        | intro v hv =>
          cases uintBoolPair_slot_extract hI hDenS with
          | intro sc hsc =>
            cases hsc with
            | intro vb hsc =>
              have hvEq : v = .aggregate 0 [.scalar sc, vb] := by
                have h := hv.1; rw [hsc.1] at h; cases h; rfl
              subst hvEq
              exact ⟨_, by rw [hL, hsc.1], hv.2,
                ⟨bool_and_true_left hI,
                  by rw [boolAbs_clearGuardIf_isInit]; exact bool_and_true_right hI,
                  hsc.2.1, hsc.2.2.1,
                  boolAbs_clearGuardIf_denote_update hSetC hsc.2.2.2⟩,
                setMirAbsSlot_sound hEnv hD hSA hSetC
                  ⟨hDenS.1, absVal_uninit_sound_none, True.intro⟩, hDenS.1⟩
  | sintBoolPair i a ov =>
    dsimp only [evalMoveLocalSlot] at hAbs
    cases hI : (a.isInit && ov.isInit) with
    | false => rw [hI] at hAbs; nomatch hAbs
    | true =>
      rw [hI] at hAbs; dsimp only at hAbs
      cases hSA : setMirAbsSlot l
          (.sintBoolPair i (AbsVal.uninit (uintWidth (intTwin i))) .uninit) env with
      | none => rw [hSA] at hAbs; nomatch hAbs
      | some envM =>
        rw [hSA] at hAbs; cases hAbs
        cases mirAbsSlot_init (s := .sintBoolPair i a ov) hI hDenS with
        | intro v hv =>
          cases sintBoolPair_slot_extract hI hDenS with
          | intro sc hsc =>
            cases hsc with
            | intro vb hsc =>
              have hvEq : v = .aggregate 0 [.scalar sc, vb] := by
                have h := hv.1; rw [hsc.1] at h; cases h; rfl
              subst hvEq
              exact ⟨_, by rw [hL, hsc.1], hv.2,
                ⟨bool_and_true_left hI,
                  by rw [boolAbs_clearGuardIf_isInit]; exact bool_and_true_right hI,
                  hsc.2.1, hsc.2.2.1,
                  boolAbs_clearGuardIf_denote_update hSetC hsc.2.2.2⟩,
                setMirAbsSlot_sound hEnv hD hSA hSetC
                  ⟨hDenS.1, absVal_uninit_sound_none, True.intro⟩, hDenS.1⟩
  | top => nomatch hAbs
  | dead => nomatch hAbs

private theorem evalOperandAbs_move_local_core {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals locals' : List LocalSlot} {l : Nat}
    {av : MirAbsVal} (hEnv : mirAbsEnvDenote decls env locals)
    (hSetC : set? locals l .uninit = some locals')
    (hAbs : evalOperandAbs env (.move ⟨l, []⟩) = some (av, env')) :
    ∃ v d, get? locals l = some (.init v) ∧
      valueContainsUninit v = false ∧ av.denote locals' v ∧
      mirAbsEnvDenote decls env' locals' ∧
      get? decls l = some d ∧ av.kindOk d.ty.kind := by
  dsimp only [evalOperandAbs] at hAbs
  cases hS : get? env l with
  | none => rw [hS] at hAbs; nomatch hAbs
  | some s =>
    rw [hS] at hAbs
    cases mirAbsEnv_lookup hEnv hS with
    | intro d hd =>
      cases hd with
      | intro cs hcs =>
        cases evalMoveLocalSlot_sound hEnv hcs.1 hcs.2.1 hcs.2.2 hSetC hAbs with
        | intro v hv =>
          exact ⟨v, d, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hcs.1, hv.2.2.2.2⟩

/-- A successful `move _l` reads a live local, so the concrete write
`set? locals l .uninit` succeeds. -/
private theorem evalOperandAbs_move_local_set {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals : List LocalSlot} {l : Nat}
    {av : MirAbsVal} (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalOperandAbs env (.move ⟨l, []⟩) = some (av, env')) :
    ∃ locals', set? locals l .uninit = some locals' := by
  conv at hAbs => lhs; whnf
  cases hS : get? env l with
  | none => rw [hS] at hAbs; nomatch hAbs
  | some s =>
    cases mirAbsEnv_lookup hEnv hS with
    | intro d hd =>
      cases hd with
      | intro cs hcs => exact set?_some_of_get? LocalSlot.uninit hcs.2.1

/-- Soundness of `evalOperandAbs` against `evalOperand` for every borrow/global/
caller context and either body `decls` or erased `[]` (as in
`evalOperandWithBodyCast`). -/
theorem evalOperandAbs_sound {decls : List LocalDecl} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {op : Operand} {av : MirAbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalOperandAbs env op = some (av, env')) :
    ∃ v locals',
      (∀ (borrows : List BorrowEntry) (globals : List CapturedAllocation)
        (layouts : LayoutTable) (callerLocals : List LocalSlot)
        (cdecls : List LocalDecl) (callStack : List SavedCallerFrame),
        (cdecls = decls ∨ cdecls = []) →
        evalOperand locals op borrows globals layouts callerLocals cdecls
          callStack = .ok v locals') ∧
      av.denote locals' v ∧
      mirAbsEnvDenote decls env' locals' ∧
      (operandMovedLocal? op = none → locals' = locals) ∧
      (∀ l, operandMovedLocal? op = some l →
        ∃ newCs, set? locals l newCs = some locals') ∧
      (∀ layouts, ∃ ty, operandTy decls layouts op = some ty ∧
        av.kindOk ty.kind) := by
  have hNoMove : ∀ {op0 : Operand}, operandMovedLocal? op0 = none →
      ∀ l, operandMovedLocal? op0 = some l →
        ∃ newCs, set? locals l newCs = some locals := by
    intro op0 hN l hS
    rw [hN] at hS
    nomatch hS
  have hField : ∀ (l idx : Nat) (fty : Ty) (isMove : Bool),
      evalPairFieldAbs env l idx fty = some (av, env') →
      ∃ v, (∀ (borrows : List BorrowEntry) (globals : List CapturedAllocation)
          (layouts : LayoutTable) (callerLocals : List LocalSlot)
          (cdecls : List LocalDecl) (callStack : List SavedCallerFrame),
          (cdecls = decls ∨ cdecls = []) →
          evalOperand locals
            (match isMove with
             | false => .copy ⟨l, [.field idx fty]⟩
             | true => .move ⟨l, [.field idx fty]⟩)
            borrows globals layouts callerLocals cdecls callStack =
              .ok v locals) ∧
        av.denote locals v ∧ mirAbsEnvDenote decls env' locals ∧
        (∀ layouts, ∃ ty, operandTy decls layouts
            (match isMove with
             | false => .copy ⟨l, [.field idx fty]⟩
             | true => .move ⟨l, [.field idx fty]⟩) = some ty ∧
          av.kindOk ty.kind) := by
    intro l idx fty isMove hF
    cases evalPairFieldAbs_sound hEnv hF with
    | intro v hv =>
      cases hv with
      | intro d hd =>
        cases hd with
        | intro rootVal hr =>
          cases hr with
          | intro ts hr =>
            have hE := hr.2.2.2.2.1
            subst hE
            refine ⟨v, ?_, hr.2.2.2.2.2.1, hEnv, ?_⟩
            · intro borrows globals layouts callerLocals cdecls callStack hCd
              have hNoU : placeTouchesUnion cdecls layouts
                  ⟨l, [.field idx fty]⟩ = false := by
                cases hCd with
                | inl hEq =>
                  subst hEq
                  exact placeTouchesUnion_tuple_field_false _ layouts
                    hr.1 hr.2.1
                | inr hNil => subst hNil; rfl
              have hEv := evalOperand_field_local hr.2.2.1 hNoU hr.2.2.2.1
                borrows globals callerLocals callStack
              cases isMove with
              | false => exact hEv.1
              | true => exact hEv.2
            · intro layouts
              cases isMove with
              | false => exact ⟨fty, (operandTy_field hr.1).1, hr.2.2.2.2.2.2⟩
              | true => exact ⟨fty, (operandTy_field hr.1).2, hr.2.2.2.2.2.2⟩
  cases op with
  | constant c =>
    unfold evalOperandAbs at hAbs
    dsimp only at hAbs
    cases hC : evalConstLitAbs c with
    | none => rw [hC] at hAbs; nomatch hAbs
    | some av0 =>
      rw [hC] at hAbs
      cases hAbs
      cases evalConstLitAbs_sound hC with
      | intro v hv =>
        refine ⟨v, locals, fun b g lay cl cd cs _ => hv.1 locals b g lay cl cd cs,
          hv.2.1 locals, hEnv, fun _ => rfl, hNoMove rfl, ?_⟩
        intro layouts
        exact ⟨c.ty, rfl, hv.2.2⟩
  | copy p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil =>
        cases evalOperandAbs_copy_local_core hEnv hAbs with
        | intro hE hc =>
          subst hE
          cases hc with
          | intro v hc =>
            cases hc with
            | intro d hc =>
              exact ⟨v, locals,
                fun b g lay cl cd cs _ =>
                  evalOperand_copy_local hc.1 hc.2.1 b g lay cl cd cs,
                hc.2.2.1, hEnv, fun _ => rfl, hNoMove rfl,
                fun _ => ⟨d.ty, (operandTy_local hc.2.2.2.1).1, hc.2.2.2.2⟩⟩
      | cons pe rest =>
        cases pe with
        | field idx fty =>
          cases rest with
          | cons _ _ => nomatch hAbs
          | nil =>
            cases hField l idx fty false hAbs with
            | intro v hv =>
              exact ⟨v, locals, hv.1, hv.2.1, hv.2.2.1, fun _ => rfl,
                hNoMove rfl, hv.2.2.2⟩
        | _ => nomatch hAbs
  | move p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil =>
        cases evalOperandAbs_move_local_set hEnv hAbs with
        | intro locals' hSetC =>
          cases evalOperandAbs_move_local_core hEnv hSetC hAbs with
          | intro v hc =>
            cases hc with
            | intro d hc =>
              refine ⟨v, locals',
                fun b g lay cl cd cs _ =>
                  evalOperand_move_local hc.1 hc.2.1 hSetC b g lay cl cd cs,
                hc.2.2.1, hc.2.2.2.1, (fun h => nomatch h), ?_,
                fun _ => ⟨d.ty, (operandTy_local hc.2.2.2.2.1).2,
                  hc.2.2.2.2.2⟩⟩
              intro r hr
              injection hr with hr
              subst hr
              exact ⟨.uninit, hSetC⟩
      | cons pe rest =>
        cases pe with
        | field idx fty =>
          cases rest with
          | cons _ _ => nomatch hAbs
          | nil =>
            cases hField l idx fty true hAbs with
            | intro v hv =>
              exact ⟨v, locals, hv.1, hv.2.1, hv.2.2.1, fun _ => rfl,
                hNoMove rfl, hv.2.2.2⟩
        | _ => nomatch hAbs

/-! ## 4. Unsigned Value Transfers -/

/-- An `AbsVal` denotation transfers to any wider modulus. -/
theorem absVal_denote_widen {w1 w2 x : Nat} {a : AbsVal}
    (hle : modPow2 w1 ≤ modPow2 w2) (h : a.denote w1 (some x)) :
    a.denote w2 (some x) := by
  cases a with
  | mk i0 tnum wi sc =>
    refine ⟨?_, h.2.1, ?_, h.2.2.2⟩
    · have hI := h.1
      cases i0 with
      | bot => exact hI
      | init =>
        cases hI with
        | intro x' hx' => exact ⟨x', hx'.1, Nat.lt_of_lt_of_le hx'.2 hle⟩
      | uninit => exact Nat.lt_of_lt_of_le hI hle
    · have hW := h.2.2.1
      cases wi with
      | bot => exact hW
      | top => exact Nat.lt_of_lt_of_le hW hle
      | iv lo hi =>
        exact ⟨Nat.lt_of_lt_of_le hW.1 hle, Nat.lt_of_lt_of_le hW.2.1 hle,
          Nat.lt_of_lt_of_le hW.2.2.1 hle, hW.2.2.2⟩

/-- `topInit` refined by an upper bound when one is known. -/
def topBelow (w : Nat) (hi? : Option Nat) : AbsVal :=
  match hi? with
  | some hi => AbsVal.refineUleConst w (AbsVal.topInit w) hi
  | none => AbsVal.topInit w

theorem absVal_topInit_isInit (w : Nat) : (AbsVal.topInit w).isInit = true :=
  rfl

theorem topBelow_sound {w x : Nat} {hi? : Option Nat}
    (hw : validWidth w = true) (hx : x < modPow2 w)
    (hle : ∀ hi, hi? = some hi → x ≤ hi) :
    (topBelow w hi?).denote w (some x) := by
  unfold topBelow
  cases hi? with
  | none => exact absVal_topInit_sound hx
  | some hi =>
    exact absVal_refineUleConst_sound hw (absVal_topInit_sound hx)
      (absVal_topInit_isInit w) (hle hi rfl)

/-- Overflow-freedom check for unsigned multiplication via interval bounds
(defaulting an unconstrained operand upper bound to `2^w - 1`). -/
def AbsVal.noOverflowMul (w : Nat) (a b : AbsVal) : Bool :=
  let h1 :=
    match a.ubound? with
    | some h => h
    | none => modPow2 w - 1
  let h2 :=
    match b.ubound? with
    | some h => h
    | none => modPow2 w - 1
  Nat.blt (h1 * h2) (modPow2 w)

theorem absVal_noOverflowMul_sound {w x y : Nat} {a b : AbsVal}
    (h : AbsVal.noOverflowMul w a b = true) (hx : a.denote w (some x))
    (hy : b.denote w (some y)) : x * y < modPow2 w := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  unfold AbsVal.noOverflowMul at h
  have hX : x ≤ (match a.ubound? with | some hi => hi | none => modPow2 w - 1) := by
    cases hU1 : a.ubound? with
    | some hi => exact absVal_ubound?_sound hU1 hx
    | none => exact Nat.le_sub_one_of_lt hxLt
  have hY : y ≤ (match b.ubound? with | some hi => hi | none => modPow2 w - 1) := by
    cases hU2 : b.ubound? with
    | some hi => exact absVal_ubound?_sound hU2 hy
    | none => exact Nat.le_sub_one_of_lt hyLt
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hX hY) (lt_of_blt_true h)

private theorem mod_wrapVal_of_dvd {w c n : Nat}
    (hDvd : Nat.mod (modPow2 w) c = 0) (hN : Nat.mod n c = 0) :
    Nat.mod (wrapVal w n) c = 0 := by
  let M := modPow2 w
  let q := Nat.div M c
  let k := Nat.div n M
  let r := Nat.mod n M
  have hM : c * q = M := by
    have h := nat_div_add_mod M c
    rw [hDvd, Nat.add_zero] at h
    exact h
  have hDecomp : n = c * (q * k) + r := by
    have h1 := nat_div_add_mod n M
    have h2 : M * k = c * (q * k) := by
      rw [← hM, Nat.mul_assoc]
    change M * k + r = n at h1
    rw [h2] at h1
    exact h1.symm
  have hMod : Nat.mod (c * (q * k) + r) c = Nat.mod r c :=
    Nat.mul_add_mod_self_left c (q * k) r
  rw [← hDecomp] at hMod
  have hZero : Nat.mod r c = 0 := Eq.trans hMod.symm hN
  exact hZero

/-- Constant factor `c > 0` for `StridedCong.cong c 0` on multiplication. -/
def mulCongFactor (w : Nat) (a1 a2 : AbsVal) (noWrap : Bool) : StridedCong :=
  match a2.exactVal? w with
  | some c =>
    match Nat.blt 0 c && (noWrap || Nat.beq (Nat.mod (modPow2 w) c) 0) with
    | true => .cong c 0
    | false => .top
  | none =>
    match a1.exactVal? w with
    | some c =>
      match Nat.blt 0 c && (noWrap || Nat.beq (Nat.mod (modPow2 w) c) 0) with
      | true => .cong c 0
      | false => .top
    | none => .top

/-- Interval/congruence fallback for `mulUintAbs` when neither operand is an
exact `0`/`1` and they are not both exact constants. -/
def mulUintAbsFallback (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.lbound? with
  | some lo1 =>
    match a1.ubound? with
    | some hi1 =>
      match a2.lbound? with
      | some lo2 =>
        match a2.ubound? with
        | some hi2 =>
          match Nat.blt (hi1 * hi2) (modPow2 w) with
          | true =>
            reduceAbsVal w
              ⟨.init, Tnum.top w, .iv (lo1 * lo2) (hi1 * hi2),
                mulCongFactor w a1 a2 true⟩
          | false =>
            reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩
        | none =>
          reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩
      | none =>
        reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩
    | none =>
      reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩
  | none =>
    reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩

/-- Unsigned multiplication transfer: folds exact constants, `0`/`1`
identities, propagates non-wrapping product intervals `[lo1 * lo2, hi1 * hi2]`,
and tracks stride congruence `≡ 0 (mod c)` for constant factors. -/
def mulUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w with
  | some x =>
    match a2.exactVal? w with
    | some y => AbsVal.const w (x * y)
    | none =>
      match x with
      | 0 => AbsVal.const w 0
      | 1 => a2
      | _ => mulUintAbsFallback w a1 a2
  | none =>
    match a2.exactVal? w with
    | some 0 => AbsVal.const w 0
    | some 1 => a1
    | _ => mulUintAbsFallback w a1 a2

private theorem mulCongFactor_sound {w x y : Nat} {a1 a2 : AbsVal}
    {noWrap : Bool} (hx : a1.denote w (some x)) (hy : a2.denote w (some y))
    (hNw : noWrap = true → x * y < modPow2 w) :
    (mulCongFactor w a1 a2 noWrap).denote (wrapVal w (x * y)) := by
  have hFactor : ∀ (c : Nat), (x * y) % c = 0 →
      (match Nat.blt 0 c && (noWrap || Nat.beq (Nat.mod (modPow2 w) c) 0) with
       | true => StridedCong.cong c 0
       | false => StridedCong.top).denote (wrapVal w (x * y)) := by
    intro c hMod0
    cases hC : (Nat.blt 0 c && (noWrap || Nat.beq (Nat.mod (modPow2 w) c) 0)) with
    | false => exact True.intro
    | true =>
      have hcPos : 0 < c := lt_of_blt_true (bool_and_true_left hC)
      have hOr := bool_and_true_right hC
      refine ⟨hcPos, hcPos, ?_⟩
      cases hNwB : noWrap with
      | true =>
        rw [wrapVal_of_lt (hNw hNwB)]
        exact hMod0
      | false =>
        rw [hNwB, Bool.false_or] at hOr
        exact mod_wrapVal_of_dvd (Nat.eq_of_beq_eq_true hOr) hMod0
  unfold mulCongFactor
  cases hE2 : a2.exactVal? w with
  | some c =>
    have h2 := (absVal_exactVal?_sound hE2 hy).1
    cases h2
    exact hFactor y (Nat.mul_mod_left x y)
  | none =>
    cases hE1 : a1.exactVal? w with
    | none => exact True.intro
    | some c =>
      have h1 := (absVal_exactVal?_sound hE1 hx).1
      cases h1
      exact hFactor x (Nat.mul_mod_right x y)

private theorem mulUintAbsFallback_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) :
    (mulUintAbsFallback w a1 a2).denote w (some (wrapVal w (x * y))) := by
  have hWrapLt : wrapVal w (x * y) < modPow2 w := nat_mod_lt _ (modPow2_pos w)
  have hTopCase : (reduceAbsVal w ⟨.init, Tnum.top w, .top,
      mulCongFactor w a1 a2 false⟩).denote w (some (wrapVal w (x * y))) := by
    apply reduceAbsVal_sound hw
    exact ⟨⟨wrapVal w (x * y), rfl, hWrapLt⟩, tnum_top_sound hWrapLt, hWrapLt,
      mulCongFactor_sound hx hy (fun h => nomatch h)⟩
  unfold mulUintAbsFallback
  cases hLo1 : a1.lbound? with
  | none => exact hTopCase
  | some lo1 =>
    dsimp only
    cases hHi1 : a1.ubound? with
    | none => exact hTopCase
    | some hi1 =>
      dsimp only
      cases hLo2 : a2.lbound? with
      | none => exact hTopCase
      | some lo2 =>
        dsimp only
        cases hHi2 : a2.ubound? with
        | none => exact hTopCase
        | some hi2 =>
          dsimp only
          cases hLtB : Nat.blt (hi1 * hi2) (modPow2 w) with
          | false => exact hTopCase
          | true =>
            dsimp only
            have hHiLt : hi1 * hi2 < modPow2 w := lt_of_blt_true hLtB
            have hLoProd : lo1 * lo2 ≤ x * y :=
              Nat.mul_le_mul (absVal_lbound?_sound hLo1 hx)
                (absVal_lbound?_sound hLo2 hy)
            have hHiProd : x * y ≤ hi1 * hi2 :=
              Nat.mul_le_mul (absVal_ubound?_sound hHi1 hx)
                (absVal_ubound?_sound hHi2 hy)
            have hProdLt : x * y < modPow2 w := Nat.lt_of_le_of_lt hHiProd hHiLt
            have hLoLeHi : lo1 * lo2 ≤ hi1 * hi2 := Nat.le_trans hLoProd hHiProd
            have hLoLt : lo1 * lo2 < modPow2 w := Nat.lt_of_le_of_lt hLoLeHi hHiLt
            apply reduceAbsVal_sound hw
            refine ⟨⟨wrapVal w (x * y), rfl, hWrapLt⟩, tnum_top_sound hWrapLt,
              ?_, mulCongFactor_sound hx hy (fun _ => hProdLt)⟩
            rw [wrapVal_of_lt hProdLt]
            exact wrapped_denote_iv_of_le hLoLt hHiLt hLoLeHi hLoProd hHiProd

theorem mulUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) :
    (mulUintAbs w a1 a2).denote w (some (wrapVal w (x * y))) := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  unfold mulUintAbs
  cases hE1 : a1.exactVal? w with
  | some cx =>
    cases hE2 : a2.exactVal? w with
    | some cy =>
      have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
      have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
      exact absVal_const_sound hw
    | none =>
      cases cx with
      | zero =>
        have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
        rw [Nat.zero_mul]; exact absVal_const_sound hw
      | succ cx1 =>
        cases cx1 with
        | zero =>
          have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
          rw [Nat.one_mul, wrapVal_of_lt hyLt]; exact hy
        | succ _ => exact mulUintAbsFallback_sound hw hx hy
  | none =>
    cases hE2 : a2.exactVal? w with
    | none => exact mulUintAbsFallback_sound hw hx hy
    | some cy =>
      cases cy with
      | zero =>
        have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
        rw [Nat.mul_zero]; exact absVal_const_sound hw
      | succ cy1 =>
        cases cy1 with
        | zero =>
          have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
          rw [Nat.mul_one, wrapVal_of_lt hxLt]; exact hx
        | succ _ => exact mulUintAbsFallback_sound hw hx hy

private theorem nat_div_le_div_right_of_le {a b c : Nat} (h : a ≤ b) :
    a / c ≤ b / c :=
  Nat.div_le_div_right h

private theorem nat_div_le_div_left_of_le {a b c : Nat} (hbc : b ≤ c)
    (hb : 0 < b) : a / c ≤ a / b :=
  Nat.div_le_div_left hbc hb

/-- Interval fallback for `divUintAbs`. -/
def divUintAbsFallback (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  let hi1 :=
    match a1.ubound? with
    | some h => h
    | none => modPow2 w - 1
  let hi :=
    match a2.lbound? with
    | some lo2 =>
      match Nat.blt 0 lo2 with
      | true => hi1 / lo2
      | false => hi1
    | none => hi1
  let lo :=
    match a1.lbound? with
    | some lo1 =>
      match a2.ubound? with
      | some hi2 =>
        match Nat.blt 0 hi2 with
        | true => lo1 / hi2
        | false => 0
      | none => 0
    | none => 0
  match Nat.ble lo hi && Nat.blt hi (modPow2 w) with
  | true => reduceAbsVal w ⟨.init, Tnum.top w, .iv lo hi, .top⟩
  | false => topBelow w (some hi1)

/-- Unsigned division transfer: folds exact constants and `0`/`1` identities,
otherwise bounds `[lo1 / hi2, hi1 / lo2]` (defaulting an unconstrained dividend
upper bound to `2^w - 1`). -/
def divUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w with
  | some x =>
    match a2.exactVal? w with
    | some y => AbsVal.const w (x / y)
    | none =>
      match x with
      | 0 => AbsVal.const w 0
      | _ => divUintAbsFallback w a1 a2
  | none =>
    match a2.exactVal? w with
    | some 1 => a1
    | _ => divUintAbsFallback w a1 a2

private theorem divUintAbsFallback_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (divUintAbsFallback w a1 a2).denote w (some (wrapVal w (x / y))) := by
  have hxLt := (absVal_some_elim hx).1
  have hDivLt : x / y < modPow2 w := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxLt
  rw [wrapVal_of_lt hDivLt]
  unfold divUintAbsFallback
  let hi1 := match a1.ubound? with | some h => h | none => modPow2 w - 1
  have hxHi1 : x ≤ hi1 := by
    dsimp only [hi1]
    cases hHi1 : a1.ubound? with
    | none => exact Nat.le_sub_one_of_lt hxLt
    | some h => exact absVal_ubound?_sound hHi1 hx
  let hi := match a2.lbound? with
    | some lo2 => match Nat.blt 0 lo2 with | true => hi1 / lo2 | false => hi1
    | none => hi1
  let lo := match a1.lbound? with
    | some lo1 =>
      match a2.ubound? with
      | some hi2 => match Nat.blt 0 hi2 with | true => lo1 / hi2 | false => 0
      | none => 0
    | none => 0
  have hDivLeHi : x / y ≤ hi := by
    dsimp only [hi]
    cases hLo2 : a2.lbound? with
    | none => exact Nat.le_trans (Nat.div_le_self x y) hxHi1
    | some lo2 =>
      dsimp only
      cases hPos2 : Nat.blt 0 lo2 with
      | false => exact Nat.le_trans (Nat.div_le_self x y) hxHi1
      | true =>
        exact Nat.le_trans
          (nat_div_le_div_left_of_le (absVal_lbound?_sound hLo2 hy)
            (lt_of_blt_true hPos2))
          (nat_div_le_div_right_of_le hxHi1)
  have hLoLeDiv : lo ≤ x / y := by
    dsimp only [lo]
    cases hLo1 : a1.lbound? with
    | none => exact Nat.zero_le _
    | some lo1 =>
      dsimp only
      cases hHi2 : a2.ubound? with
      | none => exact Nat.zero_le _
      | some hi2 =>
        dsimp only
        cases hPos2 : Nat.blt 0 hi2 with
        | false => exact Nat.zero_le _
        | true =>
          exact Nat.le_trans
            (nat_div_le_div_left_of_le (absVal_ubound?_sound hHi2 hy) hyPos)
            (nat_div_le_div_right_of_le (absVal_lbound?_sound hLo1 hx))
  dsimp only
  cases hOk : (Nat.ble lo hi && Nat.blt hi (modPow2 w)) with
  | false =>
    exact topBelow_sound hw hDivLt (fun hi' hE => by
      cases hE; exact Nat.le_trans (Nat.div_le_self x y) hxHi1)
  | true =>
    have hLoHi := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
    have hHiLt := lt_of_blt_true (bool_and_true_right hOk)
    have hLoLt := Nat.lt_of_le_of_lt hLoHi hHiLt
    apply reduceAbsVal_sound hw
    exact ⟨⟨x / y, rfl, hDivLt⟩, tnum_top_sound hDivLt,
      wrapped_denote_iv_of_le hLoLt hHiLt hLoHi hLoLeDiv hDivLeHi, True.intro⟩

theorem divUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (divUintAbs w a1 a2).denote w (some (wrapVal w (x / y))) := by
  have hxLt := (absVal_some_elim hx).1
  unfold divUintAbs
  cases hE1 : a1.exactVal? w with
  | some cx =>
    cases hE2 : a2.exactVal? w with
    | some cy =>
      have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
      have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
      exact absVal_const_sound hw
    | none =>
      cases cx with
      | zero =>
        have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
        rw [Nat.zero_div]; exact absVal_const_sound hw
      | succ _ => exact divUintAbsFallback_sound hw hx hy hyPos
  | none =>
    cases hE2 : a2.exactVal? w with
    | none => exact divUintAbsFallback_sound hw hx hy hyPos
    | some cy =>
      cases cy with
      | zero => exact divUintAbsFallback_sound hw hx hy hyPos
      | succ cy1 =>
        cases cy1 with
        | zero =>
          have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
          rw [Nat.div_one, wrapVal_of_lt hxLt]; exact hx
        | succ _ => exact divUintAbsFallback_sound hw hx hy hyPos

/-- Interval fallback for `remUintAbs`. -/
def remUintAbsFallback (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.ubound? with
  | some hi1 =>
    match a2.lbound? with
    | some lo2 =>
      match Nat.blt hi1 lo2 with
      | true => a1
      | false =>
        match a2.ubound? with
        | some hi2 => topBelow w (some (Nat.min hi1 (hi2 - 1)))
        | none => topBelow w (some hi1)
    | none =>
      match a2.ubound? with
      | some hi2 => topBelow w (some (Nat.min hi1 (hi2 - 1)))
      | none => topBelow w (some hi1)
  | none =>
    match a2.ubound? with
    | some hi2 => topBelow w (some (hi2 - 1))
    | none => AbsVal.topInit w

/-- Unsigned remainder transfer: folds exact constants and `0`/`1` identities,
returns `a1` unchanged when `hi1 < lo2` (`x % y = x`), else bounds by
`min hi1 (hi2 - 1)`. -/
def remUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w with
  | some x =>
    match a2.exactVal? w with
    | some y => AbsVal.const w (x % y)
    | none =>
      match x with
      | 0 => AbsVal.const w 0
      | _ => remUintAbsFallback w a1 a2
  | none =>
    match a2.exactVal? w with
    | some 1 => AbsVal.const w 0
    | _ => remUintAbsFallback w a1 a2

private theorem remUintAbsFallback_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (remUintAbsFallback w a1 a2).denote w (some (wrapVal w (x % y))) := by
  have hyLt := (absVal_some_elim hy).1
  have hRemLt : x % y < modPow2 w := Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
    (Nat.le_of_lt hyLt)
  have hModLeX : x % y ≤ x := Nat.mod_le x y
  have hBoundHi1 : ∀ hi1, a1.ubound? = some hi1 →
      (match a2.ubound? with
       | some hi2 => topBelow w (some (Nat.min hi1 (hi2 - 1)))
       | none => topBelow w (some hi1)).denote w (some (x % y)) := by
    intro hi1 hU1
    have hLe1 : x % y ≤ hi1 := Nat.le_trans hModLeX (absVal_ubound?_sound hU1 hx)
    cases hU2 : a2.ubound? with
    | none =>
      exact topBelow_sound hw hRemLt (fun _ hE => by cases hE; exact hLe1)
    | some hi2 =>
      have hLe2 : x % y ≤ hi2 - 1 :=
        Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
          (absVal_ubound?_sound hU2 hy))
      exact topBelow_sound hw hRemLt (fun _ hE => by cases hE; exact nat_le_min hLe1 hLe2)
  rw [wrapVal_of_lt hRemLt]
  unfold remUintAbsFallback
  cases hU1 : a1.ubound? with
  | none =>
    cases hU2 : a2.ubound? with
    | none => exact absVal_topInit_sound hRemLt
    | some hi2 =>
      exact topBelow_sound hw hRemLt (fun _ hE => by
        cases hE
        exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
          (absVal_ubound?_sound hU2 hy)))
  | some hi1 =>
    dsimp only
    cases hL2 : a2.lbound? with
    | none => exact hBoundHi1 hi1 hU1
    | some lo2 =>
      dsimp only
      cases hLtB : Nat.blt hi1 lo2 with
      | false => exact hBoundHi1 hi1 hU1
      | true =>
        dsimp only
        have hXLtY : x < y :=
          Nat.lt_of_le_of_lt (absVal_ubound?_sound hU1 hx)
            (Nat.lt_of_lt_of_le (lt_of_blt_true hLtB)
              (absVal_lbound?_sound hL2 hy))
        rw [Nat.mod_eq_of_lt hXLtY]
        exact hx

theorem remUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (remUintAbs w a1 a2).denote w (some (wrapVal w (x % y))) := by
  unfold remUintAbs
  cases hE1 : a1.exactVal? w with
  | some cx =>
    cases hE2 : a2.exactVal? w with
    | some cy =>
      have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
      have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
      exact absVal_const_sound hw
    | none =>
      cases cx with
      | zero =>
        have h1 := (absVal_exactVal?_sound hE1 hx).1; cases h1
        rw [Nat.zero_mod]; exact absVal_const_sound hw
      | succ _ => exact remUintAbsFallback_sound hw hx hy hyPos
  | none =>
    cases hE2 : a2.exactVal? w with
    | none => exact remUintAbsFallback_sound hw hx hy hyPos
    | some cy =>
      cases cy with
      | zero => exact remUintAbsFallback_sound hw hx hy hyPos
      | succ cy1 =>
        cases cy1 with
        | zero =>
          have h2 := (absVal_exactVal?_sound hE2 hy).1; cases h2
          rw [Nat.mod_one]; exact absVal_const_sound hw
        | succ _ => exact remUintAbsFallback_sound hw hx hy hyPos

/-- Unsigned shift-left transfer (exact shift amount `k`, else `topInit`). -/
def shlUintAbs (w : Nat) (a : AbsVal) (k? : Option Nat) : AbsVal :=
  match k? with
  | some k => AbsVal.shlConst w k a
  | none => AbsVal.topInit w

/-- Unsigned logical shift-right transfer (exact amount, else `topInit`). -/
def shrUintAbs (w : Nat) (a : AbsVal) (k? : Option Nat) : AbsVal :=
  match k? with
  | some k => AbsVal.shrConst w k a
  | none => AbsVal.topInit w

/-- Unsigned integer-to-integer cast transfer:
- same-width casts preserve `a` unchanged;
- widening casts tighten `a` by `x ≤ 2^wSrc - 1` so `WrappedInterval.top` at
  `wSrc` becomes `[0, 2^wSrc - 1]` at `wDst`;
- narrowing casts fold constants, narrow losslessly when `hi < 2^wDst`, and
  otherwise preserve the low `wDst` `Tnum` bits via `Tnum.capPow2`. -/
def castUintAbs (uSrc uDst : UintTy) (a : AbsVal) : AbsVal :=
  let wSrc := uintWidth uSrc
  let wDst := uintWidth uDst
  match Nat.beq wSrc wDst with
  | true => a
  | false =>
    match Nat.blt wSrc wDst with
    | true => AbsVal.refineUleConst wDst a (modPow2 wSrc - 1)
    | false =>
      match a.exactVal? wSrc with
      | some x => AbsVal.const wDst x
      | none =>
        match a.ubound? with
        | some hi =>
          match Nat.blt hi (modPow2 wDst) with
          | true =>
            reduceAbsVal wDst ⟨.init, Tnum.capPow2 wDst a.tnum, a.wi, a.sc⟩
          | false =>
            reduceAbsVal wDst ⟨.init, Tnum.capPow2 wDst a.tnum, .top, .top⟩
        | none =>
          reduceAbsVal wDst ⟨.init, Tnum.capPow2 wDst a.tnum, .top, .top⟩

theorem castUintAbs_sound {uSrc uDst : UintTy} {a : AbsVal} {x : Nat}
    (hai : a.isInit = true) (hx : a.denote (uintWidth uSrc) (some x)) :
    (castUintAbs uSrc uDst a).denote (uintWidth uDst)
      (some (wrapVal (uintWidth uDst) x)) := by
  have hxE := absVal_some_elim hx
  have hxLt := hxE.1
  have hWrapLt : wrapVal (uintWidth uDst) x < modPow2 (uintWidth uDst) :=
    nat_mod_lt _ (modPow2_pos _)
  have hNarrowCap :
      (reduceAbsVal (uintWidth uDst)
        ⟨.init, Tnum.capPow2 (uintWidth uDst) a.tnum, .top, .top⟩).denote
        (uintWidth uDst) (some (wrapVal (uintWidth uDst) x)) := by
    apply reduceAbsVal_sound (uintWidth_valid uDst)
    exact ⟨⟨wrapVal (uintWidth uDst) x, rfl, hWrapLt⟩,
      tnum_capPow2_wrap_sound hxE.2.1, hWrapLt, True.intro⟩
  unfold castUintAbs
  dsimp only
  cases hEq : Nat.beq (uintWidth uSrc) (uintWidth uDst) with
  | true =>
    have hwEq := Nat.eq_of_beq_eq_true hEq
    simp only
    rw [← hwEq, wrapVal_of_lt hxLt]
    exact hx
  | false =>
    simp only
    cases hLt : Nat.blt (uintWidth uSrc) (uintWidth uDst) with
    | true =>
      simp only
      have hMono := modPow2_mono (Nat.le_of_lt (lt_of_blt_true hLt))
      rw [wrapVal_of_lt (Nat.lt_of_lt_of_le hxLt hMono)]
      exact absVal_refineUleConst_sound (uintWidth_valid uDst)
        (absVal_denote_widen hMono hx) hai (Nat.le_sub_one_of_lt hxLt)
    | false =>
      simp only
      cases hEx : a.exactVal? (uintWidth uSrc) with
      | some cx =>
        simp only
        have h1 := (absVal_exactVal?_sound hEx hx).1
        injection h1 with h1
        subst h1
        exact absVal_const_sound (uintWidth_valid uDst)
      | none =>
        simp only
        cases hHi : a.ubound? with
        | none => exact hNarrowCap
        | some hi =>
          simp only
          cases hHiLt : Nat.blt hi (modPow2 (uintWidth uDst)) with
          | false => exact hNarrowCap
          | true =>
            simp only
            have hXLeHi : x ≤ hi := absVal_ubound?_sound hHi hx
            have hHiDst : hi < modPow2 (uintWidth uDst) := lt_of_blt_true hHiLt
            have hXDst : x < modPow2 (uintWidth uDst) :=
              Nat.lt_of_le_of_lt hXLeHi hHiDst
            rw [wrapVal_of_lt hXDst]
            apply reduceAbsVal_sound (uintWidth_valid uDst)
            refine ⟨⟨x, rfl, hXDst⟩, tnum_capPow2_sound hxE.2.1 hXDst, ?_,
              hxE.2.2.2⟩
            unfold AbsVal.ubound? at hHi
            cases hI0 : a.init with
            | bot => rw [hI0] at hHi; nomatch hHi
            | uninit => rw [hI0] at hHi; nomatch hHi
            | init =>
              cases hWi : a.wi with
              | bot => rw [hI0, hWi] at hHi; nomatch hHi
              | top => rw [hI0, hWi] at hHi; nomatch hHi
              | iv lo hi' =>
                rw [hI0, hWi] at hHi
                simp only at hHi
                cases hBle : Nat.ble lo hi' with
                | false => rw [hBle] at hHi; nomatch hHi
                | true =>
                  rw [hBle] at hHi
                  injection hHi with hHiEq
                  subst hHiEq
                  have hW := hxE.2.2.1
                  rw [hWi] at hW
                  simp only [WrappedInterval.denote, hBle] at hW
                  have hLoLeHi := Nat.le_of_ble_eq_true hBle
                  exact wrapped_denote_iv_of_le
                    (Nat.lt_of_le_of_lt hLoLeHi hHiDst) hHiDst hLoLeHi
                    hW.2.2.2.1 hW.2.2.2.2

/-- `bool as uN` cast transfer (`false ↦ 0`, `true ↦ 1`). -/
def boolToUintAbs (uDst : UintTy) (ba : BoolAbs) : AbsVal :=
  match ba with
  | .exact c _ => AbsVal.const (uintWidth uDst) (boolToScalar c).bits
  | _ => topBelow (uintWidth uDst) (some 1)

theorem one_lt_modPow2_uint (u : UintTy) : 1 < modPow2 (uintWidth u) := by
  cases u <;> exact lt_of_blt_true rfl

theorem boolToScalar_sizeBytes (c : Bool) : (boolToScalar c).sizeBytes = 1 := by
  cases c <;> rfl

theorem boolToScalar_bits_le_one (c : Bool) : (boolToScalar c).bits ≤ 1 := by
  cases c
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1

theorem boolToUintAbs_sound {uDst : UintTy} {ba : BoolAbs} {c : Bool}
    {locals : List LocalSlot} (h : ba.denoteBool locals c) :
    (boolToUintAbs uDst ba).denote (uintWidth uDst)
      (some (boolToScalar c).bits) := by
  have hLt : (boolToScalar c).bits < modPow2 (uintWidth uDst) :=
    Nat.lt_of_le_of_lt (boolToScalar_bits_le_one c) (one_lt_modPow2_uint uDst)
  unfold boolToUintAbs
  cases ba with
  | exact c' g =>
    have hc : c = c' := h.1
    subst hc
    exact absVal_const_denote_lt (uintWidth_valid uDst) hLt
  | bot => exact False.elim h
  | uninit =>
    exact topBelow_sound (uintWidth_valid uDst) hLt
      (fun hi hE => by injection hE with hE; subst hE; exact boolToScalar_bits_le_one c)
  | top g =>
    exact topBelow_sound (uintWidth_valid uDst) hLt
      (fun hi hE => by injection hE with hE; subst hE; exact boolToScalar_bits_le_one c)

/-! ## 5. Comparisons and Relational Guard Synthesis -/

def binOpToCmp? : BinOp → Option CmpOp
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | _ => none

def cmpOpFlip : CmpOp → CmpOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le

def cmpOpEval (cop : CmpOp) (x y : Nat) : Bool :=
  match cop with
  | .eq => Nat.beq x y
  | .ne => !(Nat.beq x y)
  | .lt => Nat.blt x y
  | .le => Nat.ble x y
  | .gt => Nat.blt y x
  | .ge => Nat.ble y x

/-- Unsigned comparison outcome computed by `evalScalarBinOp`. -/
def cmpResult (op : BinOp) (x y : Nat) : Bool :=
  match binOpToCmp? op with
  | some cop => cmpOpEval cop x y
  | none => false

/-- Flip the operand direction of a comparison operator. -/
def flipCmpOp : BinOp → BinOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le
  | op => op

private theorem binOpToCmp?_flipCmpOp : ∀ (op : BinOp),
    binOpToCmp? (flipCmpOp op) = (binOpToCmp? op).map cmpOpFlip
  | .eq | .ne | .lt | .le | .gt | .ge => rfl
  | .add | .addUnchecked | .addWithOverflow
  | .sub | .subUnchecked | .subWithOverflow
  | .mul | .mulUnchecked | .mulWithOverflow
  | .div | .rem | .bitXor | .bitAnd | .bitOr
  | .shl | .shlUnchecked | .shr | .shrUnchecked
  | .cmp | .offset => rfl

private theorem nat_beq_comm (x y : Nat) : Nat.beq y x = Nat.beq x y := by
  cases h : Nat.beq y x with
  | true => rw [Nat.eq_of_beq_eq_true h, Nat.beq_refl]
  | false =>
    cases h2 : Nat.beq x y with
    | false => rfl
    | true => rw [Nat.eq_of_beq_eq_true h2, Nat.beq_refl] at h; nomatch h

theorem cmpResult_flip (op : BinOp) (x y : Nat) :
    cmpResult (flipCmpOp op) y x = cmpResult op x y := by
  unfold cmpResult
  rw [binOpToCmp?_flipCmpOp]
  cases binOpToCmp? op with
  | none => rfl
  | some cop =>
    cases cop with
    | eq => exact nat_beq_comm x y
    | ne => exact congrArg Bool.not (nat_beq_comm x y)
    | lt | le | gt | ge => rfl

theorem nat_beq_true_iff {x y : Nat} : Nat.beq x y = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h, Nat.beq_refl]⟩

theorem nat_not_beq_true_iff {x y : Nat} : (!(Nat.beq x y)) = true ↔ x ≠ y := by
  constructor
  · intro h hEq
    rw [hEq, Nat.beq_refl] at h
    cases h
  · intro hNe
    cases hB : Nat.beq x y with
    | true => exact absurd (Nat.eq_of_beq_eq_true hB) hNe
    | false => rfl

theorem nat_ble_true_iff {x y : Nat} : Nat.ble x y = true ↔ x ≤ y :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem nat_blt_true_iff {x y : Nat} : Nat.blt x y = true ↔ x < y :=
  ⟨lt_of_blt_true, blt_true_of_lt⟩

/-- Static decision of the unsigned comparison `op` between `a1` and `a2`. -/
def decideCmpAbs (op : BinOp) (w : Nat) (a1 a2 : AbsVal) : Option Bool :=
  match binOpToCmp? op with
  | some .eq => AbsVal.decideEq? w a1 a2
  | some .ne =>
    match AbsVal.decideEq? w a1 a2 with
    | some r => some (!r)
    | none => none
  | some .lt => AbsVal.decideLt? w a1 a2
  | some .le => AbsVal.decideLe? w a1 a2
  | some .gt => AbsVal.decideLt? w a2 a1
  | some .ge => AbsVal.decideLe? w a2 a1
  | none => none

theorem decideCmpAbs_sound {op : BinOp} {w x y : Nat} {a1 a2 : AbsVal}
    {r : Bool} (h : decideCmpAbs op w a1 a2 = some r)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    cmpResult op x y = r := by
  unfold decideCmpAbs at h
  unfold cmpResult
  cases hC : binOpToCmp? op with
  | none => rw [hC] at h; nomatch h
  | some cop =>
    rw [hC] at h
    cases cop with
    | eq => exact absVal_decideEq?_sound h hx hy
    | lt => exact absVal_decideLt?_sound h hx hy
    | le => exact absVal_decideLe?_sound h hx hy
    | gt => exact absVal_decideLt?_sound h hy hx
    | ge => exact absVal_decideLe?_sound h hy hx
    | ne =>
      dsimp only at h
      cases hD : AbsVal.decideEq? w a1 a2 with
      | none => rw [hD] at h; nomatch h
      | some r' =>
        rw [hD] at h
        injection h with h
        subst h
        exact congrArg Bool.not (absVal_decideEq?_sound hD hx hy)

/-- Guard for `op(copy r, const v)`. -/
def cmpGuardConstR (op : BinOp) (r : Nat) (u : UintTy) (v : Nat) : RelGuard :=
  match binOpToCmp? op with
  | some .eq => .ueqConst r u v
  | some .ne => .uneConst r u v
  | some .lt =>
    match v with
    | 0 => .none
    | k + 1 => .uleConst r u k
  | some .le => .uleConst r u v
  | some .gt => .ugtConst r u v
  | some .ge =>
    match v with
    | 0 => .none
    | k + 1 => .ugtConst r u k
  | none => .none

/-- Guard for `op(copy l, copy r)` across all six comparison operators. -/
def cmpGuardRegs (op : BinOp) (l r : Nat) (u : UintTy) : RelGuard :=
  match binOpToCmp? op with
  | some .eq => .ueqReg l r u
  | some .ne => .uneReg l r u
  | some .lt => .ultReg l r u
  | some .le => .ugeReg r l u
  | some .gt => .ultReg r l u
  | some .ge => .ugeReg l r u
  | none => .none

/-- Guard for `op(const v, copy r)` across all six comparison operators. -/
def cmpGuardConstL (op : BinOp) (v : Nat) (r : Nat) (u : UintTy) : RelGuard :=
  cmpGuardConstR (flipCmpOp op) r u v

theorem cmpGuardConstR_sound {op : BinOp} {locals : List LocalSlot} {r : Nat}
    {u : UintTy} {x y : Nat} (hx : localUintNat? locals r u = some x) :
    (cmpGuardConstR op r u y).denote locals (cmpResult op x y) := by
  unfold cmpGuardConstR cmpResult
  cases binOpToCmp? op with
  | none => exact True.intro
  | some cop =>
    cases cop with
    | eq =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_beq_true_iff
    | ne =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_not_beq_true_iff
    | le =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_ble_true_iff
    | gt =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_blt_true_iff
    | lt =>
      cases y with
      | zero => exact True.intro
      | succ k =>
        intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
        exact Iff.trans nat_blt_true_iff Nat.lt_succ_iff
    | ge =>
      cases y with
      | zero => exact True.intro
      | succ k =>
        intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
        exact nat_ble_true_iff

theorem cmpGuardRegs_sound {op : BinOp} {locals : List LocalSlot} {l r : Nat}
    {u : UintTy} {x y : Nat} (hx : localUintNat? locals l u = some x)
    (hy : localUintNat? locals r u = some y) :
    (cmpGuardRegs op l r u).denote locals (cmpResult op x y) := by
  unfold cmpGuardRegs cmpResult
  cases binOpToCmp? op with
  | none => exact True.intro
  | some cop =>
    cases cop with
    | eq =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_beq_true_iff
    | ne =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_not_beq_true_iff
    | lt =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_blt_true_iff
    | le =>
      intro y' x' hy' hx'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_ble_true_iff
    | gt =>
      intro y' x' hy' hx'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_blt_true_iff
    | ge =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact nat_ble_true_iff

theorem cmpGuardConstL_sound {op : BinOp} {locals : List LocalSlot} {r : Nat}
    {u : UintTy} {x y : Nat} (hy : localUintNat? locals r u = some y) :
    (cmpGuardConstL op x r u).denote locals (cmpResult op x y) := by
  unfold cmpGuardConstL
  rw [← cmpResult_flip op x y]
  exact cmpGuardConstR_sound hy

/-- Synthesize a `RelGuard` for an unsigned comparison from the operands'
source locals and exactly-known values. Constant-on-left guards are tried
before register-register guards so equalities and inequalities against a
known-constant local retain constant precision. -/
def synthCmpGuard (op : BinOp) (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match srcL, a2.exactVal? (uintWidth u) with
  | some r, some v => cmpGuardConstR op r u v
  | _, _ =>
    match srcR, a1.exactVal? (uintWidth u) with
    | some r, some v => cmpGuardConstL op v r u
    | _, _ =>
      match srcL, srcR with
      | some l, some r => cmpGuardRegs op l r u
      | _, _ => .none

theorem synthCmpGuard_sound {op : BinOp} {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (synthCmpGuard op u srcL srcR a1 a2).denote locals (cmpResult op x y) := by
  have hConstL : ∀ (r v : Nat), srcR = some r →
      a1.exactVal? (uintWidth u) = some v →
      (cmpGuardConstL op v r u).denote locals (cmpResult op x y) := by
    intro r v hr hE1
    have h1 := (absVal_exactVal?_sound hE1 hx).1
    injection h1 with h1
    subst h1
    exact cmpGuardConstL_sound (hR r hr)
  unfold synthCmpGuard
  cases srcL with
  | some l =>
    cases hE2 : a2.exactVal? (uintWidth u) with
    | some v =>
      have h2 := (absVal_exactVal?_sound hE2 hy).1
      injection h2 with h2
      subst h2
      exact cmpGuardConstR_sound (hL l rfl)
    | none =>
      cases srcR with
      | none => exact True.intro
      | some r =>
        cases hE1 : a1.exactVal? (uintWidth u) with
        | some v => exact hConstL r v rfl hE1
        | none => exact cmpGuardRegs_sound (hL l rfl) (hR r rfl)
  | none =>
    cases srcR with
    | none =>
      cases a2.exactVal? (uintWidth u) <;> exact True.intro
    | some r =>
      cases hE1 : a1.exactVal? (uintWidth u) with
      | none =>
        cases a2.exactVal? (uintWidth u) <;> exact True.intro
      | some v =>
        cases a2.exactVal? (uintWidth u) <;> exact hConstL r v rfl hE1

/-- Build a `BoolAbs` from an optional statically known outcome and guard. -/
def mkBoolAbs (known? : Option Bool) (g : RelGuard) : BoolAbs :=
  match known? with
  | some v => .exact v g
  | none => .top g

theorem mkBoolAbs_sound {known? : Option Bool} {g : RelGuard}
    {locals : List LocalSlot} {b : Bool}
    (hK : ∀ r, known? = some r → b = r) (hG : g.denote locals b) :
    (mkBoolAbs known? g).denoteBool locals b := by
  cases known? with
  | none => exact hG
  | some r => exact ⟨hK r rfl, hG⟩

theorem mkBoolAbs_isInit (known? : Option Bool) (g : RelGuard) :
    (mkBoolAbs known? g).isInit = true := by
  cases known? <;> rfl

/-! ## 6. Unsigned and Boolean Binary Operations -/

/-- Replace a possibly-uninitialized `AbsVal` by `topInit` (results of
arithmetic on initialized operands are always initialized). -/
def AbsVal.ensureInit (w : Nat) (a : AbsVal) : AbsVal :=
  match a.isInit with
  | true => a
  | false => AbsVal.topInit w

theorem absVal_ensureInit_isInit (w : Nat) (a : AbsVal) :
    (AbsVal.ensureInit w a).isInit = true := by
  unfold AbsVal.ensureInit
  cases h : a.isInit with
  | true => exact h
  | false => rfl

theorem absVal_ensureInit_sound {w x : Nat} {a : AbsVal}
    (h : a.denote w (some x)) : (AbsVal.ensureInit w a).denote w (some x) := by
  unfold AbsVal.ensureInit
  cases a.isInit with
  | true => exact h
  | false => exact absVal_topInit_sound (absVal_some_elim h).1

/-- Unsigned result value (initialized, with no source local). -/
def mkUintVal (u : UintTy) (a : AbsVal) : MirAbsVal :=
  .uint u (AbsVal.ensureInit (uintWidth u) a) none

theorem mkUintVal_denote {locals : List LocalSlot} {u : UintTy} {a : AbsVal}
    {bits : Nat} (h : a.denote (uintWidth u) (some bits)) :
    (mkUintVal u a).denote locals (.scalar ⟨bits, uintBytes u⟩) :=
  ⟨absVal_ensureInit_isInit _ a, rfl, absVal_ensureInit_sound h, True.intro⟩

/-- Checked `(u, bool)` arithmetic result value. -/
def mkUintBoolPairVal (u : UintTy) (a : AbsVal) (ov : BoolAbs) : MirAbsVal :=
  .uintBoolPair u (AbsVal.ensureInit (uintWidth u) a) ov

theorem mkUintBoolPairVal_denote {locals : List LocalSlot} {u : UintTy}
    {a : AbsVal} {ov : BoolAbs} {bits : Nat} {b : Bool}
    (hA : a.denote (uintWidth u) (some bits)) (hOvI : ov.isInit = true)
    (hOv : ov.denoteBool locals b) :
    (mkUintBoolPairVal u a ov).denote locals
      (.aggregate 0 [.scalar ⟨bits, uintBytes u⟩, .scalar (boolToScalar b)]) :=
  ⟨absVal_ensureInit_isInit _ a, hOvI, rfl, absVal_ensureInit_sound hA,
    boolAbs_denote_of_bool hOv⟩

private theorem add_overflow_ugt_iff {w x v : Nat} (hvLt : v < modPow2 w) :
    Nat.ble (modPow2 w) (x + v) = true ↔ modPow2 w - v - 1 < x := by
  have hSubPos : 1 ≤ modPow2 w - v := Nat.sub_pos_of_lt hvLt
  have hK1 : modPow2 w - v - 1 + 1 = modPow2 w - v := Nat.sub_add_cancel hSubPos
  have hMv : modPow2 w - v + v = modPow2 w := Nat.sub_add_cancel (Nat.le_of_lt hvLt)
  constructor
  · intro hBle
    have hLe : modPow2 w ≤ x + v := Nat.le_of_ble_eq_true hBle
    rw [← hMv] at hLe
    have hLeX : modPow2 w - v ≤ x := Nat.le_of_add_le_add_right hLe
    rw [← hK1] at hLeX
    exact hLeX
  · intro hLt
    have hLe : modPow2 w - v ≤ x := by
      have h1 : modPow2 w - v - 1 + 1 ≤ x := hLt
      rw [hK1] at h1
      exact h1
    apply Nat.ble_eq_true_of_le
    rw [← hMv]
    exact Nat.add_le_add_right hLe v

/-- True iff `a` is statically known to equal `0` at width `w`. -/
def isZeroExact (w : Nat) (a : AbsVal) : Bool :=
  match a.exactVal? w with
  | some 0 => true
  | _ => false

private theorem isZeroExact_eq {w x : Nat} {a : AbsVal}
    (h : isZeroExact w a = true) (ha : a.denote w (some x)) : x = 0 := by
  unfold isZeroExact at h
  cases hE : a.exactVal? w with
  | none => rw [hE] at h; nomatch h
  | some c =>
    rw [hE] at h
    cases c with
    | succ _ => nomatch h
    | zero =>
      have hEq := (absVal_exactVal?_sound hE ha).1
      injection hEq

private def addOverflowKnown? (w : Nat) (a1 a2 : AbsVal) : Option Bool :=
  match isZeroExact w a1 || isZeroExact w a2 with
  | true => some false
  | false =>
    match AbsVal.noOverflowAdd w a1 a2 with
    | true => some false
    | false =>
      match a1.lbound? with
      | none => none
      | some lo1 =>
        match a2.lbound? with
        | none => none
        | some lo2 =>
          match Nat.ble (modPow2 w) (lo1 + lo2) with
          | true => some true
          | false => none

private def addOverflowGuardOne (u : UintTy) (src : Option Nat) (aOther : AbsVal) :
    RelGuard :=
  match src with
  | none => .none
  | some r =>
    match aOther.exactVal? (uintWidth u) with
    | none => .none
    | some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u (modPow2 (uintWidth u) - v - 1)
      | false => .none

private def addOverflowGuard (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match srcL with
  | some r =>
    match a2.exactVal? (uintWidth u) with
    | some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u (modPow2 (uintWidth u) - v - 1)
      | false => .none
    | none => addOverflowGuardOne u srcR a1
  | none => addOverflowGuardOne u srcR a1

/-- Overflow boolean and optional guard for `addWithOverflow`. -/
def addOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  mkBoolAbs (addOverflowKnown? (uintWidth u) a1 a2)
    (addOverflowGuard u srcL srcR a1 a2)

theorem addOverflowBoolAbs_isInit (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (addOverflowBoolAbs u srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

private theorem addOverflowKnown?_sound {w x y : Nat} {a1 a2 : AbsVal} {r : Bool}
    (hr : addOverflowKnown? w a1 a2 = some r)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    Nat.ble (modPow2 w) (x + y) = r := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  unfold addOverflowKnown? at hr
  cases hZ1 : isZeroExact w a1 with
  | true =>
    rw [hZ1, Bool.true_or] at hr; cases hr
    rw [isZeroExact_eq hZ1 hx, Nat.zero_add]
    cases hB : Nat.ble (modPow2 w) y with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hyLt (Nat.le_of_ble_eq_true hB))
  | false =>
    rw [hZ1, Bool.false_or] at hr
    cases hZ2 : isZeroExact w a2 with
    | true =>
      rw [hZ2] at hr; cases hr
      rw [isZeroExact_eq hZ2 hy, Nat.add_zero]
      cases hB : Nat.ble (modPow2 w) x with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hxLt (Nat.le_of_ble_eq_true hB))
    | false =>
      rw [hZ2] at hr; dsimp only at hr
      cases hNo : AbsVal.noOverflowAdd w a1 a2 with
      | true =>
        rw [hNo] at hr; cases hr
        cases absVal_noOverflowAdd_sound hNo hx hy with
        | intro x' hxy =>
          cases hxy with
          | intro y' hxy =>
            injection hxy.1 with h1; injection hxy.2.1 with h2; subst h1; subst h2
            cases hB : Nat.ble (modPow2 w) (x + y) with
            | false => rfl
            | true =>
              exact False.elim (Nat.not_le_of_gt hxy.2.2.1 (Nat.le_of_ble_eq_true hB))
      | false =>
        rw [hNo] at hr; dsimp only at hr
        cases hL1 : a1.lbound? with
        | none => rw [hL1] at hr; nomatch hr
        | some lo1 =>
          rw [hL1] at hr; dsimp only at hr
          cases hL2 : a2.lbound? with
          | none => rw [hL2] at hr; nomatch hr
          | some lo2 =>
            rw [hL2] at hr; dsimp only at hr
            cases hOv : Nat.ble (modPow2 w) (lo1 + lo2) with
            | false => rw [hOv] at hr; nomatch hr
            | true =>
              rw [hOv] at hr; cases hr
              exact Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOv)
                (Nat.add_le_add (absVal_lbound?_sound hL1 hx)
                  (absVal_lbound?_sound hL2 hy)))

private theorem addOverflowGuardOne_sound {u : UintTy} {src : Option Nat}
    {aOther : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hy : aOther.denote (uintWidth u) (some y))
    (hS : ∀ r, src = some r → localUintNat? locals r u = some x) :
    (addOverflowGuardOne u src aOther).denote locals
      (Nat.ble (modPow2 (uintWidth u)) (x + y)) := by
  unfold addOverflowGuardOne
  cases src with
  | none => exact True.intro
  | some r =>
    cases hE : aOther.exactVal? (uintWidth u) with
    | none => exact True.intro
    | some v =>
      dsimp only
      cases hPos : Nat.blt 0 v with
      | false => exact True.intro
      | true =>
        have h2 := (absVal_exactVal?_sound hE hy).1
        injection h2 with h2; subst h2
        intro x' hx'
        rw [hS r rfl] at hx'; injection hx' with hx'; subst hx'
        exact add_overflow_ugt_iff (absVal_some_elim hy).1

theorem addOverflowBoolAbs_sound {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (addOverflowBoolAbs u srcL srcR a1 a2).denoteBool locals
      (Nat.ble (modPow2 (uintWidth u)) (x + y)) := by
  apply mkBoolAbs_sound (fun _ hr => addOverflowKnown?_sound hr hx hy)
  have hRight : (addOverflowGuardOne u srcR a1).denote locals
      (Nat.ble (modPow2 (uintWidth u)) (x + y)) := by
    rw [Nat.add_comm x y]
    exact addOverflowGuardOne_sound hx hR
  unfold addOverflowGuard
  cases srcL with
  | none => exact hRight
  | some r =>
    cases hE2 : a2.exactVal? (uintWidth u) with
    | none => exact hRight
    | some v =>
      dsimp only
      cases hPos : Nat.blt 0 v with
      | false => exact True.intro
      | true =>
        have h2 := (absVal_exactVal?_sound hE2 hy).1
        injection h2 with h2; subst h2
        intro x' hx'
        rw [hL r rfl] at hx'; injection hx' with hx'; subst hx'
        exact add_overflow_ugt_iff (absVal_some_elim hy).1

/-- Overflow-freedom check for unsigned addition, handling `0 + y` and `x + 0`
even when the other operand is unconstrained (`topInit`). -/
def noOverflowAddSafe (w : Nat) (a1 a2 : AbsVal) : Bool :=
  AbsVal.noOverflowAdd w a1 a2 || isZeroExact w a1 || isZeroExact w a2

theorem noOverflowAddSafe_sound {w x y : Nat} {a1 a2 : AbsVal}
    (h : noOverflowAddSafe w a1 a2 = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) : x + y < modPow2 w := by
  unfold noOverflowAddSafe at h
  cases hA : AbsVal.noOverflowAdd w a1 a2 with
  | true =>
    cases absVal_noOverflowAdd_sound hA hx hy with
    | intro x' hxy =>
      cases hxy with
      | intro y' hxy =>
        injection hxy.1 with h1
        injection hxy.2.1 with h2
        subst h1
        subst h2
        exact hxy.2.2.1
  | false =>
    rw [hA, Bool.false_or] at h
    cases hZ1 : isZeroExact w a1 with
    | true =>
      rw [isZeroExact_eq hZ1 hx, Nat.zero_add]
      exact (absVal_some_elim hy).1
    | false =>
      rw [hZ1, Bool.false_or] at h
      rw [isZeroExact_eq h hy, Nat.add_zero]
      exact (absVal_some_elim hx).1

/-- Underflow-freedom check for unsigned subtraction, handling `x - 0` even
when `x` is unconstrained (`topInit`). -/
def noUnderflowSubSafe (w : Nat) (a1 a2 : AbsVal) : Bool :=
  AbsVal.noUnderflowSub w a1 a2 || isZeroExact w a2

theorem noUnderflowSubSafe_sound {w x y : Nat} {a1 a2 : AbsVal}
    (h : noUnderflowSubSafe w a1 a2 = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) : y ≤ x := by
  unfold noUnderflowSubSafe at h
  cases hS : AbsVal.noUnderflowSub w a1 a2 with
  | true =>
    cases absVal_noUnderflowSub_sound hS hx hy with
    | intro x' hxy =>
      cases hxy with
      | intro y' hxy =>
        injection hxy.1 with h1
        injection hxy.2.1 with h2
        subst h1
        subst h2
        exact hxy.2.2.1
  | false =>
    rw [hS, Bool.false_or] at h
    rw [isZeroExact_eq h hy]
    exact Nat.zero_le x

/-- Nonzero-divisor check combining `AbsVal.nonzeroDiv` with `Tnum` known-one
bits (`tnum.val > 0`) and `StridedCong` nonzero residues (`r > 0`). -/
def nonzeroDivSafe (w : Nat) (a : AbsVal) : Bool :=
  AbsVal.nonzeroDiv w a ||
  Nat.blt 0 a.tnum.val ||
  match a.sc with
  | .cong _ r => Nat.blt 0 r
  | _ => false

theorem nonzeroDivSafe_sound {w y : Nat} {a : AbsVal}
    (h : nonzeroDivSafe w a = true) (hy : a.denote w (some y)) : 0 < y := by
  have hyE := absVal_some_elim hy
  unfold nonzeroDivSafe at h
  cases hN : AbsVal.nonzeroDiv w a with
  | true =>
    cases absVal_nonzeroDiv_sound hN hy with
    | intro y' hy' =>
      injection hy'.1 with hEq
      subst hEq
      exact hy'.2.1
  | false =>
    rw [hN, Bool.false_or] at h
    cases hT : Nat.blt 0 a.tnum.val with
    | true =>
      have hValPos : 0 < a.tnum.val := lt_of_blt_true hT
      apply Nat.pos_of_ne_zero
      intro hy0
      subst hy0
      have hTn := hyE.2.1
      rw [tnum_denote_iff_bitAt] at hTn
      have hValZero : a.tnum.val = 0 := by
        apply nat_eq_of_bitAt
        intro k
        rw [bitAt_zero_nat]
        cases hm : bitAt a.tnum.mask k with
        | false =>
          have hBit := hTn.2 k hm
          rw [bitAt_zero_nat] at hBit
          exact hBit.symm
        | true =>
          have hWf : bitAt (Nat.land a.tnum.val a.tnum.mask) k = bitAt 0 k := by
            rw [Nat.eq_of_beq_eq_true hTn.1]
          rw [bitAt_land, hm, Bool.and_true, bitAt_zero_nat] at hWf
          exact hWf
      rw [hValZero] at hValPos
      exact Nat.lt_irrefl 0 hValPos
    | false =>
      rw [hT, Bool.false_or] at h
      have hSc := hyE.2.2.2
      cases hScTag : a.sc with
      | bot => rw [hScTag] at h; nomatch h
      | top => rw [hScTag] at h; nomatch h
      | cong m r =>
        rw [hScTag] at h hSc
        have hrPos : 0 < r := lt_of_blt_true h
        apply Nat.pos_of_ne_zero
        intro hy0
        subst hy0
        have hMod0 : 0 % m = r := hSc.2.2
        rw [Nat.zero_mod] at hMod0
        rw [← hMod0] at hrPos
        exact Nat.lt_irrefl 0 hrPos

/-- Overflow boolean and guard for `subWithOverflow` (underflow iff `x < y`). -/
def subOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  let w := uintWidth u
  let known? :=
    match noUnderflowSubSafe w a1 a2 with
    | true => some false
    | false => decideCmpAbs .lt w a1 a2
  mkBoolAbs known? (synthCmpGuard .lt u srcL srcR a1 a2)

theorem subOverflowBoolAbs_isInit (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (subOverflowBoolAbs u srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

theorem subOverflowBoolAbs_sound {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (subOverflowBoolAbs u srcL srcR a1 a2).denoteBool locals (!(Nat.ble y x)) := by
  rw [← nat_blt_eq_not_ble]
  apply mkBoolAbs_sound
  · intro r hr
    cases hNo : noUnderflowSubSafe (uintWidth u) a1 a2 with
    | true =>
      rw [hNo] at hr
      injection hr with hr
      subst hr
      rw [nat_blt_eq_not_ble,
        Nat.ble_eq_true_of_le (noUnderflowSubSafe_sound hNo hx hy)]
      rfl
    | false =>
      rw [hNo] at hr
      exact decideCmpAbs_sound hr hx hy
  · exact synthCmpGuard_sound (op := .lt) hx hy hL hR

private theorem mul_overflow_ugt_iff {w x v : Nat} (hvPos : 0 < v) :
    Nat.ble (modPow2 w) (x * v) = true ↔ (modPow2 w - 1) / v < x := by
  let M := modPow2 w
  let q := (M - 1) / v
  have hMPos : 0 < M := modPow2_pos w
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hMPos
  have hDecomp : v * q + (M - 1) % v = M - 1 := nat_div_add_mod (M - 1) v
  have hRemLt : (M - 1) % v < v := Nat.mod_lt (M - 1) hvPos
  constructor
  · intro hBle
    have hLe : M ≤ x * v := Nat.le_of_ble_eq_true hBle
    exact Nat.lt_of_not_ge (fun hXLeQ => by
      have h1 : x * v ≤ q * v := Nat.mul_le_mul_right v hXLeQ
      rw [Nat.mul_comm q v] at h1
      have h2 : v * q ≤ M - 1 := by
        rw [← hDecomp]
        exact Nat.le_add_right _ _
      have h3 : M - 1 < M := Nat.sub_lt hMPos Nat.zero_lt_one
      exact Nat.not_le_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3) hLe)
  · intro hLt
    have hMul : (q + 1) * v ≤ x * v := Nat.mul_le_mul_right v hLt
    have hExp : (q + 1) * v = v * q + v := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q v]
    have hStep : M ≤ v * q + v := by
      rw [← hM1, ← hDecomp, Nat.add_assoc]
      exact Nat.add_le_add_left hRemLt (v * q)
    rw [hExp] at hMul
    exact Nat.ble_eq_true_of_le (Nat.le_trans hStep hMul)

private def mulOverflowKnown? (w : Nat) (a1 a2 : AbsVal) : Option Bool :=
  match isZeroExact w a1 || isZeroExact w a2 with
  | true => some false
  | false =>
    match AbsVal.noOverflowMul w a1 a2 with
    | true => some false
    | false =>
      match a1.lbound? with
      | none => none
      | some lo1 =>
        match a2.lbound? with
        | none => none
        | some lo2 =>
          match Nat.ble (modPow2 w) (lo1 * lo2) with
          | true => some true
          | false => none

private def mulOverflowGuardOne (u : UintTy) (src : Option Nat) (aOther : AbsVal) :
    RelGuard :=
  match src with
  | none => .none
  | some r =>
    match aOther.exactVal? (uintWidth u) with
    | none => .none
    | some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u ((modPow2 (uintWidth u) - 1) / v)
      | false => .none

private def mulOverflowGuard (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match srcL with
  | some r =>
    match a2.exactVal? (uintWidth u) with
    | some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u ((modPow2 (uintWidth u) - 1) / v)
      | false => .none
    | none => mulOverflowGuardOne u srcR a1
  | none => mulOverflowGuardOne u srcR a1

/-- Overflow boolean and optional guard for `mulWithOverflow`. -/
def mulOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  mkBoolAbs (mulOverflowKnown? (uintWidth u) a1 a2)
    (mulOverflowGuard u srcL srcR a1 a2)

theorem mulOverflowBoolAbs_isInit (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (mulOverflowBoolAbs u srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

private theorem mulOverflowKnown?_sound {w x y : Nat} {a1 a2 : AbsVal} {r : Bool}
    (hr : mulOverflowKnown? w a1 a2 = some r)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    Nat.ble (modPow2 w) (x * y) = r := by
  have hMPos : 0 < modPow2 w := modPow2_pos w
  unfold mulOverflowKnown? at hr
  cases hZ1 : isZeroExact w a1 with
  | true =>
    rw [hZ1, Bool.true_or] at hr; cases hr
    rw [isZeroExact_eq hZ1 hx, Nat.zero_mul]
    cases hB : Nat.ble (modPow2 w) 0 with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hMPos (Nat.le_of_ble_eq_true hB))
  | false =>
    rw [hZ1, Bool.false_or] at hr
    cases hZ2 : isZeroExact w a2 with
    | true =>
      rw [hZ2] at hr; cases hr
      rw [isZeroExact_eq hZ2 hy, Nat.mul_zero]
      cases hB : Nat.ble (modPow2 w) 0 with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hMPos (Nat.le_of_ble_eq_true hB))
    | false =>
      rw [hZ2] at hr; dsimp only at hr
      cases hNo : AbsVal.noOverflowMul w a1 a2 with
      | true =>
        rw [hNo] at hr; cases hr
        have hLt := absVal_noOverflowMul_sound hNo hx hy
        cases hB : Nat.ble (modPow2 w) (x * y) with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true hB))
      | false =>
        rw [hNo] at hr; dsimp only at hr
        cases hL1 : a1.lbound? with
        | none => rw [hL1] at hr; nomatch hr
        | some lo1 =>
          rw [hL1] at hr; dsimp only at hr
          cases hL2 : a2.lbound? with
          | none => rw [hL2] at hr; nomatch hr
          | some lo2 =>
            rw [hL2] at hr; dsimp only at hr
            cases hOv : Nat.ble (modPow2 w) (lo1 * lo2) with
            | false => rw [hOv] at hr; nomatch hr
            | true =>
              rw [hOv] at hr; cases hr
              exact Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOv)
                (Nat.mul_le_mul (absVal_lbound?_sound hL1 hx)
                  (absVal_lbound?_sound hL2 hy)))

private theorem mulOverflowGuardOne_sound {u : UintTy} {src : Option Nat}
    {aOther : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hy : aOther.denote (uintWidth u) (some y))
    (hS : ∀ r, src = some r → localUintNat? locals r u = some x) :
    (mulOverflowGuardOne u src aOther).denote locals
      (Nat.ble (modPow2 (uintWidth u)) (x * y)) := by
  unfold mulOverflowGuardOne
  cases src with
  | none => exact True.intro
  | some r =>
    cases hE : aOther.exactVal? (uintWidth u) with
    | none => exact True.intro
    | some v =>
      dsimp only
      cases hPos : Nat.blt 0 v with
      | false => exact True.intro
      | true =>
        have h2 := (absVal_exactVal?_sound hE hy).1
        injection h2 with h2; subst h2
        intro x' hx'
        rw [hS r rfl] at hx'; injection hx' with hx'; subst hx'
        exact mul_overflow_ugt_iff (lt_of_blt_true hPos)

theorem mulOverflowBoolAbs_sound {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (mulOverflowBoolAbs u srcL srcR a1 a2).denoteBool locals
      (Nat.ble (modPow2 (uintWidth u)) (x * y)) := by
  apply mkBoolAbs_sound (fun _ hr => mulOverflowKnown?_sound hr hx hy)
  have hRight : (mulOverflowGuardOne u srcR a1).denote locals
      (Nat.ble (modPow2 (uintWidth u)) (x * y)) := by
    rw [Nat.mul_comm x y]
    exact mulOverflowGuardOne_sound hx hR
  unfold mulOverflowGuard
  cases srcL with
  | none => exact hRight
  | some r =>
    cases hE2 : a2.exactVal? (uintWidth u) with
    | none => exact hRight
    | some v =>
      dsimp only
      cases hPos : Nat.blt 0 v with
      | false => exact True.intro
      | true =>
        have h2 := (absVal_exactVal?_sound hE2 hy).1
        injection h2 with h2; subst h2
        intro x' hx'
        rw [hL r rfl] at hx'; injection hx' with hx'; subst hx'
        exact mul_overflow_ugt_iff (lt_of_blt_true hPos)

/-- True iff both operands originate from the same local register. -/
def sameLocalOpt (srcL srcR : Option Nat) : Bool :=
  match srcL, srcR with
  | some l, some r => Nat.beq l r
  | _, _ => false

private theorem sameLocalOpt_eq {locals : List LocalSlot} {u : UintTy}
    {srcL srcR : Option Nat} {x y : Nat}
    (hSame : sameLocalOpt srcL srcR = true)
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    x = y := by
  unfold sameLocalOpt at hSame
  cases srcL with
  | none => nomatch hSame
  | some l =>
    cases srcR with
    | none => nomatch hSame
    | some r =>
      have hEq := Nat.eq_of_beq_eq_true hSame
      subst hEq
      have h1 := hL l rfl
      have h2 := hR l rfl
      rw [h1] at h2
      injection h2

private theorem nat_xor_self_zero (x : Nat) : Nat.xor x x = 0 := by
  apply nat_eq_of_bitAt
  intro k
  rw [bitAt_xor, bitAt_zero_nat]
  cases bitAt x k <;> rfl

private theorem nat_land_self (x : Nat) : Nat.land x x = x := by
  apply nat_eq_of_bitAt
  intro k
  rw [bitAt_land]
  cases bitAt x k <;> rfl

private theorem nat_lor_self (x : Nat) : Nat.lor x x = x := by
  apply nat_eq_of_bitAt
  intro k
  rw [bitAt_lor]
  cases bitAt x k <;> rfl

/-- Constant outcome of comparing a value with itself (`x op x`). -/
def decideCmpSame : BinOp → Bool
  | .eq | .le | .ge => true
  | _ => false

/-- Unsigned wrapping addition preserving the other operand when one side is
known `0`. -/
def addUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match isZeroExact w a1, isZeroExact w a2 with
  | true, _ => a2
  | false, true => a1
  | false, false => AbsVal.addWrap w a1 a2

theorem addUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    (addUintAbs w a1 a2).denote w (some (wrapVal w (x + y))) := by
  unfold addUintAbs
  cases hZ1 : isZeroExact w a1 with
  | true =>
    rw [isZeroExact_eq hZ1 hx, Nat.zero_add, wrapVal_of_lt (absVal_some_elim hy).1]
    exact hy
  | false =>
    cases hZ2 : isZeroExact w a2 with
    | true =>
      rw [isZeroExact_eq hZ2 hy, Nat.add_zero, wrapVal_of_lt (absVal_some_elim hx).1]
      exact hx
    | false => exact absVal_addWrap_sound hw hx hy hi1 hi2

/-- Unsigned wrapping subtraction preserving `a1` when `a2` is known `0`. -/
def subUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match isZeroExact w a2 with
  | true => a1
  | false => AbsVal.subWrap w a1 a2

theorem subUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    (subUintAbs w a1 a2).denote w (some (wrapVal w (modPow2 w + x - y))) := by
  unfold subUintAbs
  cases hZ2 : isZeroExact w a2 with
  | true =>
    rw [isZeroExact_eq hZ2 hy, Nat.sub_zero]
    have hMod : wrapVal w (modPow2 w + x) = x := by
      change (modPow2 w + x) % modPow2 w = x
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (absVal_some_elim hx).1
    rw [hMod]
    exact hx
  | false => exact absVal_subWrap_sound hw hx hy hi1 hi2

/-- Abstract unsigned `BinOp` transfer for operands of equal type `u`.
When both operands share the same source local (`sameLocalOpt`), self-identities
(`x - x = 0`, `x ^ x = 0`, `x & x = x`, `x | x = x`, `x / x = 1`, `x % x = 0`,
`x == x = true`, etc.) are folded directly. -/
def binOpSameAbs (op : BinOp) (u : UintTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  let w := uintWidth u
  let same := sameLocalOpt srcL srcR
  match op with
  | .add => some (mkUintVal u (addUintAbs w a1 a2))
  | .addUnchecked =>
    match noOverflowAddSafe w a1 a2 with
    | true => some (mkUintVal u (addUintAbs w a1 a2))
    | false => none
  | .addWithOverflow =>
    some (mkUintBoolPairVal u (addUintAbs w a1 a2)
      (addOverflowBoolAbs u srcL srcR a1 a2))
  | .sub =>
    match same with
    | true => some (mkUintVal u (AbsVal.const w 0))
    | false => some (mkUintVal u (subUintAbs w a1 a2))
  | .subUnchecked =>
    match same with
    | true => some (mkUintVal u (AbsVal.const w 0))
    | false =>
      match noUnderflowSubSafe w a1 a2 with
      | true => some (mkUintVal u (subUintAbs w a1 a2))
      | false => none
  | .subWithOverflow =>
    match same with
    | true => some (mkUintBoolPairVal u (AbsVal.const w 0) (.exact false .none))
    | false =>
      some (mkUintBoolPairVal u (subUintAbs w a1 a2)
        (subOverflowBoolAbs u srcL srcR a1 a2))
  | .mul => some (mkUintVal u (mulUintAbs w a1 a2))
  | .mulUnchecked =>
    match AbsVal.noOverflowMul w a1 a2 with
    | true => some (mkUintVal u (mulUintAbs w a1 a2))
    | false => none
  | .mulWithOverflow =>
    some (mkUintBoolPairVal u (mulUintAbs w a1 a2)
      (mulOverflowBoolAbs u srcL srcR a1 a2))
  | .div =>
    match nonzeroDivSafe w a2 with
    | true =>
      match same with
      | true => some (mkUintVal u (AbsVal.const w 1))
      | false => some (mkUintVal u (divUintAbs w a1 a2))
    | false => none
  | .rem =>
    match nonzeroDivSafe w a2 with
    | true =>
      match same with
      | true => some (mkUintVal u (AbsVal.const w 0))
      | false => some (mkUintVal u (remUintAbs w a1 a2))
    | false => none
  | .bitAnd =>
    match same with
    | true => some (mkUintVal u a1)
    | false => some (mkUintVal u (AbsVal.bitAnd w a1 a2))
  | .bitOr =>
    match same with
    | true => some (mkUintVal u a1)
    | false => some (mkUintVal u (AbsVal.bitOr w a1 a2))
  | .bitXor =>
    match same with
    | true => some (mkUintVal u (AbsVal.const w 0))
    | false => some (mkUintVal u (AbsVal.bitXor w a1 a2))
  | .eq | .ne | .lt | .le | .gt | .ge =>
    match same with
    | true => some (.bool (.exact (decideCmpSame op) .none))
    | false =>
      some (.bool (mkBoolAbs (decideCmpAbs op w a1 a2)
        (synthCmpGuard op u srcL srcR a1 a2)))
  | _ => none

def binOpToShift? : BinOp → Option ShiftOp
  | .shl => some .shl
  | .shlUnchecked => some .shlUnchecked
  | .shr => some .shr
  | .shrUnchecked => some .shrUnchecked
  | _ => none

private theorem binOpToShift?_eq {op : BinOp} {sop : ShiftOp}
    (h : binOpToShift? op = some sop) :
    match sop with
    | .shl => op = .shl
    | .shlUnchecked => op = .shlUnchecked
    | .shr => op = .shr
    | .shrUnchecked => op = .shrUnchecked := by
  cases op with
  | shl => injection h with h; subst h; rfl
  | shlUnchecked => injection h with h; subst h; rfl
  | shr => injection h with h; subst h; rfl
  | shrUnchecked => injection h with h; subst h; rfl
  | _ => nomatch h

/-- Abstract unsigned `BinOp` transfer on evaluated operands `(u1, a1)` and
`(u2, a2)`. Shifts accept any unsigned right-hand type; every other operator
requires equal operand types (`evalScalarBinOp` requires equal byte widths). -/
def binOpUintAbs (op : BinOp) (u1 : UintTy) (a1 : AbsVal) (srcL : Option Nat)
    (u2 : UintTy) (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  let w := uintWidth u1
  let k? := a2.exactVal? (uintWidth u2)
  match binOpToShift? op with
  | some .shl => some (mkUintVal u1 (shlUintAbs w a1 (k?.map (fun k => Nat.mod k w))))
  | some .shlUnchecked =>
    match AbsVal.shiftInBounds w (uintWidth u2) a2 with
    | true => some (mkUintVal u1 (shlUintAbs w a1 k?))
    | false => none
  | some .shr => some (mkUintVal u1 (shrUintAbs w a1 (k?.map (fun k => Nat.mod k w))))
  | some .shrUnchecked =>
    match AbsVal.shiftInBounds w (uintWidth u2) a2 with
    | true => some (mkUintVal u1 (shrUintAbs w a1 k?))
    | false => none
  | none =>
    match uintTyBeq u1 u2 with
    | false => none
    | true => binOpSameAbs op u1 a1 srcL a2 srcR

theorem shlUintAbs_sound {w x : Nat} {a : AbsVal} {k? : Option Nat} {s : Nat}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hk : ∀ k, k? = some k → k = s) :
    (shlUintAbs w a k?).denote w (some (wrapVal w (Nat.shiftLeft x s))) := by
  unfold shlUintAbs
  cases k? with
  | none => exact absVal_topInit_sound (nat_mod_lt _ (modPow2_pos w))
  | some k =>
    rw [← hk k rfl]
    exact absVal_shlConst_sound hw ha hai

theorem shrUintAbs_sound {w x : Nat} {a : AbsVal} {k? : Option Nat} {s : Nat}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hk : ∀ k, k? = some k → k = s) :
    (shrUintAbs w a k?).denote w (some (Nat.shiftRight x s)) := by
  unfold shrUintAbs
  cases k? with
  | none =>
    exact absVal_topInit_sound (shiftRight_lt_of_lt (absVal_some_elim ha).1)
  | some k =>
    rw [← hk k rfl]
    exact absVal_shrConst_sound hw ha hai

theorem exactVal?_eq {w c x : Nat} {a : AbsVal} (hE : a.exactVal? w = some c)
    (ha : a.denote w (some x)) : c = x := by
  have h := (absVal_exactVal?_sound hE ha).1
  injection h with h
  exact h.symm

theorem cmp_bool_denote {op : BinOp} {u : UintTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (MirAbsVal.bool (mkBoolAbs (decideCmpAbs op (uintWidth u) a1 a2)
      (synthCmpGuard op u srcL srcR a1 a2))).denote locals
      (.scalar (boolToScalar (cmpResult op x y))) :=
  boolAbs_denote_of_bool (mkBoolAbs_sound
    (fun _ hr => decideCmpAbs_sound hr hx hy) (synthCmpGuard_sound hx hy hL hR))

private theorem evalScalarBinOp_uint_cmp {u : UintTy} {op : BinOp} {x y : Nat}
    (locals : List LocalSlot) (mem : Memory) {cop : CmpOp}
    (hop : binOpToCmp? op = some cop) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (cmpResult op x y))) locals mem := by
  cases op with
  | eq => exact evalScalarBinOp_uint_eq locals mem
  | ne => exact evalScalarBinOp_uint_ne locals mem
  | lt => exact evalScalarBinOp_uint_lt locals mem
  | le => exact evalScalarBinOp_uint_le locals mem
  | gt => exact evalScalarBinOp_uint_gt locals mem
  | ge => exact evalScalarBinOp_uint_ge locals mem
  | _ => nomatch hop

private theorem cmpResult_self_of_toCmp {op : BinOp} {cop : CmpOp}
    (hop : binOpToCmp? op = some cop) (z : Nat) :
    cmpResult op z z = decideCmpSame op := by
  cases op with
  | eq => exact nat_beq_refl z
  | ne => exact congrArg Bool.not (nat_beq_refl z)
  | lt =>
    change Nat.blt z z = false
    rw [nat_blt_eq_not_ble, Nat.ble_eq_true_of_le (Nat.le_refl z)]; rfl
  | le => exact Nat.ble_eq_true_of_le (Nat.le_refl z)
  | gt =>
    change Nat.blt z z = false
    rw [nat_blt_eq_not_ble, Nat.ble_eq_true_of_le (Nat.le_refl z)]; rfl
  | ge => exact Nat.ble_eq_true_of_le (Nat.le_refl z)
  | _ => nomatch hop

/-- Scalar-level soundness of `binOpSameAbs` against `evalScalarBinOp`. -/
theorem binOpSameAbs_sound {op : BinOp} {u : UintTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory)
    (h : binOpSameAbs op u a1 srcL a2 srcR = some av)
    (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem
        false = .ok v locals mem ∧ av.denote locals v := by
  have hw := uintWidth_valid u
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  have hWrap0 : wrapVal (uintWidth u) (modPow2 (uintWidth u) + x - x) = 0 := by
    rw [Nat.add_sub_cancel]; exact Nat.mod_self _
  have hCmp : ∀ (op' : BinOp) (cop : CmpOp), binOpToCmp? op' = some cop →
      (match sameLocalOpt srcL srcR with
       | true => some (.bool (.exact (decideCmpSame op') .none))
       | false =>
         some (.bool (mkBoolAbs (decideCmpAbs op' (uintWidth u) a1 a2)
           (synthCmpGuard op' u srcL srcR a1 a2)))) = some av →
      ∃ v, evalScalarBinOp op' ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem
          false = .ok v locals mem ∧ av.denote locals v := by
    intro op' cop hCop hC
    have hEv := evalScalarBinOp_uint_cmp (u := u) (x := x) (y := y) locals mem hCop
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at hC; cases hC
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact _ .none)
        ⟨cmpResult_self_of_toCmp hCop x, True.intro⟩⟩
    | false =>
      rw [hSame] at hC; cases hC
      exact ⟨_, hEv, cmp_bool_denote hx hy hL hR⟩
  cases op with
  | add =>
    cases h
    exact ⟨_, evalScalarBinOp_uint_add locals mem,
      mkUintVal_denote (addUintAbs_sound hw hi1 hi2 hx hy)⟩
  | addUnchecked =>
    dsimp only [binOpSameAbs] at h
    cases hB : noOverflowAddSafe (uintWidth u) a1 a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_addUnchecked locals mem
        (noOverflowAddSafe_sound hB hx hy),
        mkUintVal_denote (addUintAbs_sound hw hi1 hi2 hx hy)⟩
  | addWithOverflow =>
    cases h
    exact ⟨_, evalScalarBinOp_uint_addWithOverflow locals mem,
      mkUintBoolPairVal_denote (addUintAbs_sound hw hi1 hi2 hx hy)
        (addOverflowBoolAbs_isInit u srcL srcR a1 a2)
        (addOverflowBoolAbs_sound hx hy hL hR)⟩
  | sub =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_sub (u := u) (a := x) (b := x) locals mem hxLt hxLt
      rw [hWrap0] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_sub locals mem hxLt hyLt,
        mkUintVal_denote (subUintAbs_sound hw hi1 hi2 hx hy)⟩
  | subUnchecked =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_subUnchecked (u := u) (a := x) (b := x)
        locals mem hxLt (Nat.le_refl x)
      rw [hWrap0] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h; dsimp only at h
      cases hB : noUnderflowSubSafe (uintWidth u) a1 a2 with
      | false => rw [hB] at h; nomatch h
      | true =>
        rw [hB] at h; cases h
        exact ⟨_, evalScalarBinOp_uint_subUnchecked locals mem hxLt
          (noUnderflowSubSafe_sound hB hx hy),
          mkUintVal_denote (subUintAbs_sound hw hi1 hi2 hx hy)⟩
  | subWithOverflow =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_subWithOverflow (u := u) (a := x) (b := x)
        locals mem hxLt hxLt
      rw [hWrap0, Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, mkUintBoolPairVal_denote
        (absVal_const_denote_lt hw (modPow2_pos _)) rfl ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_subWithOverflow locals mem hxLt hyLt,
        mkUintBoolPairVal_denote (subUintAbs_sound hw hi1 hi2 hx hy)
          (subOverflowBoolAbs_isInit u srcL srcR a1 a2)
          (subOverflowBoolAbs_sound hx hy hL hR)⟩
  | mul =>
    cases h
    exact ⟨_, evalScalarBinOp_uint_mul locals mem,
      mkUintVal_denote (mulUintAbs_sound hw hx hy)⟩
  | mulUnchecked =>
    dsimp only [binOpSameAbs] at h
    cases hB : AbsVal.noOverflowMul (uintWidth u) a1 a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_mulUnchecked locals mem
        (absVal_noOverflowMul_sound hB hx hy),
        mkUintVal_denote (mulUintAbs_sound hw hx hy)⟩
  | mulWithOverflow =>
    cases h
    exact ⟨_, evalScalarBinOp_uint_mulWithOverflow locals mem,
      mkUintBoolPairVal_denote (mulUintAbs_sound hw hx hy)
        (mulOverflowBoolAbs_isInit u srcL srcR a1 a2)
        (mulOverflowBoolAbs_sound hx hy hL hR)⟩
  | div =>
    dsimp only [binOpSameAbs] at h
    cases hB : nonzeroDivSafe (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h; dsimp only at h
      have hyPos := nonzeroDivSafe_sound hB hy
      cases hSame : sameLocalOpt srcL srcR with
      | true =>
        rw [hSame] at h; cases h
        have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
        have hEv := evalScalarBinOp_uint_div (u := u) (a := x) (b := x)
          locals mem hyPos
        rw [Nat.div_self hyPos, wrapVal_of_lt (one_lt_modPow2_uint u)] at hEv
        exact ⟨_, hEv, mkUintVal_denote
          (absVal_const_denote_lt hw (one_lt_modPow2_uint u))⟩
      | false =>
        rw [hSame] at h; cases h
        exact ⟨_, evalScalarBinOp_uint_div locals mem hyPos,
          mkUintVal_denote (divUintAbs_sound hw hx hy hyPos)⟩
  | rem =>
    dsimp only [binOpSameAbs] at h
    cases hB : nonzeroDivSafe (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h; dsimp only at h
      have hyPos := nonzeroDivSafe_sound hB hy
      cases hSame : sameLocalOpt srcL srcR with
      | true =>
        rw [hSame] at h; cases h
        have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
        have hEv := evalScalarBinOp_uint_rem (u := u) (a := x) (b := x)
          locals mem hyPos
        rw [Nat.mod_self, wrapVal_of_lt (modPow2_pos _)] at hEv
        exact ⟨_, hEv, mkUintVal_denote
          (absVal_const_denote_lt hw (modPow2_pos _))⟩
      | false =>
        rw [hSame] at h; cases h
        exact ⟨_, evalScalarBinOp_uint_rem locals mem hyPos,
          mkUintVal_denote (remUintAbs_sound hw hx hy hyPos)⟩
  | bitAnd =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_bitAnd (u := u) (a := x) (b := x)
        locals mem hxLt
      rw [nat_land_self] at hEv
      exact ⟨_, hEv, mkUintVal_denote hx⟩
    | false =>
      rw [hSame] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_bitAnd locals mem hxLt,
        mkUintVal_denote (absVal_bitAnd_sound hw hx hy hi1 hi2)⟩
  | bitOr =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_bitOr (u := u) (a := x) (b := x)
        locals mem hxLt hxLt
      rw [nat_lor_self] at hEv
      exact ⟨_, hEv, mkUintVal_denote hx⟩
    | false =>
      rw [hSame] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_bitOr locals mem hxLt hyLt,
        mkUintVal_denote (absVal_bitOr_sound hw hx hy hi1 hi2)⟩
  | bitXor =>
    dsimp only [binOpSameAbs] at h
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h; cases h
      have hxy := sameLocalOpt_eq hSame hL hR; subst hxy
      have hEv := evalScalarBinOp_uint_bitXor (u := u) (a := x) (b := x)
        locals mem hxLt hxLt
      rw [nat_xor_self_zero] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h; cases h
      exact ⟨_, evalScalarBinOp_uint_bitXor locals mem hxLt hyLt,
        mkUintVal_denote (absVal_bitXor_sound hw hx hy hi1 hi2)⟩
  | eq | ne | lt | le | gt | ge => exact hCmp _ _ rfl h
  | _ => nomatch h

theorem binOpUintAbs_not_offset {op : BinOp} {u1 u2 : UintTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal}
    (h : binOpUintAbs op u1 a1 srcL u2 a2 srcR = some av) : op ≠ .offset := by
  intro hOp
  subst hOp
  unfold binOpUintAbs at h
  dsimp only at h
  cases hU : uintTyBeq u1 u2 <;> (rw [hU] at h; nomatch h)

/-- Scalar-level soundness of `binOpUintAbs` against `evalScalarBinOp` at
`isSigned = false`. -/
theorem binOpUintAbs_sound {op : BinOp} {u1 u2 : UintTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory)
    (h : binOpUintAbs op u1 a1 srcL u2 a2 srcR = some av)
    (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote (uintWidth u1) (some x))
    (hy : a2.denote (uintWidth u2) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u1 = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u2 = some y) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes u1⟩ ⟨y, uintBytes u2⟩ locals mem
        false = .ok v locals mem ∧ av.denote locals v := by
  have hw1 := uintWidth_valid u1
  have hxLt := (absVal_some_elim hx).1
  have hKShift : ∀ k, (a2.exactVal? (uintWidth u2)).map
      (fun k => Nat.mod k (uintWidth u1)) = some k →
      k = Nat.mod y (uintWidth u1) := by
    intro k hk
    cases hE : a2.exactVal? (uintWidth u2) with
    | none => rw [hE] at hk; nomatch hk
    | some c =>
      rw [hE] at hk
      injection hk with hk
      rw [← hk, exactVal?_eq hE hy]
  have hKExact : ∀ k, a2.exactVal? (uintWidth u2) = some k → k = y :=
    fun k hE => exactVal?_eq hE hy
  unfold binOpUintAbs at h
  dsimp only at h
  cases hSh : binOpToShift? op with
  | none =>
    rw [hSh] at h; dsimp only at h
    cases hU : uintTyBeq u1 u2 with
    | false => rw [hU] at h; nomatch h
    | true =>
      rw [hU] at h
      have hu := uintTy_eq_of_beq hU
      subst hu
      exact binOpSameAbs_sound mem h hi1 hi2 hx hy hL hR
  | some sop =>
    rw [hSh] at h
    have hOpEq := binOpToShift?_eq hSh
    cases sop with
    | shl =>
      have hOp : op = .shl := hOpEq; subst hOp
      injection h with h; subst h
      exact ⟨_, evalScalarBinOp_uint_shl locals mem,
        mkUintVal_denote (shlUintAbs_sound hw1 hx hi1 hKShift)⟩
    | shr =>
      have hOp : op = .shr := hOpEq; subst hOp
      injection h with h; subst h
      exact ⟨_, evalScalarBinOp_uint_shr locals mem hxLt,
        mkUintVal_denote (shrUintAbs_sound hw1 hx hi1 hKShift)⟩
    | shlUnchecked =>
      have hOp : op = .shlUnchecked := hOpEq; subst hOp
      dsimp only at h
      cases hB : AbsVal.shiftInBounds (uintWidth u1) (uintWidth u2) a2 with
      | false => rw [hB] at h; nomatch h
      | true =>
        rw [hB] at h; injection h with h; subst h
        cases absVal_shiftInBounds_sound hB hy with
        | intro y' hy' =>
          injection hy'.1 with hyEq; subst hyEq
          exact ⟨_, evalScalarBinOp_uint_shlUnchecked locals mem hy'.2.1,
            mkUintVal_denote (shlUintAbs_sound hw1 hx hi1 hKExact)⟩
    | shrUnchecked =>
      have hOp : op = .shrUnchecked := hOpEq; subst hOp
      dsimp only at h
      cases hB : AbsVal.shiftInBounds (uintWidth u1) (uintWidth u2) a2 with
      | false => rw [hB] at h; nomatch h
      | true =>
        rw [hB] at h; injection h with h; subst h
        cases absVal_shiftInBounds_sound hB hy with
        | intro y' hy' =>
          injection hy'.1 with hyEq; subst hyEq
          exact ⟨_, evalScalarBinOp_uint_shrUnchecked locals mem hxLt hy'.2.1,
            mkUintVal_denote (shrUintAbs_sound hw1 hx hi1 hKExact)⟩

/-! ### Signed (`IntTy`) binary operations -/

/-- Signed result value (initialized, with no source local). -/
def mkSintVal (i : IntTy) (a : AbsVal) : MirAbsVal :=
  .sint i (AbsVal.ensureInit (uintWidth (intTwin i)) a) none

theorem mkSintVal_denote {locals : List LocalSlot} {i : IntTy} {a : AbsVal}
    {bits : Nat} (h : a.denote (uintWidth (intTwin i)) (some bits)) :
    (mkSintVal i a).denote locals (.scalar ⟨bits, uintBytes (intTwin i)⟩) :=
  ⟨absVal_ensureInit_isInit _ a, rfl, absVal_ensureInit_sound h, True.intro⟩

/-- Checked signed arithmetic tuple `(i, bool)` (initialized). -/
def mkSintBoolPairVal (i : IntTy) (a : AbsVal) (ov : BoolAbs) : MirAbsVal :=
  .sintBoolPair i (AbsVal.ensureInit (uintWidth (intTwin i)) a) ov

theorem mkSintBoolPairVal_denote {locals : List LocalSlot} {i : IntTy}
    {a : AbsVal} {ov : BoolAbs} {bits : Nat} {vb : Value}
    (hOvI : ov.isInit = true)
    (ha : a.denote (uintWidth (intTwin i)) (some bits))
    (hov : ov.denote locals (some vb)) :
    (mkSintBoolPairVal i a ov).denote locals
      (.aggregate 0 [.scalar ⟨bits, uintBytes (intTwin i)⟩, vb]) :=
  ⟨absVal_ensureInit_isInit _ a, hOvI, rfl, absVal_ensureInit_sound ha, hov⟩

/-- `a` (a signed bit pattern) is certainly non-negative (`< 2^(w-1)`). -/
def sintNonneg (i : IntTy) (a : AbsVal) : Bool :=
  match a.ubound? with
  | some hi => Nat.blt hi (modPow2 (uintWidth (intTwin i)) / 2)
  | none => false

theorem sintNonneg_sound {i : IntTy} {a : AbsVal} {x : Nat}
    (h : sintNonneg i a = true) (hx : a.denote (uintWidth (intTwin i)) (some x)) :
    x < modPow2 (uintWidth (intTwin i)) / 2 := by
  unfold sintNonneg at h
  cases hU : a.ubound? with
  | none => rw [hU] at h; nomatch h
  | some hi =>
    rw [hU] at h
    exact Nat.lt_of_le_of_lt (absVal_ubound?_sound hU hx) (lt_of_blt_true h)

/-- `a` (a signed bit pattern) is certainly negative (`≥ 2^(w-1)`). -/
def sintNeg (i : IntTy) (a : AbsVal) : Bool :=
  match a.lbound? with
  | some lo => Nat.ble (modPow2 (uintWidth (intTwin i)) / 2) lo
  | none => false

theorem sintNeg_sound {i : IntTy} {a : AbsVal} {x : Nat}
    (h : sintNeg i a = true) (hx : a.denote (uintWidth (intTwin i)) (some x)) :
    modPow2 (uintWidth (intTwin i)) / 2 ≤ x ∧
      x < modPow2 (uintWidth (intTwin i)) := by
  unfold sintNeg at h
  cases hL : a.lbound? with
  | none => rw [hL] at h; nomatch h
  | some lo =>
    rw [hL] at h
    exact ⟨Nat.le_trans (Nat.le_of_ble_eq_true h) (absVal_lbound?_sound hL hx),
      (absVal_some_elim hx).1⟩

/-- Certifies `signedOverflowAdd x y (uintBytes (intTwin i)) = false`. -/
def sintNoOverflowAdd (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  let w := uintWidth (intTwin i)
  isZeroExact w a1 || isZeroExact w a2 ||
    (sintNonneg i a1 && sintNeg i a2) ||
    (sintNeg i a1 && sintNonneg i a2) ||
    match a1.ubound?, a2.ubound? with
    | some hi1, some hi2 => Nat.blt (hi1 + hi2) (modPow2 w / 2)
    | _, _ => false

theorem sintNoOverflowAdd_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintNoOverflowAdd i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowAdd x y (uintBytes (intTwin i)) = false := by
  unfold sintNoOverflowAdd at h
  cases hZ1 : isZeroExact (uintWidth (intTwin i)) a1 with
  | true =>
    have hx0 := isZeroExact_eq hZ1 hx
    subst hx0
    exact signedOverflowAdd_false_of_zero_left (absVal_some_elim hy).1
  | false =>
    cases hZ2 : isZeroExact (uintWidth (intTwin i)) a2 with
    | true =>
      have hy0 := isZeroExact_eq hZ2 hy
      subst hy0
      exact signedOverflowAdd_false_of_zero_right (absVal_some_elim hx).1
    | false =>
      cases hO1 : (sintNonneg i a1 && sintNeg i a2) with
      | true =>
        have h1 := sintNonneg_sound (bool_and_true_left hO1) hx
        have h2 := sintNeg_sound (bool_and_true_right hO1) hy
        exact signedOverflowAdd_false_of_opp_sign (Or.inl ⟨h1, h2.1, h2.2⟩)
      | false =>
        cases hO2 : (sintNeg i a1 && sintNonneg i a2) with
        | true =>
          have h1 := sintNeg_sound (bool_and_true_left hO2) hx
          have h2 := sintNonneg_sound (bool_and_true_right hO2) hy
          exact signedOverflowAdd_false_of_opp_sign (Or.inr ⟨h1.1, h1.2, h2⟩)
        | false =>
          simp only [hZ1, hZ2, hO1, hO2, Bool.false_or] at h
          cases hU1 : a1.ubound? with
          | none => rw [hU1] at h; nomatch h
          | some hi1 =>
            cases hU2 : a2.ubound? with
            | none => rw [hU1, hU2] at h; nomatch h
            | some hi2 =>
              rw [hU1, hU2] at h
              have hSumLt : x + y < modPow2 (uintWidth (intTwin i)) / 2 :=
                Nat.lt_of_le_of_lt
                  (Nat.add_le_add (absVal_ubound?_sound hU1 hx)
                    (absVal_ubound?_sound hU2 hy))
                  (lt_of_blt_true h)
              exact signedOverflowAdd_false_of_nonneg_lt
                (Nat.lt_of_le_of_lt (Nat.le_add_right x y) hSumLt)
                (Nat.lt_of_le_of_lt (Nat.le_add_left y x) hSumLt) hSumLt

/-- Certifies `signedOverflowSub x y (uintBytes (intTwin i)) = false`. -/
def sintNoOverflowSub (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  isZeroExact (uintWidth (intTwin i)) a2 ||
    (sintNonneg i a1 && sintNonneg i a2) ||
    (sintNeg i a1 && sintNeg i a2)

theorem sintNoOverflowSub_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintNoOverflowSub i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowSub x y (uintBytes (intTwin i)) = false := by
  unfold sintNoOverflowSub at h
  cases hZ2 : isZeroExact (uintWidth (intTwin i)) a2 with
  | true =>
    have hy0 := isZeroExact_eq hZ2 hy
    subst hy0
    exact signedOverflowSub_false_of_zero_right (absVal_some_elim hx).1
  | false =>
    cases hNN : (sintNonneg i a1 && sintNonneg i a2) with
    | true =>
      exact signedOverflowSub_false_of_same_sign
        (Or.inl ⟨sintNonneg_sound (bool_and_true_left hNN) hx,
          sintNonneg_sound (bool_and_true_right hNN) hy⟩)
    | false =>
      simp only [hZ2, hNN, Bool.false_or] at h
      have h1 := sintNeg_sound (bool_and_true_left h) hx
      have h2 := sintNeg_sound (bool_and_true_right h) hy
      exact signedOverflowSub_false_of_same_sign
        (Or.inr ⟨h1.1, h1.2, h2.1, h2.2⟩)

/-- Certifies `signedOverflowMul x y (uintBytes (intTwin i)) = false`. -/
def sintNoOverflowMul (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  let w := uintWidth (intTwin i)
  isZeroExact w a1 || isZeroExact w a2 ||
    (sintNonneg i a1 && sintNonneg i a2 &&
      match a1.ubound?, a2.ubound? with
      | some hi1, some hi2 => Nat.blt (hi1 * hi2) (modPow2 w / 2)
      | _, _ => false)

theorem sintNoOverflowMul_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintNoOverflowMul i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowMul x y (uintBytes (intTwin i)) = false := by
  unfold sintNoOverflowMul at h
  cases hZ1 : isZeroExact (uintWidth (intTwin i)) a1 with
  | true =>
    have hx0 := isZeroExact_eq hZ1 hx
    subst hx0
    exact signedOverflowMul_false_of_zero_left (absVal_some_elim hy).1
  | false =>
    cases hZ2 : isZeroExact (uintWidth (intTwin i)) a2 with
    | true =>
      have hy0 := isZeroExact_eq hZ2 hy
      subst hy0
      exact signedOverflowMul_false_of_zero_right (absVal_some_elim hx).1
    | false =>
      simp only [hZ1, hZ2, Bool.false_or] at h
      have hNN := bool_and_true_left h
      have hProdB := bool_and_true_right h
      cases hU1 : a1.ubound? with
      | none => rw [hU1] at hProdB; nomatch hProdB
      | some hi1 =>
        cases hU2 : a2.ubound? with
        | none => rw [hU1, hU2] at hProdB; nomatch hProdB
        | some hi2 =>
          rw [hU1, hU2] at hProdB
          have hProdLt : x * y < modPow2 (uintWidth (intTwin i)) / 2 :=
            Nat.lt_of_le_of_lt
              (Nat.mul_le_mul (absVal_ubound?_sound hU1 hx)
                (absVal_ubound?_sound hU2 hy))
              (lt_of_blt_true hProdB)
          exact signedOverflowMul_false_of_nonneg_lt
            (sintNonneg_sound (bool_and_true_left hNN) hx)
            (sintNonneg_sound (bool_and_true_right hNN) hy) hProdLt

/-- Certifies `¬ (x = MIN ∧ y = -1)` for signed division / remainder. -/
def sintNotMinDivNegOne (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  let w := uintWidth (intTwin i)
  let m := modPow2 w
  sintNonneg i a1 || sintNonneg i a2 ||
    (match AbsVal.decideEq? w a1 (AbsVal.const w (m / 2)) with
     | some false => true
     | _ => false) ||
    (match AbsVal.decideEq? w a2 (AbsVal.const w (m - 1)) with
     | some false => true
     | _ => false)

theorem sintNotMinDivNegOne_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintNotMinDivNegOne i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    ¬ (x = modPow2 (uintWidth (intTwin i)) / 2 ∧
       y = modPow2 (uintWidth (intTwin i)) - 1) := by
  intro hBad
  unfold sintNotMinDivNegOne at h
  cases hN1 : sintNonneg i a1 with
  | true =>
    have hLt := sintNonneg_sound hN1 hx
    rw [hBad.1] at hLt
    exact Nat.lt_irrefl _ hLt
  | false =>
    cases hN2 : sintNonneg i a2 with
    | true =>
      have hLt := sintNonneg_sound hN2 hy
      have hGe := half_le_sub_one_uint (intTwin i)
      rw [hBad.2] at hLt
      exact Nat.not_le_of_gt hLt hGe
    | false =>
      simp only [hN1, hN2, Bool.false_or] at h
      have hCheck2 :
          (match AbsVal.decideEq? (uintWidth (intTwin i)) a2
              (AbsVal.const (uintWidth (intTwin i))
                (modPow2 (uintWidth (intTwin i)) - 1)) with
           | some false => true
           | _ => false) = true → False := by
        intro h2
        cases hE2 : AbsVal.decideEq? (uintWidth (intTwin i)) a2
            (AbsVal.const (uintWidth (intTwin i))
              (modPow2 (uintWidth (intTwin i)) - 1)) with
        | none => rw [hE2] at h2; nomatch h2
        | some b2 =>
          cases b2 with
          | true => rw [hE2] at h2; nomatch h2
          | false =>
            have hM1Lt : modPow2 (uintWidth (intTwin i)) - 1 <
                modPow2 (uintWidth (intTwin i)) :=
              Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one
            have hBeq := absVal_decideEq?_sound hE2 hy
              (absVal_const_denote_lt (uintWidth_valid (intTwin i)) hM1Lt)
            exact nat_ne_of_beq_false hBeq hBad.2
      cases hE1 : AbsVal.decideEq? (uintWidth (intTwin i)) a1
          (AbsVal.const (uintWidth (intTwin i))
            (modPow2 (uintWidth (intTwin i)) / 2)) with
      | some b1 =>
        cases b1 with
        | false =>
          have hHalfLt : modPow2 (uintWidth (intTwin i)) / 2 <
              modPow2 (uintWidth (intTwin i)) :=
            Nat.lt_of_le_of_lt (half_le_sub_one_uint (intTwin i))
              (Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one)
          have hBeq := absVal_decideEq?_sound hE1 hx
            (absVal_const_denote_lt (uintWidth_valid (intTwin i)) hHalfLt)
          exact nat_ne_of_beq_false hBeq hBad.1
        | true =>
          simp only [hE1, Bool.false_or] at h
          exact hCheck2 h
      | none =>
        simp only [hE1, Bool.false_or] at h
        exact hCheck2 h

/-! ### Biased signed checks (`ReducedProduct` signed domain) -/

/-- Certifies `signedOverflowAdd x y (uintBytes (intTwin i)) = false` either
by `ReducedProduct`'s biased interval check `AbsVal.noSignedOverflowAdd`
(which accepts sign-straddling operands such as `[-100, 100] + 10`) or by the
bit-pattern checks of `sintNoOverflowAdd` (exact zero operands). -/
def sintAddOk (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  AbsVal.noSignedOverflowAdd (uintWidth (intTwin i)) a1 a2 ||
    sintNoOverflowAdd i a1 a2

theorem sintAddOk_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintAddOk i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowAdd x y (uintBytes (intTwin i)) = false := by
  unfold sintAddOk at h
  cases hB : AbsVal.noSignedOverflowAdd (uintWidth (intTwin i)) a1 a2 with
  | true =>
    have hb := absVal_noSignedOverflowAdd_sound hB hx hy
    exact signedOverflowAdd_false_of_biased_bounds (absVal_some_elim hx).1
      (absVal_some_elim hy).1 hb.1 hb.2
  | false =>
    rw [hB, Bool.false_or] at h
    exact sintNoOverflowAdd_sound h hx hy

/-- Certifies `signedOverflowSub x y (uintBytes (intTwin i)) = false` either
by `AbsVal.noSignedOverflowSub` (accepting sign-straddling operands such as
`[-100, 100] - (-10)`) or by the bit-pattern checks of `sintNoOverflowSub`. -/
def sintSubOk (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  AbsVal.noSignedOverflowSub (uintWidth (intTwin i)) a1 a2 ||
    sintNoOverflowSub i a1 a2

theorem sintSubOk_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintSubOk i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowSub x y (uintBytes (intTwin i)) = false := by
  unfold sintSubOk at h
  cases hB : AbsVal.noSignedOverflowSub (uintWidth (intTwin i)) a1 a2 with
  | true =>
    have hb := absVal_noSignedOverflowSub_sound hB hx hy
    exact signedOverflowSub_false_of_biased_bounds (absVal_some_elim hx).1
      (absVal_some_elim hy).1 hb.1 hb.2
  | false =>
    rw [hB, Bool.false_or] at h
    exact sintNoOverflowSub_sound h hx hy

/-- Certifies that signed `div` / `rem` is UB-free (`y ≠ 0` and
`¬ (x = INT_MIN ∧ y = -1)`) either by `AbsVal.safeSignedDiv` (biased divisor
bounds) or by `nonzeroDivSafe` together with `sintNotMinDivNegOne`. -/
def sintDivRemOk (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  AbsVal.safeSignedDiv (uintWidth (intTwin i)) a1 a2 ||
    (nonzeroDivSafe (uintWidth (intTwin i)) a2 && sintNotMinDivNegOne i a1 a2)

theorem sintDivRemOk_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintDivRemOk i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    y ≠ 0 ∧ ¬ (x = modPow2 (uintWidth (intTwin i)) / 2 ∧
      y = modPow2 (uintWidth (intTwin i)) - 1) := by
  unfold sintDivRemOk at h
  cases hB : AbsVal.safeSignedDiv (uintWidth (intTwin i)) a1 a2 with
  | true => exact safeSignedDiv_sound_v2026 hB hx hy
  | false =>
    rw [hB, Bool.false_or] at h
    exact ⟨Nat.ne_of_gt (nonzeroDivSafe_sound (bool_and_true_left h) hy),
      sintNotMinDivNegOne_sound (bool_and_true_right h) hx hy⟩

/-- Maximum signed magnitude `|v|` over biased coordinates `[sLo, sHi]` at width `w`. -/
def signedBiasMaxMag (w sLo sHi : Nat) : Nat :=
  let H := halfModPow2 w
  let mLo := match Nat.blt sLo H with | true => H - sLo | false => sLo - H
  let mHi := match Nat.blt sHi H with | true => H - sHi | false => sHi - H
  Nat.max mLo mHi

private theorem signedBias_mag_le {w sLo sHi s : Nat}
    (hLo : sLo ≤ s) (hHi : s ≤ sHi) :
    (match Nat.blt s (halfModPow2 w) with
     | true => halfModPow2 w - s
     | false => s - halfModPow2 w) ≤ signedBiasMaxMag w sLo sHi := by
  unfold signedBiasMaxMag
  dsimp only
  cases hs : Nat.blt s (halfModPow2 w) with
  | true =>
    have hsLt : s < halfModPow2 w := lt_of_blt_true hs
    have hLoLt : sLo < halfModPow2 w := Nat.lt_of_le_of_lt hLo hsLt
    rw [blt_true_of_lt hLoLt]
    exact Nat.le_trans (Nat.sub_le_sub_left hLo _) (Nat.le_max_left _ _)
  | false =>
    have hGe : halfModPow2 w ≤ s := by
      cases Nat.lt_or_ge s (halfModPow2 w) with
      | inl h => rw [blt_true_of_lt h] at hs; nomatch hs
      | inr h => exact h
    have hHiGe : halfModPow2 w ≤ sHi := Nat.le_trans hGe hHi
    have hHiF : Nat.blt sHi (halfModPow2 w) = false := by
      cases h : Nat.blt sHi (halfModPow2 w) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true h) hHiGe)
    rw [hHiF]
    exact Nat.le_trans (Nat.sub_le_sub_right hHi _) (Nat.le_max_right _ _)

private theorem signed_mag_eq_biased_dist {u : UintTy} {x : Nat}
    (hx : x < modPow2 (uintWidth u)) :
    (match isSignedNegative x (uintBytes u) with
     | false => x
     | true => modPow2 (uintWidth u) - x) =
    (match Nat.blt (signedBias (uintWidth u) x) (halfModPow2 (uintWidth u)) with
     | true => halfModPow2 (uintWidth u) - signedBias (uintWidth u) x
     | false => signedBias (uintWidth u) x - halfModPow2 (uintWidth u)) := by
  have hw := uintWidth_valid u
  have hH : halfModPow2 (uintWidth u) = modPow2 (uintWidth u) / 2 :=
    halfModPow2_uintWidth_eq_half u
  cases hLt : Nat.blt x (halfModPow2 (uintWidth u)) with
  | true =>
    have hxLt : x < modPow2 (uintWidth u) / 2 := hH ▸ lt_of_blt_true hLt
    rw [isSignedNegative_of_lt_half hxLt, signedBias_of_lt_half hw (lt_of_blt_true hLt)]
    have hGeH : halfModPow2 (uintWidth u) ≤ x + halfModPow2 (uintWidth u) :=
      Nat.le_add_left _ _
    have hBltF : Nat.blt (x + halfModPow2 (uintWidth u)) (halfModPow2 (uintWidth u)) = false := by
      cases h : Nat.blt (x + halfModPow2 (uintWidth u)) (halfModPow2 (uintWidth u)) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true h) hGeH)
    rw [hBltF, Nat.add_sub_cancel]
  | false =>
    have hxGeH : halfModPow2 (uintWidth u) ≤ x := by
      cases Nat.lt_or_ge x (halfModPow2 (uintWidth u)) with
      | inl h => rw [blt_true_of_lt h] at hLt; nomatch hLt
      | inr h => exact h
    have hxGe : modPow2 (uintWidth u) / 2 ≤ x := hH ▸ hxGeH
    rw [isSignedNegative_of_ge_half hxGe hx, signedBias_of_ge_half hw hxGeH hx]
    have hSubLt : x - halfModPow2 (uintWidth u) < halfModPow2 (uintWidth u) := by
      have hM : modPow2 (uintWidth u) = halfModPow2 (uintWidth u) + halfModPow2 (uintWidth u) :=
        modPow2_eq_half_add_half hw
      exact nat_sub_lt_of_lt_add hxGeH (hM ▸ hx)
    rw [blt_true_of_lt hSubLt, modPow2_eq_half_add_half hw]
    have hEqX : halfModPow2 (uintWidth u) + (x - halfModPow2 (uintWidth u)) = x :=
      Nat.add_sub_cancel' hxGeH
    calc halfModPow2 (uintWidth u) + halfModPow2 (uintWidth u) - x
        = halfModPow2 (uintWidth u) + halfModPow2 (uintWidth u) -
            (halfModPow2 (uintWidth u) + (x - halfModPow2 (uintWidth u))) :=
          congrArg (halfModPow2 (uintWidth u) + halfModPow2 (uintWidth u) - ·) hEqX.symm
      _ = halfModPow2 (uintWidth u) - (x - halfModPow2 (uintWidth u)) :=
          Nat.add_sub_add_left _ _ _

/-- Biased signed interval check certifying `signedOverflowMul = false`:
accepts any bounded signed intervals `[sLo1, sHi1]` and `[sLo2, sHi2]` whose
maximum magnitude product is `< 2^(w-1)` (or `≤ 2^(w-1)` when the two intervals
have strictly opposite signs, permitting exact `INT_MIN` such as
`[-64, -1] * [1, 2]`). -/
def sintNoOverflowMulBiased (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  let w := uintWidth (intTwin i)
  match a1.signedBounds? w, a2.signedBounds? w with
  | some (sLo1, sHi1), some (sLo2, sHi2) =>
    let H := halfModPow2 w
    let prod := signedBiasMaxMag w sLo1 sHi1 * signedBiasMaxMag w sLo2 sHi2
    Nat.blt prod H ||
      (Nat.ble prod H &&
        ((Nat.blt sHi1 H && Nat.ble H sLo2) ||
         (Nat.ble H sLo1 && Nat.blt sHi2 H)))
  | _, _ => false

private theorem isSignedNegative_of_signedBias_lt {u : UintTy} {z : Nat}
    (hzLt : z < modPow2 (uintWidth u))
    (hSbLt : signedBias (uintWidth u) z < halfModPow2 (uintWidth u)) :
    isSignedNegative z (uintBytes u) = true := by
  have hw := uintWidth_valid u
  have hH := halfModPow2_uintWidth_eq_half u
  cases Nat.lt_or_ge z (halfModPow2 (uintWidth u)) with
  | inr hGe => exact isSignedNegative_of_ge_half (hH ▸ hGe) hzLt
  | inl hLt =>
    rw [signedBias_of_lt_half hw hLt] at hSbLt
    exact False.elim (Nat.not_le_of_gt hSbLt (Nat.le_add_left _ _))

private theorem isSignedNegative_of_signedBias_ge {u : UintTy} {z : Nat}
    (hzLt : z < modPow2 (uintWidth u))
    (hSbGe : halfModPow2 (uintWidth u) ≤ signedBias (uintWidth u) z) :
    isSignedNegative z (uintBytes u) = false := by
  have hw := uintWidth_valid u
  have hH := halfModPow2_uintWidth_eq_half u
  cases Nat.lt_or_ge z (halfModPow2 (uintWidth u)) with
  | inl hLt => exact isSignedNegative_of_lt_half (hH ▸ hLt)
  | inr hGe =>
    rw [signedBias_of_ge_half hw hGe hzLt] at hSbGe
    have hSubLt := nat_sub_lt_of_lt_add hGe ((modPow2_eq_half_add_half hw) ▸ hzLt)
    exact False.elim (Nat.not_le_of_gt hSubLt hSbGe)

private theorem signedOverflowMul_false_of_mag_lt {u : UintTy} {x y : Nat}
    (hxLt : x < modPow2 (uintWidth u)) (hyLt : y < modPow2 (uintWidth u))
    (hLt : (match isSignedNegative x (uintBytes u) with
              | false => x | true => modPow2 (uintWidth u) - x) *
            (match isSignedNegative y (uintBytes u) with
              | false => y | true => modPow2 (uintWidth u) - y) <
            halfModPow2 (uintWidth u)) :
    signedOverflowMul x y (uintBytes u) = false := by
  unfold signedOverflowMul
  rw [uintBytes_beq_zero]; dsimp only
  have hHDiv : Nat.div (modPow2 (uintWidth u)) 2 = halfModPow2 (uintWidth u) :=
    (halfModPow2_uintWidth_eq_half u).symm
  rw [wrapScalarBits_of_lt_uint hxLt, wrapScalarBits_of_lt_uint hyLt,
    scalarModulus_uintBytes, hHDiv]
  cases hN1 : isSignedNegative x (uintBytes u) <;>
    cases hN2 : isSignedNegative y (uintBytes u) <;>
    (rw [hN1, hN2] at hLt; dsimp only at hLt ⊢)
  · cases Nat.beq (x * y) 0 with
    | true => rfl
    | false =>
      cases hb : Nat.ble (halfModPow2 (uintWidth u)) (x * y) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true hb))
  · cases Nat.beq (x * (modPow2 (uintWidth u) - y)) 0 with
    | true => rfl
    | false =>
      exact congrArg Bool.not (Nat.ble_eq_true_of_le (Nat.le_of_lt hLt))
  · cases Nat.beq ((modPow2 (uintWidth u) - x) * y) 0 with
    | true => rfl
    | false =>
      exact congrArg Bool.not (Nat.ble_eq_true_of_le (Nat.le_of_lt hLt))
  · cases Nat.beq ((modPow2 (uintWidth u) - x) * (modPow2 (uintWidth u) - y)) 0 with
    | true => rfl
    | false =>
      cases hb : Nat.ble (halfModPow2 (uintWidth u))
          ((modPow2 (uintWidth u) - x) * (modPow2 (uintWidth u) - y)) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true hb))

private theorem signedOverflowMul_false_of_opp_mag_le {u : UintTy} {x y : Nat}
    (hxLt : x < modPow2 (uintWidth u)) (hyLt : y < modPow2 (uintWidth u))
    (hOpp : (isSignedNegative x (uintBytes u) = true ∧
              isSignedNegative y (uintBytes u) = false) ∨
            (isSignedNegative x (uintBytes u) = false ∧
              isSignedNegative y (uintBytes u) = true))
    (hLe : (match isSignedNegative x (uintBytes u) with
              | false => x | true => modPow2 (uintWidth u) - x) *
            (match isSignedNegative y (uintBytes u) with
              | false => y | true => modPow2 (uintWidth u) - y) ≤
            halfModPow2 (uintWidth u)) :
    signedOverflowMul x y (uintBytes u) = false := by
  unfold signedOverflowMul
  rw [uintBytes_beq_zero]; dsimp only
  have hHDiv : Nat.div (modPow2 (uintWidth u)) 2 = halfModPow2 (uintWidth u) :=
    (halfModPow2_uintWidth_eq_half u).symm
  rw [wrapScalarBits_of_lt_uint hxLt, wrapScalarBits_of_lt_uint hyLt,
    scalarModulus_uintBytes, hHDiv]
  cases hOpp with
  | inl h =>
    rw [h.1, h.2] at hLe ⊢; dsimp only at hLe ⊢
    cases Nat.beq ((modPow2 (uintWidth u) - x) * y) 0 with
    | true => rfl
    | false => exact congrArg Bool.not (Nat.ble_eq_true_of_le hLe)
  | inr h =>
    rw [h.1, h.2] at hLe ⊢; dsimp only at hLe ⊢
    cases Nat.beq (x * (modPow2 (uintWidth u) - y)) 0 with
    | true => rfl
    | false => exact congrArg Bool.not (Nat.ble_eq_true_of_le hLe)

theorem sintNoOverflowMulBiased_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintNoOverflowMulBiased i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowMul x y (uintBytes (intTwin i)) = false := by
  let u := intTwin i
  let w := uintWidth u
  let H := halfModPow2 w
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  unfold sintNoOverflowMulBiased at h
  dsimp only at h
  cases hB1 : a1.signedBounds? w with
  | none => rw [hB1] at h; nomatch h
  | some p1 =>
    cases p1 with | mk sLo1 sHi1 =>
    cases hB2 : a2.signedBounds? w with
    | none => rw [hB1, hB2] at h; nomatch h
    | some p2 =>
      cases p2 with | mk sLo2 sHi2 =>
      rw [hB1, hB2] at h
      dsimp only at h
      have h1 := absVal_signedBounds?_sound hB1 hx
      have h2 := absVal_signedBounds?_sound hB2 hy
      have hMagA : (match isSignedNegative x (uintBytes u) with
          | false => x | true => modPow2 w - x) ≤ signedBiasMaxMag w sLo1 sHi1 := by
        rw [signed_mag_eq_biased_dist hxLt]
        exact signedBias_mag_le h1.2.1 h1.2.2.1
      have hMagB : (match isSignedNegative y (uintBytes u) with
          | false => y | true => modPow2 w - y) ≤ signedBiasMaxMag w sLo2 sHi2 := by
        rw [signed_mag_eq_biased_dist hyLt]
        exact signedBias_mag_le h2.2.1 h2.2.2.1
      have hProdLe := Nat.mul_le_mul hMagA hMagB
      cases hStrict : Nat.blt (signedBiasMaxMag w sLo1 sHi1 * signedBiasMaxMag w sLo2 sHi2) H with
      | true =>
        exact signedOverflowMul_false_of_mag_lt hxLt hyLt
          (Nat.lt_of_le_of_lt hProdLe (lt_of_blt_true hStrict))
      | false =>
        rw [hStrict, Bool.false_or] at h
        have hLeH := Nat.le_trans hProdLe (Nat.le_of_ble_eq_true (bool_and_true_left h))
        have hOpp := bool_and_true_right h
        cases hO1 : (Nat.blt sHi1 H && Nat.ble H sLo2) with
        | true =>
          exact signedOverflowMul_false_of_opp_mag_le hxLt hyLt
            (Or.inl ⟨isSignedNegative_of_signedBias_lt hxLt
                (Nat.lt_of_le_of_lt h1.2.2.1 (lt_of_blt_true (bool_and_true_left hO1))),
              isSignedNegative_of_signedBias_ge hyLt
                (Nat.le_trans (Nat.le_of_ble_eq_true (bool_and_true_right hO1)) h2.2.1)⟩)
            hLeH
        | false =>
          rw [hO1, Bool.false_or] at hOpp
          exact signedOverflowMul_false_of_opp_mag_le hxLt hyLt
            (Or.inr ⟨isSignedNegative_of_signedBias_ge hxLt
                (Nat.le_trans (Nat.le_of_ble_eq_true (bool_and_true_left hOpp)) h1.2.1),
              isSignedNegative_of_signedBias_lt hyLt
                (Nat.lt_of_le_of_lt h2.2.2.1 (lt_of_blt_true (bool_and_true_right hOpp)))⟩)
            hLeH

/-- Certifies `signedOverflowMul x y (uintBytes (intTwin i)) = false` either
by running the trusted overflow test on two exact operands (so constant
products of either sign, such as `-2 * 3` or `-64 * 2`, are decided exactly),
by the biased interval magnitude check `sintNoOverflowMulBiased` (handling
negative and sign-straddling intervals such as `[-10, 10] * 2` and
`[-64, -1] * [1, 2]`), or by `sintNoOverflowMul` (a zero operand, or
non-negative operands with a small product). -/
def sintMulOk (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  (match a1.exactVal? (uintWidth (intTwin i)),
      a2.exactVal? (uintWidth (intTwin i)) with
    | some c1, some c2 => !(signedOverflowMul c1 c2 (uintBytes (intTwin i)))
    | _, _ => false) ||
    sintNoOverflowMulBiased i a1 a2 ||
    sintNoOverflowMul i a1 a2

theorem sintMulOk_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintMulOk i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    signedOverflowMul x y (uintBytes (intTwin i)) = false := by
  have hTail : (sintNoOverflowMulBiased i a1 a2 || sintNoOverflowMul i a1 a2) = true →
      signedOverflowMul x y (uintBytes (intTwin i)) = false := by
    intro ht
    cases hB : sintNoOverflowMulBiased i a1 a2 with
    | true => exact sintNoOverflowMulBiased_sound hB hx hy
    | false => rw [hB, Bool.false_or] at ht; exact sintNoOverflowMul_sound ht hx hy
  unfold sintMulOk at h
  cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
  | none =>
    rw [hE1] at h
    exact hTail h
  | some c1 =>
    cases hE2 : a2.exactVal? (uintWidth (intTwin i)) with
    | none =>
      rw [hE1, hE2] at h
      exact hTail h
    | some c2 =>
      rw [hE1, hE2] at h
      have h1 := exactVal?_eq hE1 hx
      have h2 := exactVal?_eq hE2 hy
      subst h1
      subst h2
      cases hO : signedOverflowMul c1 c2 (uintBytes (intTwin i)) with
      | false => rfl
      | true =>
        have h' : (!(signedOverflowMul c1 c2 (uintBytes (intTwin i))) ||
            sintNoOverflowMulBiased i a1 a2 ||
            sintNoOverflowMul i a1 a2) = true := h
        rw [hO] at h'
        have h3 := hTail h'
        rw [hO] at h3
        exact h3

/-- Overflow flag of a checked signed operation: exactly `false` when the
operation is certified overflow-free, otherwise unknown. -/
def sintOverflowBoolAbs (noOverflow : Bool) : BoolAbs :=
  match noOverflow with
  | true => .exact false .none
  | false => .top .none

private def sintOverflowKnown? (w sz : Nat) (ovFn : Nat → Nat → Nat → Bool)
    (ok : Bool) (a1 a2 : AbsVal) : Option Bool :=
  match ok with
  | true => some false
  | false =>
    match a1.exactVal? w with
    | some c1 =>
      match a2.exactVal? w with
      | some c2 => some (ovFn c1 c2 sz)
      | none => none
    | none => none

private theorem sintOverflowKnown?_sound {w sz x y : Nat}
    {ovFn : Nat → Nat → Nat → Bool} {ok r : Bool} {a1 a2 : AbsVal}
    (hr : sintOverflowKnown? w sz ovFn ok a1 a2 = some r)
    (hOk : ok = true → ovFn x y sz = false)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    ovFn x y sz = r := by
  unfold sintOverflowKnown? at hr
  cases ok with
  | true => cases hr; exact hOk rfl
  | false =>
    dsimp only at hr
    cases hE1 : a1.exactVal? w with
    | none => rw [hE1] at hr; nomatch hr
    | some c1 =>
      rw [hE1] at hr; dsimp only at hr
      cases hE2 : a2.exactVal? w with
      | none => rw [hE2] at hr; nomatch hr
      | some c2 =>
        rw [hE2] at hr; cases hr
        have h1 := exactVal?_eq hE1 hx; have h2 := exactVal?_eq hE2 hy
        subst h1; subst h2; rfl

private def sintAddOverflowGuardOne (i : IntTy) (src : Option Nat)
    (aOther : AbsVal) : RelGuard :=
  match src with
  | none => .none
  | some r =>
    let w := uintWidth (intTwin i)
    match aOther.exactVal? w with
    | none => .none
    | some c =>
      match Nat.beq c 0 with
      | true => .none
      | false =>
        let H := halfModPow2 w
        match Nat.blt c H with
        | true => .sgtConst r i (H - 1 - c)
        | false => .sleConst r i (H + (modPow2 w - c) - 1)

/-- Overflow boolean and optional `.sgtConst`/`.sleConst` guard for signed
`addWithOverflow` (folds exact constants and synthesizes signed threshold
guards on constant-operand additions). -/
def sintAddOverflowBoolAbs (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : BoolAbs :=
  mkBoolAbs
    (sintOverflowKnown? (uintWidth (intTwin i)) (uintBytes (intTwin i))
      signedOverflowAdd (sintAddOk i a1 a2) a1 a2)
    (match sintAddOverflowGuardOne i srcL a2 with
     | .none => sintAddOverflowGuardOne i srcR a1
     | g => g)

theorem sintAddOverflowBoolAbs_isInit (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (sintAddOverflowBoolAbs i srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

private theorem sintAddOverflowGuardOne_sound {i : IntTy} {src : Option Nat}
    {aOther : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hxLt : x < modPow2 (uintWidth (intTwin i)))
    (hy : aOther.denote (uintWidth (intTwin i)) (some y))
    (hS : ∀ r, src = some r → localUintNat? locals r (intTwin i) = some x) :
    (sintAddOverflowGuardOne i src aOther).denote locals
      (signedOverflowAdd x y (uintBytes (intTwin i))) := by
  unfold sintAddOverflowGuardOne
  cases src with
  | none => exact True.intro
  | some r =>
    dsimp only
    cases hE : aOther.exactVal? (uintWidth (intTwin i)) with
    | none => exact True.intro
    | some c =>
      dsimp only
      have hcEq : c = y := exactVal?_eq hE hy
      subst hcEq
      cases hZ : Nat.beq c 0 with
      | true => exact True.intro
      | false =>
        dsimp only
        have hcPos : 0 < c := Nat.pos_of_ne_zero (nat_ne_of_beq_false hZ)
        cases hH : Nat.blt c (halfModPow2 (uintWidth (intTwin i))) with
        | true =>
          intro x' hx'
          rw [hS r rfl] at hx'; cases hx'
          exact signedOverflowAdd_iff_sgt hxLt hcPos (lt_of_blt_true hH)
        | false =>
          have hcGe : halfModPow2 (uintWidth (intTwin i)) ≤ c :=
            Nat.le_of_not_lt (fun hLt => by rw [blt_true_of_lt hLt] at hH; nomatch hH)
          intro x' hx'
          rw [hS r rfl] at hx'; cases hx'
          exact signedOverflowAdd_iff_sle hxLt hcGe (absVal_some_elim hy).1

theorem sintAddOverflowBoolAbs_sound {i : IntTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    (sintAddOverflowBoolAbs i srcL srcR a1 a2).denoteBool locals
      (signedOverflowAdd x y (uintBytes (intTwin i))) := by
  apply mkBoolAbs_sound
    (fun _ hr => sintOverflowKnown?_sound hr (fun h => sintAddOk_sound h hx hy) hx hy)
  have hGL := sintAddOverflowGuardOne_sound (absVal_some_elim hx).1 hy hL
  have hGR : (sintAddOverflowGuardOne i srcR a1).denote locals
      (signedOverflowAdd x y (uintBytes (intTwin i))) := by
    rw [signedOverflowAdd_comm]
    exact sintAddOverflowGuardOne_sound (absVal_some_elim hy).1 hx hR
  cases hG : sintAddOverflowGuardOne i srcL a2 with
  | none => exact hGR
  | _ => rw [hG] at hGL; exact hGL

private def sintSubOverflowGuardL (i : IntTy) (srcL : Option Nat)
    (a2 : AbsVal) : RelGuard :=
  match srcL with
  | none => .none
  | some r =>
    let w := uintWidth (intTwin i)
    match a2.exactVal? w with
    | none => .none
    | some c =>
      match Nat.beq c 0 with
      | true => .none
      | false =>
        let H := halfModPow2 w
        match Nat.blt c H with
        | true => .sleConst r i (H + c - 1)
        | false =>
          match Nat.beq c H with
          | true => .sgtConst r i (modPow2 w - 1)
          | false => .sgtConst r i (c - H - 1)

private def sintSubOverflowGuardR (i : IntTy) (srcR : Option Nat)
    (a1 : AbsVal) : RelGuard :=
  match srcR with
  | none => .none
  | some r =>
    let w := uintWidth (intTwin i)
    match a1.exactVal? w with
    | none => .none
    | some c =>
      let H := halfModPow2 w
      match Nat.blt c H with
      | true => .sleConst r i (H + c)
      | false => .sgtConst r i (c - H)

/-- Overflow boolean and optional `.sleConst`/`.sgtConst` guard for signed
`subWithOverflow` (folds exact constants and synthesizes signed threshold
guards on both `x - c` and `c - y`, including `0 - y`). -/
def sintSubOverflowBoolAbs (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : BoolAbs :=
  mkBoolAbs
    (sintOverflowKnown? (uintWidth (intTwin i)) (uintBytes (intTwin i))
      signedOverflowSub (sintSubOk i a1 a2) a1 a2)
    (match sintSubOverflowGuardL i srcL a2 with
     | .none => sintSubOverflowGuardR i srcR a1
     | g => g)

theorem sintSubOverflowBoolAbs_isInit (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (sintSubOverflowBoolAbs i srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

private theorem sintSubOverflowGuardL_sound {i : IntTy} {srcL : Option Nat}
    {a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hxLt : x < modPow2 (uintWidth (intTwin i)))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x) :
    (sintSubOverflowGuardL i srcL a2).denote locals
      (signedOverflowSub x y (uintBytes (intTwin i))) := by
  unfold sintSubOverflowGuardL
  cases srcL with
  | none => exact True.intro
  | some r =>
    dsimp only
    cases hE2 : a2.exactVal? (uintWidth (intTwin i)) with
    | none => exact True.intro
    | some c =>
      dsimp only
      have hcEq : c = y := exactVal?_eq hE2 hy
      subst hcEq
      cases hZ : Nat.beq c 0 with
      | true => exact True.intro
      | false =>
        dsimp only
        have hcPos : 0 < c := Nat.pos_of_ne_zero (nat_ne_of_beq_false hZ)
        cases hH : Nat.blt c (halfModPow2 (uintWidth (intTwin i))) with
        | true =>
          intro x' hx'
          rw [hL r rfl] at hx'; cases hx'
          exact signedOverflowSub_constR_pos_iff_sle hxLt hcPos (lt_of_blt_true hH)
        | false =>
          dsimp only
          have hcGe : halfModPow2 (uintWidth (intTwin i)) ≤ c :=
            Nat.le_of_not_lt (fun hLt => by rw [blt_true_of_lt hLt] at hH; nomatch hH)
          cases hEqH : Nat.beq c (halfModPow2 (uintWidth (intTwin i))) with
          | true =>
            have hCH := Nat.eq_of_beq_eq_true hEqH
            subst hCH
            intro x' hx'
            rw [hL r rfl] at hx'; cases hx'
            exact signedOverflowSub_constR_min_iff_sgt hxLt
          | false =>
            have hcGt : halfModPow2 (uintWidth (intTwin i)) < c :=
              Nat.lt_of_le_of_ne hcGe (fun hE => nat_ne_of_beq_false hEqH hE.symm)
            intro x' hx'
            rw [hL r rfl] at hx'; cases hx'
            exact signedOverflowSub_constR_neg_iff_sgt hxLt hcGt (absVal_some_elim hy).1

private theorem sintSubOverflowGuardR_sound {i : IntTy} {srcR : Option Nat}
    {a1 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hyLt : y < modPow2 (uintWidth (intTwin i)))
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    (sintSubOverflowGuardR i srcR a1).denote locals
      (signedOverflowSub x y (uintBytes (intTwin i))) := by
  unfold sintSubOverflowGuardR
  cases srcR with
  | none => exact True.intro
  | some r =>
    dsimp only
    cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
    | none => exact True.intro
    | some c =>
      dsimp only
      have hcEq : c = x := exactVal?_eq hE1 hx
      subst hcEq
      cases hH : Nat.blt c (halfModPow2 (uintWidth (intTwin i))) with
      | true =>
        intro y' hy'
        rw [hR r rfl] at hy'; cases hy'
        exact signedOverflowSub_constL_nonneg_iff_sle (lt_of_blt_true hH) hyLt
      | false =>
        have hcGe : halfModPow2 (uintWidth (intTwin i)) ≤ c :=
          Nat.le_of_not_lt (fun hLt => by rw [blt_true_of_lt hLt] at hH; nomatch hH)
        intro y' hy'
        rw [hR r rfl] at hy'; cases hy'
        exact signedOverflowSub_constL_neg_iff_sgt hcGe (absVal_some_elim hx).1 hyLt

theorem sintSubOverflowBoolAbs_sound {i : IntTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    (sintSubOverflowBoolAbs i srcL srcR a1 a2).denoteBool locals
      (signedOverflowSub x y (uintBytes (intTwin i))) := by
  apply mkBoolAbs_sound
    (fun _ hr => sintOverflowKnown?_sound hr (fun h => sintSubOk_sound h hx hy) hx hy)
  have hGL := sintSubOverflowGuardL_sound (absVal_some_elim hx).1 hy hL
  have hGR := sintSubOverflowGuardR_sound hx (absVal_some_elim hy).1 hR
  cases hG : sintSubOverflowGuardL i srcL a2 with
  | none => exact hGR
  | _ => rw [hG] at hGL; exact hGL

/-- Overflow boolean for signed `mulWithOverflow` (folds exact constants for
both `true` and `false` outcomes, and certifies `false` via `sintMulOk`). -/
def sintMulOverflowBoolAbs (i : IntTy) (a1 a2 : AbsVal) : BoolAbs :=
  mkBoolAbs
    (sintOverflowKnown? (uintWidth (intTwin i)) (uintBytes (intTwin i))
      signedOverflowMul (sintMulOk i a1 a2) a1 a2)
    .none

theorem sintMulOverflowBoolAbs_isInit (i : IntTy) (a1 a2 : AbsVal) :
    (sintMulOverflowBoolAbs i a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

theorem sintMulOverflowBoolAbs_sound {i : IntTy} {a1 a2 : AbsVal}
    {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    (sintMulOverflowBoolAbs i a1 a2).denoteBool locals
      (signedOverflowMul x y (uintBytes (intTwin i))) :=
  mkBoolAbs_sound (g := .none)
    (fun _ hr => sintOverflowKnown?_sound hr (fun h => sintMulOk_sound h hx hy) hx hy)
    True.intro

/-! ### Biased signed comparisons and `RelGuard` synthesis -/

/-- `op` is one of the six comparison operators. -/
def binOpIsCmp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

theorem nat_blt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hB : Nat.blt a b with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true hB) h)

/-- Comparing a value with itself gives `decideCmpSame`. -/
theorem cmpResult_self {op : BinOp} (hop : binOpIsCmp op = true) (z : Nat) :
    cmpResult op z z = decideCmpSame op := by
  cases op with
  | eq => exact nat_beq_refl z
  | ne => exact congrArg Bool.not (nat_beq_refl z)
  | lt => exact nat_blt_false_of_le (Nat.le_refl z)
  | le => exact Nat.ble_eq_true_of_le (Nat.le_refl z)
  | gt => exact nat_blt_false_of_le (Nat.le_refl z)
  | ge => exact Nat.ble_eq_true_of_le (Nat.le_refl z)
  | _ => nomatch hop

theorem signedBias_beq_true_iff {w x y : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hy : y < modPow2 w) :
    Nat.beq (signedBias w x) (signedBias w y) = true ↔ x = y := by
  rw [signedBias_beq hw hx hy]
  exact nat_beq_true_iff

theorem signedBias_not_beq_true_iff {w x y : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hy : y < modPow2 w) :
    (!(Nat.beq (signedBias w x) (signedBias w y))) = true ↔ x ≠ y := by
  rw [signedBias_beq hw hx hy]
  exact nat_not_beq_true_iff

/-- Every signed comparison at `isSigned = true` evaluates to the unsigned
comparison `cmpResult` of the biased coordinates of its operands. -/
theorem evalScalarBinOp_sint_cmp {u : UintTy} {op : BinOp} {x y : Nat}
    (locals : List LocalSlot) (mem : Memory) (hop : binOpIsCmp op = true)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar (cmpResult op (signedBias (uintWidth u) x)
        (signedBias (uintWidth u) y)))) locals mem := by
  cases op with
  | eq =>
    rw [evalScalarBinOp_signAgnostic locals mem (op := .eq) rfl,
      evalScalarBinOp_uint_eq,
      show cmpResult .eq (signedBias (uintWidth u) x)
        (signedBias (uintWidth u) y) = Nat.beq x y from
        signedBias_beq (uintWidth_valid u) hx hy]
  | ne =>
    rw [evalScalarBinOp_signAgnostic locals mem (op := .ne) rfl,
      evalScalarBinOp_uint_ne,
      show cmpResult .ne (signedBias (uintWidth u) x)
        (signedBias (uintWidth u) y) = !(Nat.beq x y) from
        congrArg Bool.not (signedBias_beq (uintWidth_valid u) hx hy)]
  | lt => exact evalScalarBinOp_sint_lt locals mem hx hy
  | le => exact evalScalarBinOp_sint_le locals mem hx hy
  | gt => exact evalScalarBinOp_sint_gt locals mem hx hy
  | ge => exact evalScalarBinOp_sint_ge locals mem hx hy
  | _ => nomatch hop

/-- `a` is exactly `INT_MIN` (biased coordinate `0`). -/
def isSignedMinExact (w : Nat) (a : AbsVal) : Bool :=
  match a.exactVal? w with
  | some v => Nat.beq (signedBias w v) 0
  | none => false

/-- `a` is exactly `INT_MAX` (biased coordinate `2^w - 1`). -/
def isSignedMaxExact (w : Nat) (a : AbsVal) : Bool :=
  match a.exactVal? w with
  | some v => Nat.beq (signedBias w v) (modPow2 w - 1)
  | none => false

theorem isSignedMinExact_sound {w x : Nat} {a : AbsVal}
    (h : isSignedMinExact w a = true) (ha : a.denote w (some x)) :
    signedBias w x = 0 := by
  unfold isSignedMinExact at h
  cases hE : a.exactVal? w with
  | none => rw [hE] at h; nomatch h
  | some v =>
    rw [hE] at h
    rw [← exactVal?_eq hE ha]
    exact Nat.eq_of_beq_eq_true h

theorem isSignedMaxExact_sound {w x : Nat} {a : AbsVal}
    (h : isSignedMaxExact w a = true) (ha : a.denote w (some x)) :
    signedBias w x = modPow2 w - 1 := by
  unfold isSignedMaxExact at h
  cases hE : a.exactVal? w with
  | none => rw [hE] at h; nomatch h
  | some v =>
    rw [hE] at h
    rw [← exactVal?_eq hE ha]
    exact Nat.eq_of_beq_eq_true h

/-- `AbsVal.decideSlt?` extended with extreme-constant folds: nothing is
signed-below `INT_MIN`, and `INT_MAX` is signed-below nothing. -/
def decideSltAbs (w : Nat) (a b : AbsVal) : Option Bool :=
  match AbsVal.decideSlt? w a b with
  | some r => some r
  | none =>
    match isSignedMinExact w b || isSignedMaxExact w a with
    | true => some false
    | false => none

theorem decideSltAbs_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (h : decideSltAbs w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.blt (signedBias w x) (signedBias w y) = r := by
  unfold decideSltAbs at h
  cases hD : AbsVal.decideSlt? w a b with
  | some r' =>
    rw [hD] at h
    injection h with h
    subst h
    exact absVal_decideSlt?_sound hD ha hb
  | none =>
    rw [hD] at h
    dsimp only at h
    cases hMin : isSignedMinExact w b with
    | true =>
      rw [hMin, Bool.true_or] at h
      injection h with h
      subst h
      rw [isSignedMinExact_sound hMin hb]
      exact nat_blt_false_of_le (Nat.zero_le _)
    | false =>
      rw [hMin, Bool.false_or] at h
      cases hMax : isSignedMaxExact w a with
      | false => rw [hMax] at h; nomatch h
      | true =>
        rw [hMax] at h
        injection h with h
        subst h
        rw [isSignedMaxExact_sound hMax ha]
        exact nat_blt_false_of_le (Nat.le_sub_one_of_lt (signedBias_lt y))

/-- `AbsVal.decideSle?` extended with extreme-constant folds: `INT_MIN` is
signed-below-or-equal everything, and everything is `≤ INT_MAX`. -/
def decideSleAbs (w : Nat) (a b : AbsVal) : Option Bool :=
  match AbsVal.decideSle? w a b with
  | some r => some r
  | none =>
    match isSignedMinExact w a || isSignedMaxExact w b with
    | true => some true
    | false => none

theorem decideSleAbs_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (h : decideSleAbs w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.ble (signedBias w x) (signedBias w y) = r := by
  unfold decideSleAbs at h
  cases hD : AbsVal.decideSle? w a b with
  | some r' =>
    rw [hD] at h
    injection h with h
    subst h
    exact absVal_decideSle?_sound hD ha hb
  | none =>
    rw [hD] at h
    dsimp only at h
    cases hMin : isSignedMinExact w a with
    | true =>
      rw [hMin, Bool.true_or] at h
      injection h with h
      subst h
      rw [isSignedMinExact_sound hMin ha]
      exact Nat.ble_eq_true_of_le (Nat.zero_le _)
    | false =>
      rw [hMin, Bool.false_or] at h
      cases hMax : isSignedMaxExact w b with
      | false => rw [hMax] at h; nomatch h
      | true =>
        rw [hMax] at h
        injection h with h
        subst h
        rw [isSignedMaxExact_sound hMax hb]
        exact Nat.ble_eq_true_of_le (Nat.le_sub_one_of_lt (signedBias_lt x))

/-- Static decision of the signed comparison `op` between `a1` and `a2`
through `AbsVal.decideEq?` / `AbsVal.decideSlt?` / `AbsVal.decideSle?` (plus
`INT_MIN` / `INT_MAX` folds). -/
def decideSignedCmpAbs (op : BinOp) (w : Nat) (a1 a2 : AbsVal) : Option Bool :=
  match binOpToCmp? op with
  | some .eq => AbsVal.decideEq? w a1 a2
  | some .ne =>
    match AbsVal.decideEq? w a1 a2 with
    | some r => some (!r)
    | none => none
  | some .lt => decideSltAbs w a1 a2
  | some .le => decideSleAbs w a1 a2
  | some .gt => decideSltAbs w a2 a1
  | some .ge => decideSleAbs w a2 a1
  | none => none

theorem decideSignedCmpAbs_sound {op : BinOp} {w x y : Nat} {a1 a2 : AbsVal}
    {r : Bool} (hw : validWidth w = true)
    (h : decideSignedCmpAbs op w a1 a2 = some r)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    cmpResult op (signedBias w x) (signedBias w y) = r := by
  have hBeq := signedBias_beq hw (absVal_some_elim hx).1 (absVal_some_elim hy).1
  unfold decideSignedCmpAbs at h
  unfold cmpResult
  cases hC : binOpToCmp? op with
  | none => rw [hC] at h; nomatch h
  | some cop =>
    rw [hC] at h
    cases cop with
    | eq => exact Eq.trans hBeq (absVal_decideEq?_sound h hx hy)
    | ne =>
      dsimp only at h
      cases hD : AbsVal.decideEq? w a1 a2 with
      | none => rw [hD] at h; nomatch h
      | some r' =>
        rw [hD] at h
        injection h with h
        subst h
        exact congrArg Bool.not (Eq.trans hBeq (absVal_decideEq?_sound hD hx hy))
    | lt => exact decideSltAbs_sound h hx hy
    | le => exact decideSleAbs_sound h hx hy
    | gt => exact decideSltAbs_sound h hy hx
    | ge => exact decideSleAbs_sound h hy hx

/-- Signed guard for `op(copy r, const v)` on a local of type `i`: `==` / `!=`
give `.seqConst` / `.sneConst`, `<=` / `>` give `.sleConst` / `.sgtConst` on
`v`, and `<` / `>=` use the signed predecessor of `v` (whose biased
coordinate is `signedBias v - 1`), with no guard when `v = INT_MIN` (the
comparison is then constant and folded by `decideSignedCmpAbs`). -/
def scmpGuardConstR (op : BinOp) (r : Nat) (i : IntTy) (v : Nat) : RelGuard :=
  match binOpToCmp? op with
  | some .eq => .seqConst r i v
  | some .ne => .sneConst r i v
  | some .le => .sleConst r i v
  | some .gt => .sgtConst r i v
  | some .lt =>
    match signedBias (uintWidth (intTwin i)) v with
    | 0 => .none
    | k + 1 => .sleConst r i (signedBias (uintWidth (intTwin i)) k)
  | some .ge =>
    match signedBias (uintWidth (intTwin i)) v with
    | 0 => .none
    | k + 1 => .sgtConst r i (signedBias (uintWidth (intTwin i)) k)
  | none => .none

/-- Signed guard for `op(const v, copy r)`. -/
def scmpGuardConstL (op : BinOp) (v : Nat) (r : Nat) (i : IntTy) : RelGuard :=
  scmpGuardConstR (flipCmpOp op) r i v

/-- Guard for a signed `op(copy l, copy r)`: equality and disequality of bit
patterns are sign-agnostic (`.ueqReg` / `.uneReg` at the twin width). -/
def scmpGuardRegs (op : BinOp) (l r : Nat) (i : IntTy) : RelGuard :=
  match binOpToCmp? op with
  | some .eq => .ueqReg l r (intTwin i)
  | some .ne => .uneReg l r (intTwin i)
  | _ => .none

theorem scmpGuardConstR_sound {op : BinOp} {locals : List LocalSlot} {r : Nat}
    {i : IntTy} {x y : Nat}
    (hx : localUintNat? locals r (intTwin i) = some x)
    (hxLt : x < modPow2 (uintWidth (intTwin i)))
    (hyLt : y < modPow2 (uintWidth (intTwin i))) :
    (scmpGuardConstR op r i y).denote locals
      (cmpResult op (signedBias (uintWidth (intTwin i)) x)
        (signedBias (uintWidth (intTwin i)) y)) := by
  have hw := uintWidth_valid (intTwin i)
  have hPred : ∀ k, signedBias (uintWidth (intTwin i)) y = k + 1 →
      k < modPow2 (uintWidth (intTwin i)) := by
    intro k hB
    have h1 := signedBias_lt (w := uintWidth (intTwin i)) y
    rw [hB] at h1
    exact Nat.lt_of_succ_lt h1
  unfold scmpGuardConstR cmpResult
  cases binOpToCmp? op with
  | none => exact True.intro
  | some cop =>
    cases cop with
    | eq =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact signedBias_beq_true_iff hw hxLt hyLt
    | ne =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact signedBias_not_beq_true_iff hw hxLt hyLt
    | le =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_ble_true_iff
    | gt =>
      intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
      exact nat_blt_true_iff
    | lt =>
      dsimp only
      cases hB : signedBias (uintWidth (intTwin i)) y with
      | zero => exact True.intro
      | succ k =>
        intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
        rw [signedBias_signedBias hw (hPred k hB)]
        exact Iff.trans nat_blt_true_iff Nat.lt_succ_iff
    | ge =>
      dsimp only
      cases hB : signedBias (uintWidth (intTwin i)) y with
      | zero => exact True.intro
      | succ k =>
        intro x' hx'; rw [hx] at hx'; injection hx' with hx'; subst hx'
        rw [signedBias_signedBias hw (hPred k hB)]
        exact nat_ble_true_iff

theorem scmpGuardConstL_sound {op : BinOp} {locals : List LocalSlot} {r : Nat}
    {i : IntTy} {x y : Nat}
    (hy : localUintNat? locals r (intTwin i) = some y)
    (hxLt : x < modPow2 (uintWidth (intTwin i)))
    (hyLt : y < modPow2 (uintWidth (intTwin i))) :
    (scmpGuardConstL op x r i).denote locals
      (cmpResult op (signedBias (uintWidth (intTwin i)) x)
        (signedBias (uintWidth (intTwin i)) y)) := by
  unfold scmpGuardConstL
  rw [← cmpResult_flip op]
  exact scmpGuardConstR_sound hy hyLt hxLt

theorem scmpGuardRegs_sound {op : BinOp} {locals : List LocalSlot} {l r : Nat}
    {i : IntTy} {x y : Nat}
    (hx : localUintNat? locals l (intTwin i) = some x)
    (hy : localUintNat? locals r (intTwin i) = some y)
    (hxLt : x < modPow2 (uintWidth (intTwin i)))
    (hyLt : y < modPow2 (uintWidth (intTwin i))) :
    (scmpGuardRegs op l r i).denote locals
      (cmpResult op (signedBias (uintWidth (intTwin i)) x)
        (signedBias (uintWidth (intTwin i)) y)) := by
  have hw := uintWidth_valid (intTwin i)
  unfold scmpGuardRegs cmpResult
  cases binOpToCmp? op with
  | none => exact True.intro
  | some cop =>
    cases cop with
    | eq =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact signedBias_beq_true_iff hw hxLt hyLt
    | ne =>
      intro x' y' hx' hy'; rw [hx] at hx'; rw [hy] at hy'
      injection hx' with hx'; injection hy' with hy'; subst hx'; subst hy'
      exact signedBias_not_beq_true_iff hw hxLt hyLt
    | lt | le | gt | ge => exact True.intro

/-- Synthesize a `RelGuard` for a signed comparison from the operands' source
locals and exactly-known values (constant-on-right, then constant-on-left,
then register-register equality). -/
def synthSignedCmpGuard (op : BinOp) (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match srcL, a2.exactVal? (uintWidth (intTwin i)) with
  | some r, some v => scmpGuardConstR op r i v
  | _, _ =>
    match srcR, a1.exactVal? (uintWidth (intTwin i)) with
    | some r, some v => scmpGuardConstL op v r i
    | _, _ =>
      match srcL, srcR with
      | some l, some r => scmpGuardRegs op l r i
      | _, _ => .none

theorem synthSignedCmpGuard_sound {op : BinOp} {i : IntTy}
    {srcL srcR : Option Nat} {a1 a2 : AbsVal} {locals : List LocalSlot}
    {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    (synthSignedCmpGuard op i srcL srcR a1 a2).denote locals
      (cmpResult op (signedBias (uintWidth (intTwin i)) x)
        (signedBias (uintWidth (intTwin i)) y)) := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  have hConstL : ∀ (r v : Nat), srcR = some r →
      a1.exactVal? (uintWidth (intTwin i)) = some v →
      (scmpGuardConstL op v r i).denote locals
        (cmpResult op (signedBias (uintWidth (intTwin i)) x)
          (signedBias (uintWidth (intTwin i)) y)) := by
    intro r v hr hE1
    have h1 := exactVal?_eq hE1 hx
    subst h1
    exact scmpGuardConstL_sound (hR r hr) hxLt hyLt
  unfold synthSignedCmpGuard
  cases srcL with
  | some l =>
    cases hE2 : a2.exactVal? (uintWidth (intTwin i)) with
    | some v =>
      have h2 := exactVal?_eq hE2 hy
      subst h2
      exact scmpGuardConstR_sound (hL l rfl) hxLt hyLt
    | none =>
      cases srcR with
      | none => exact True.intro
      | some r =>
        cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
        | some v => exact hConstL r v rfl hE1
        | none => exact scmpGuardRegs_sound (hL l rfl) (hR r rfl) hxLt hyLt
  | none =>
    cases srcR with
    | none =>
      cases a2.exactVal? (uintWidth (intTwin i)) <;> exact True.intro
    | some r =>
      cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
      | none =>
        cases a2.exactVal? (uintWidth (intTwin i)) <;> exact True.intro
      | some v =>
        cases a2.exactVal? (uintWidth (intTwin i)) <;> exact hConstL r v rfl hE1

/-- `g` carries no relational information. -/
def relGuardIsNone : RelGuard → Bool
  | .none => true
  | _ => false

/-- Both operands certainly have the same sign (both non-negative or both
negative), so signed and unsigned order coincide on them. -/
def sintSameSign (i : IntTy) (a1 a2 : AbsVal) : Bool :=
  (sintNonneg i a1 && sintNonneg i a2) || (sintNeg i a1 && sintNeg i a2)

theorem sintSameSign_sound {i : IntTy} {a1 a2 : AbsVal} {x y : Nat}
    (h : sintSameSign i a1 a2 = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    (x < modPow2 (uintWidth (intTwin i)) / 2 ∧
        y < modPow2 (uintWidth (intTwin i)) / 2) ∨
      (modPow2 (uintWidth (intTwin i)) / 2 ≤ x ∧
        modPow2 (uintWidth (intTwin i)) / 2 ≤ y) := by
  unfold sintSameSign at h
  cases hNN : (sintNonneg i a1 && sintNonneg i a2) with
  | true =>
    exact Or.inl ⟨sintNonneg_sound (bool_and_true_left hNN) hx,
      sintNonneg_sound (bool_and_true_right hNN) hy⟩
  | false =>
    rw [hNN, Bool.false_or] at h
    exact Or.inr ⟨(sintNeg_sound (bool_and_true_left h) hx).1,
      (sintNeg_sound (bool_and_true_right h) hy).1⟩

/-- On same-sign operands signed order is unsigned order: `cmpResult` of the
biased coordinates is `cmpResult` of the bit patterns. -/
theorem cmpResult_signedBias_same_sign {u : UintTy} (op : BinOp) {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u))
    (h : (x < modPow2 (uintWidth u) / 2 ∧ y < modPow2 (uintWidth u) / 2) ∨
      (modPow2 (uintWidth u) / 2 ≤ x ∧ modPow2 (uintWidth u) / 2 ≤ y)) :
    cmpResult op (signedBias (uintWidth u) x) (signedBias (uintWidth u) y) =
      cmpResult op x y := by
  have hLtXY : signedLt x y (uintBytes u) = !(Nat.ble y x) := by
    cases h with
    | inl h1 => exact signedLt_of_nonneg h1.1 h1.2
    | inr h2 => exact signedLt_of_neg h2.1 hx h2.2 hy
  have hLtYX : signedLt y x (uintBytes u) = !(Nat.ble x y) := by
    cases h with
    | inl h1 => exact signedLt_of_nonneg h1.2 h1.1
    | inr h2 => exact signedLt_of_neg h2.2 hy h2.1 hx
  have hBltXY : Nat.blt (signedBias (uintWidth u) x)
      (signedBias (uintWidth u) y) = Nat.blt x y := by
    rw [← signedLt_eq_blt_signedBias hx hy, hLtXY, nat_blt_eq_not_ble]
  have hBltYX : Nat.blt (signedBias (uintWidth u) y)
      (signedBias (uintWidth u) x) = Nat.blt y x := by
    rw [← signedLt_eq_blt_signedBias hy hx, hLtYX, nat_blt_eq_not_ble]
  have hBleXY : Nat.ble (signedBias (uintWidth u) x)
      (signedBias (uintWidth u) y) = Nat.ble x y := by
    rw [← signedLe_eq_ble_signedBias hx hy]
    simp only [signedLe]
    rw [hLtYX, Bool.not_not]
  have hBleYX : Nat.ble (signedBias (uintWidth u) y)
      (signedBias (uintWidth u) x) = Nat.ble y x := by
    rw [← signedLe_eq_ble_signedBias hy hx]
    simp only [signedLe]
    rw [hLtXY, Bool.not_not]
  have hBeq := signedBias_beq (uintWidth_valid u) hx hy
  unfold cmpResult
  cases binOpToCmp? op with
  | none => rfl
  | some cop =>
    cases cop with
    | eq => exact hBeq
    | ne => exact congrArg Bool.not hBeq
    | lt => exact hBltXY
    | le => exact hBleXY
    | gt => exact hBltYX
    | ge => exact hBleYX

/-- Guard recorded by a signed comparison: the signed synthesis
(`synthSignedCmpGuard`) when it yields a guard; otherwise, on operands of
certainly equal sign, the unsigned synthesis (`synthCmpGuard`, which also
covers register-register ordered comparisons). -/
def sintCmpGuard (op : BinOp) (i : IntTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match relGuardIsNone (synthSignedCmpGuard op i srcL srcR a1 a2) &&
      sintSameSign i a1 a2 with
  | true => synthCmpGuard op (intTwin i) srcL srcR a1 a2
  | false => synthSignedCmpGuard op i srcL srcR a1 a2

theorem sintCmpGuard_sound {op : BinOp} {i : IntTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    (sintCmpGuard op i srcL srcR a1 a2).denote locals
      (cmpResult op (signedBias (uintWidth (intTwin i)) x)
        (signedBias (uintWidth (intTwin i)) y)) := by
  unfold sintCmpGuard
  cases hC : (relGuardIsNone (synthSignedCmpGuard op i srcL srcR a1 a2) &&
      sintSameSign i a1 a2) with
  | false => exact synthSignedCmpGuard_sound hx hy hL hR
  | true =>
    dsimp only
    rw [cmpResult_signedBias_same_sign op (absVal_some_elim hx).1
      (absVal_some_elim hy).1 (sintSameSign_sound (bool_and_true_right hC) hx hy)]
    exact synthCmpGuard_sound hx hy hL hR

/-- Abstract signed comparison on operands of equal type `i`: self-comparison
folds, static decision in biased coordinates, and `RelGuard` synthesis. -/
def sintCmpAbs (op : BinOp) (i : IntTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  match sameLocalOpt srcL srcR with
  | true => some (.bool (.exact (decideCmpSame op) .none))
  | false =>
    some (.bool (mkBoolAbs
      (decideSignedCmpAbs op (uintWidth (intTwin i)) a1 a2)
      (sintCmpGuard op i srcL srcR a1 a2)))

theorem sintCmpAbs_sound {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory) (hop : binOpIsCmp op = true)
    (h : sintCmpAbs op i a1 srcL a2 srcR = some av)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩
        ⟨y, uintBytes (intTwin i)⟩ locals mem true = .ok v locals mem ∧
      av.denote locals v := by
  have hEv := evalScalarBinOp_sint_cmp (u := intTwin i) locals mem hop
    (absVal_some_elim hx).1 (absVal_some_elim hy).1
  unfold sintCmpAbs at h
  cases hSame : sameLocalOpt srcL srcR with
  | true =>
    rw [hSame] at h
    injection h with h
    subst h
    have hxy := sameLocalOpt_eq hSame hL hR
    subst hxy
    exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact _ .none)
      ⟨cmpResult_self hop _, True.intro⟩⟩
  | false =>
    rw [hSame] at h
    injection h with h
    subst h
    exact ⟨_, hEv, boolAbs_denote_of_bool (mkBoolAbs_sound
      (fun _ hr => decideSignedCmpAbs_sound (uintWidth_valid _) hr hx hy)
      (sintCmpGuard_sound hx hy hL hR))⟩

/-- Build the `BoolAbs` for a sign test (`wantNonneg = true` means `x ≥_s 0`,
i.e. `x ≤ 2^(w-1) - 1`; `wantNonneg = false` means `x <_s 0`, i.e.
`x > 2^(w-1) - 1`), attaching a `RelGuard` on `src` even when `a` is `top`. -/
def sintSignTestBool (i : IntTy) (a : AbsVal) (src : Option Nat)
    (wantNonneg : Bool) : BoolAbs :=
  let u := intTwin i
  let half1 := modPow2 (uintWidth u) / 2 - 1
  let g : RelGuard :=
    match src with
    | some r =>
      match wantNonneg with
      | true => .uleConst r u half1
      | false => .ugtConst r u half1
    | none => .none
  match sintNonneg i a with
  | true => .exact wantNonneg g
  | false =>
    match sintNeg i a with
    | true => .exact (!wantNonneg) g
    | false => .top g

theorem sintSignTestBool_sound {locals : List LocalSlot} {i : IntTy}
    {a : AbsVal} {src : Option Nat} {x : Nat} (wantNonneg : Bool)
    (hx : a.denote (uintWidth (intTwin i)) (some x))
    (hSrc : ∀ r, src = some r → localUintNat? locals r (intTwin i) = some x) :
    (sintSignTestBool i a src wantNonneg).denoteBool locals
      (match wantNonneg with
       | true => Nat.ble x (modPow2 (uintWidth (intTwin i)) / 2 - 1)
       | false => !(Nat.ble x (modPow2 (uintWidth (intTwin i)) / 2 - 1))) := by
  let half1 := modPow2 (uintWidth (intTwin i)) / 2 - 1
  let bRes :=
    match wantNonneg with
    | true => Nat.ble x half1
    | false => !(Nat.ble x half1)
  have hGuard :
      (match src with
       | some r =>
         match wantNonneg with
         | true => RelGuard.uleConst r (intTwin i) half1
         | false => RelGuard.ugtConst r (intTwin i) half1
       | none => RelGuard.none).denote locals bRes := by
    cases src with
    | none => exact True.intro
    | some r =>
      cases wantNonneg with
      | true =>
        intro x' hx'
        rw [hSrc r rfl] at hx'
        injection hx' with hxEq
        subst hxEq
        exact nat_ble_true_iff
      | false =>
        intro x' hx'
        rw [hSrc r rfl] at hx'
        injection hx' with hxEq
        subst hxEq
        dsimp only [bRes]
        exact ⟨fun hb =>
          Nat.lt_of_not_le (fun hle => by
            rw [Nat.ble_eq_true_of_le hle] at hb; nomatch hb),
          fun hlt => by
            cases hb : Nat.ble x half1 with
            | false => rfl
            | true =>
              exact False.elim (Nat.not_le_of_gt hlt (Nat.le_of_ble_eq_true hb))⟩
  unfold sintSignTestBool
  cases hNN : sintNonneg i a with
  | true =>
    have hBleT : Nat.ble x half1 = true :=
      Nat.ble_eq_true_of_le (Nat.le_sub_one_of_lt (sintNonneg_sound hNN hx))
    refine ⟨?_, hGuard⟩
    cases wantNonneg with
    | true => exact hBleT
    | false => dsimp only; rw [hBleT]; rfl
  | false =>
    cases hNeg : sintNeg i a with
    | true =>
      have hGt : half1 < x :=
        Nat.lt_of_lt_of_le (Nat.sub_lt (half_pos_uint (intTwin i)) Nat.zero_lt_one)
          (sintNeg_sound hNeg hx).1
      have hBleF : Nat.ble x half1 = false := by
        cases hb : Nat.ble x half1 with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hb))
      refine ⟨?_, hGuard⟩
      cases wantNonneg with
      | true => exact hBleF
      | false => dsimp only; rw [hBleF]
    | false =>
      exact hGuard

/-- Exact `BoolAbs` + `RelGuard` for the 8 signed sign-test comparisons against
`0` (`x < 0`, `x ≥ 0`, `0 > y`, `0 ≤ y`) and `-1` (`x ≤ -1`, `x > -1`,
`-1 ≥ y`, `-1 < y`). -/
def sintSignCmpAbs (op : BinOp) (i : IntTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option BoolAbs :=
  let w := uintWidth (intTwin i)
  let m1 := modPow2 w - 1
  let pick (aZ aM : AbsVal) (srcZ srcM : Option Nat) (wantZ wantM : Bool) :
      Option BoolAbs :=
    match isZeroExact w aZ with
    | true => some (sintSignTestBool i aM srcM wantZ)
    | false =>
      match aM.exactVal? w with
      | some v =>
        match Nat.beq v m1 with
        | true => some (sintSignTestBool i aZ srcZ wantM)
        | false => none
      | none => none
  match binOpToCmp? op with
  | some .lt => pick a2 a1 srcR srcL false true
  | some .ge => pick a2 a1 srcR srcL true false
  | some .gt => pick a1 a2 srcL srcR false true
  | some .le => pick a1 a2 srcL srcR true false
  | _ => none

/-- Signed `<` on equal-width operands evaluates to `signedLt`. -/
private theorem evalScalarBinOp_sint_lt_raw (i : IntTy) (x y : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .lt ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes (intTwin i)⟩
        locals mem true =
      .ok (.scalar (boolToScalar (signedLt x y (uintBytes (intTwin i))))) locals
        mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [Nat.beq_refl]

/-- Signed `<=` on equal-width operands evaluates to `!signedLt` flipped. -/
private theorem evalScalarBinOp_sint_le_raw (i : IntTy) (x y : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .le ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes (intTwin i)⟩
        locals mem true =
      .ok (.scalar (boolToScalar (!(signedLt y x (uintBytes (intTwin i))))))
        locals mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [Nat.beq_refl]; rfl

/-- Signed `>` on equal-width operands evaluates to flipped `signedLt`. -/
private theorem evalScalarBinOp_sint_gt_raw (i : IntTy) (x y : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .gt ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes (intTwin i)⟩
        locals mem true =
      .ok (.scalar (boolToScalar (signedLt y x (uintBytes (intTwin i))))) locals
        mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [Nat.beq_refl]

/-- Signed `>=` on equal-width operands evaluates to `!signedLt`. -/
private theorem evalScalarBinOp_sint_ge_raw (i : IntTy) (x y : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .ge ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes (intTwin i)⟩
        locals mem true =
      .ok (.scalar (boolToScalar (!(signedLt x y (uintBytes (intTwin i))))))
        locals mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [Nat.beq_refl]; rfl

private theorem binOpToCmp?_ord_eq {op : BinOp} {cop : CmpOp}
    (h : binOpToCmp? op = some cop) :
    match cop with
    | .lt => op = .lt
    | .le => op = .le
    | .gt => op = .gt
    | .ge => op = .ge
    | _ => True := by
  cases op with
  | lt => injection h with h; subst h; rfl
  | le => injection h with h; subst h; rfl
  | gt => injection h with h; subst h; rfl
  | ge => injection h with h; subst h; rfl
  | eq => injection h with h; subst h; exact True.intro
  | ne => injection h with h; subst h; exact True.intro
  | _ => nomatch h

theorem sintSignCmpAbs_sound {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {ba : BoolAbs} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory)
    (h : sintSignCmpAbs op i a1 srcL a2 srcR = some ba)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩
        ⟨y, uintBytes (intTwin i)⟩ locals mem true = .ok v locals mem ∧
      ba.denote locals (some v) := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  have hPick : ∀ {aZ aM : AbsVal} {srcZ srcM : Option Nat} {z m : Nat}
      (negate : Bool),
      aZ.denote (uintWidth (intTwin i)) (some z) →
      aM.denote (uintWidth (intTwin i)) (some m) →
      z < modPow2 (uintWidth (intTwin i)) →
      m < modPow2 (uintWidth (intTwin i)) →
      (∀ r, srcZ = some r → localUintNat? locals r (intTwin i) = some z) →
      (∀ r, srcM = some r → localUintNat? locals r (intTwin i) = some m) →
      (match isZeroExact (uintWidth (intTwin i)) aZ with
       | true => some (sintSignTestBool i aM srcM negate)
       | false =>
         match aM.exactVal? (uintWidth (intTwin i)) with
         | some v =>
           match Nat.beq v (modPow2 (uintWidth (intTwin i)) - 1) with
           | true => some (sintSignTestBool i aZ srcZ (!negate))
           | false => none
         | none => none) = some ba →
      ba.denote locals (some (.scalar (boolToScalar
        (match negate with
         | false => signedLt m z (uintBytes (intTwin i))
         | true => !(signedLt m z (uintBytes (intTwin i))))))) := by
    intro aZ aM srcZ srcM z m negate hz hm hzLt hmLt hSrcZ hSrcM hP
    cases hZ : isZeroExact (uintWidth (intTwin i)) aZ with
    | true =>
      rw [hZ] at hP; cases hP
      have hz0 := isZeroExact_eq hZ hz; subst hz0
      cases negate with
      | false =>
        rw [signedLt_zero_eq hmLt]
        exact boolAbs_denote_of_bool (sintSignTestBool_sound false hm hSrcM)
      | true =>
        dsimp only
        rw [signedLt_zero_eq hmLt, Bool.not_not]
        exact boolAbs_denote_of_bool (sintSignTestBool_sound true hm hSrcM)
    | false =>
      rw [hZ] at hP; dsimp only at hP
      cases hEx : aM.exactVal? (uintWidth (intTwin i)) with
      | none => rw [hEx] at hP; nomatch hP
      | some v =>
        rw [hEx] at hP; dsimp only at hP
        cases hEq : Nat.beq v (modPow2 (uintWidth (intTwin i)) - 1) with
        | false => rw [hEq] at hP; nomatch hP
        | true =>
          rw [hEq] at hP; cases hP
          have hmEq : m = modPow2 (uintWidth (intTwin i)) - 1 :=
            Eq.trans (exactVal?_eq hEx hm).symm (Nat.eq_of_beq_eq_true hEq)
          subst hmEq
          cases negate with
          | false =>
            rw [signedLt_minusOne_eq hzLt]
            exact boolAbs_denote_of_bool (sintSignTestBool_sound true hz hSrcZ)
          | true =>
            dsimp only
            rw [signedLt_minusOne_eq hzLt]
            exact boolAbs_denote_of_bool (sintSignTestBool_sound false hz hSrcZ)
  unfold sintSignCmpAbs at h
  dsimp only at h
  cases hC : binOpToCmp? op with
  | none => rw [hC] at h; nomatch h
  | some cop =>
    rw [hC] at h
    have hEq := binOpToCmp?_ord_eq hC
    cases cop with
    | eq | ne => nomatch h
    | lt =>
      have hop : op = .lt := hEq; subst hop
      exact ⟨_, evalScalarBinOp_sint_lt_raw i x y locals mem,
        hPick false hy hx hyLt hxLt hR hL h⟩
    | ge =>
      have hop : op = .ge := hEq; subst hop
      exact ⟨_, evalScalarBinOp_sint_ge_raw i x y locals mem,
        hPick true hy hx hyLt hxLt hR hL h⟩
    | gt =>
      have hop : op = .gt := hEq; subst hop
      exact ⟨_, evalScalarBinOp_sint_gt_raw i x y locals mem,
        hPick false hx hy hxLt hyLt hL hR h⟩
    | le =>
      have hop : op = .le := hEq; subst hop
      exact ⟨_, evalScalarBinOp_sint_le_raw i x y locals mem,
        hPick true hx hy hxLt hyLt hL hR h⟩

/-- Retype an unsigned-twin result as signed (`bool` results pass through). -/
def retypeSintResult (i : IntTy) : Option MirAbsVal → Option MirAbsVal
  | some (.uint u a s) =>
    match uintTyBeq u (intTwin i) with
    | true => some (.sint i a s)
    | false => none
  | some (.bool b) => some (.bool b)
  | _ => none

theorem retypeSintResult_denote {i : IntTy} {av0 av : MirAbsVal}
    {locals : List LocalSlot} {v : Value}
    (h : retypeSintResult i (some av0) = some av) (hD : av0.denote locals v) :
    av.denote locals v := by
  cases av0 with
  | uint u a s =>
    simp only [retypeSintResult] at h
    cases hU : uintTyBeq u (intTwin i) with
    | false => rw [hU] at h; nomatch h
    | true =>
      rw [hU] at h
      injection h with h
      subst h
      have hu := uintTy_eq_of_beq hU
      subst hu
      exact hD
  | bool b =>
    injection h with h
    subst h
    exact hD
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sint _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

/-- True iff `op` is a bit-shift operator (which permits mixed integer widths
and mixed signedness between LHS and RHS). -/
def binOpIsShift : BinOp → Bool
  | .shl | .shr | .shlUnchecked | .shrUnchecked => true
  | _ => false

/-- Exact abstract result of an arithmetic right shift of the signed bit
pattern `c` (of type `i`) by an in-range amount `k`. -/
def sintShrConst (i : IntTy) (c k : Nat) : AbsVal :=
  AbsVal.const (uintWidth (intTwin i))
    (arithmeticShrBits c (uintBytes (intTwin i)) k)

theorem sintShrConst_sound (i : IntTy) (c k : Nat) :
    (sintShrConst i c k).denote (uintWidth (intTwin i))
      (some (arithmeticShrBits c (uintBytes (intTwin i)) k)) := by
  have hLt : arithmeticShrBits c (uintBytes (intTwin i)) k <
      modPow2 (uintWidth (intTwin i)) := by
    rw [← two_pow_uintBytes]
    exact Anneal.Scalars.arithmeticShrBits_lt_two_pow _ _ _
  have h := absVal_const_sound (c := arithmeticShrBits c (uintBytes (intTwin i)) k)
    (uintWidth_valid (intTwin i))
  have hEq : Nat.mod (arithmeticShrBits c (uintBytes (intTwin i)) k)
      (modPow2 (uintWidth (intTwin i))) =
      arithmeticShrBits c (uintBytes (intTwin i)) k := Nat.mod_eq_of_lt hLt
  simp only [wrapVal, hEq] at h
  exact h

/-- Signed `.shr` evaluates to an arithmetic shift by the wrapped amount. -/
theorem evalScalarBinOp_sint_shr_eq {u u2 : UintTy} {a b : Nat}
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem true =
      .ok (.scalar ⟨arithmeticShrBits a (uintBytes u)
        (Nat.mod b (uintWidth u)), uintBytes u⟩) locals mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [uintBytes_mul_eight]

/-- Signed `.shrUnchecked` by an in-range amount is an arithmetic shift. -/
theorem evalScalarBinOp_sint_shrUnchecked_eq {u u2 : UintTy} {a b : Nat}
    (locals : List LocalSlot) (mem : Memory)
    (hb : Nat.ble (uintWidth u) b = false) :
    evalScalarBinOp .shrUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem
        true =
      .ok (.scalar ⟨arithmeticShrBits a (uintBytes u) b, uintBytes u⟩)
        locals mem := by
  conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [uintBytes_beq_zero]; conv => lhs; whnf
  rw [uintBytes_mul_eight, hb]

/-- Signed-LHS shift transfer supporting arbitrary RHS integer width `u2`
(both unsigned and signed RHS). Left shifts and non-negative right shifts
reuse `binOpUintAbs` on the unsigned twin; right shifts of other exact
operands fold to the exact arithmetic shift (`sintShrConst`). -/
def shiftSintAbs (op : BinOp) (i : IntTy) (a1 : AbsVal) (u2 : UintTy)
    (a2 : AbsVal) : Option MirAbsVal :=
  let u1 := intTwin i
  let w1 := uintWidth u1
  let w2 := uintWidth u2
  match binOpToShift? op with
  | some .shl | some .shlUnchecked =>
    retypeSintResult i (binOpUintAbs op u1 a1 none u2 a2 none)
  | some .shr =>
    match sintNonneg i a1 with
    | true => retypeSintResult i (binOpUintAbs .shr u1 a1 none u2 a2 none)
    | false =>
      match a1.exactVal? w1, a2.exactVal? w2 with
      | some c1, some c2 =>
        some (mkSintVal i
          (sintShrConst i c1 (Nat.mod c2 w1)))
      | _, _ => some (mkSintVal i (AbsVal.topInit w1))
  | some .shrUnchecked =>
    match sintNonneg i a1 with
    | true =>
      retypeSintResult i (binOpUintAbs .shrUnchecked u1 a1 none u2 a2 none)
    | false =>
      match a1.exactVal? w1, a2.exactVal? w2 with
      | some c1, some c2 =>
        match Nat.ble w1 c2 with
        | false => some (mkSintVal i (sintShrConst i c1 c2))
        | true => none
      | _, _ =>
        match AbsVal.shiftInBounds w1 w2 a2 with
        | true => some (mkSintVal i (AbsVal.topInit w1))
        | false => none
  | none => none

theorem shiftSintAbs_not_offset {op : BinOp} {i : IntTy} {a1 : AbsVal}
    {u2 : UintTy} {a2 : AbsVal} {av : MirAbsVal}
    (h : shiftSintAbs op i a1 u2 a2 = some av) : op ≠ .offset := by
  intro hOp
  subst hOp
  nomatch h

theorem shiftSintAbs_sound {op : BinOp} {i : IntTy} {a1 : AbsVal}
    {u2 : UintTy} {a2 : AbsVal} {av : MirAbsVal} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory)
    (h : shiftSintAbs op i a1 u2 a2 = some av)
    (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth u2) (some y)) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes u2⟩
        locals mem true = .ok v locals mem ∧
      av.denote locals v := by
  have hShl : ∀ (op' : BinOp), binOpSignAgnostic op' = true →
      retypeSintResult i (binOpUintAbs op' (intTwin i) a1 none u2 a2 none) = some av →
      ∃ v, evalScalarBinOp op' ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes u2⟩
          locals mem true = .ok v locals mem ∧
        av.denote locals v := by
    intro op' hAg h'
    cases hB : binOpUintAbs op' (intTwin i) a1 none u2 a2 none with
    | none => rw [hB] at h'; nomatch h'
    | some av0 =>
      rw [hB] at h'
      cases binOpUintAbs_sound mem hB hi1 hi2 hx hy
          (fun _ hr => nomatch hr) (fun _ hr => nomatch hr) with
      | intro v hv =>
        rw [evalScalarBinOp_signAgnostic locals mem hAg]
        exact ⟨v, hv.1, retypeSintResult_denote h' hv.2⟩
  unfold shiftSintAbs at h; dsimp only at h
  cases hSh : binOpToShift? op with
  | none => rw [hSh] at h; nomatch h
  | some sop =>
    rw [hSh] at h
    have hOpEq := binOpToShift?_eq hSh
    cases sop with
    | shl =>
      have hOp : op = .shl := hOpEq; subst hOp
      exact hShl .shl rfl h
    | shlUnchecked =>
      have hOp : op = .shlUnchecked := hOpEq; subst hOp
      exact hShl .shlUnchecked rfl h
    | shr =>
      have hOp : op = .shr := hOpEq; subst hOp
      dsimp only at h
      cases hNN : sintNonneg i a1 with
      | true =>
        rw [hNN] at h; dsimp only at h
        cases hB : binOpUintAbs .shr (intTwin i) a1 none u2 a2 none with
        | none => rw [hB] at h; nomatch h
        | some av0 =>
          rw [hB] at h
          cases binOpUintAbs_sound mem hB hi1 hi2 hx hy
              (fun _ hr => nomatch hr) (fun _ hr => nomatch hr) with
          | intro v hv =>
            rw [evalScalarBinOp_sint_shr_nonneg locals mem (sintNonneg_sound hNN hx)]
            exact ⟨v, hv.1, retypeSintResult_denote h hv.2⟩
      | false =>
        rw [hNN] at h; dsimp only at h
        cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
        | some c1 =>
          cases hE2 : a2.exactVal? (uintWidth u2) with
          | some c2 =>
            rw [hE1, hE2] at h; cases h
            have h1 := exactVal?_eq hE1 hx; have h2 := exactVal?_eq hE2 hy
            subst h1; subst h2
            exact ⟨_, evalScalarBinOp_sint_shr_eq locals mem,
              mkSintVal_denote (sintShrConst_sound _ _ _)⟩
          | none =>
            rw [hE1, hE2] at h; cases h
            cases evalScalarBinOp_sint_shr locals mem (u := intTwin i) (a := x)
                (b := y) (u2 := u2) with
            | intro bits hb =>
              exact ⟨_, hb.2, mkSintVal_denote (absVal_topInit_sound hb.1)⟩
        | none =>
          rw [hE1] at h; cases h
          cases evalScalarBinOp_sint_shr locals mem (u := intTwin i) (a := x)
              (b := y) (u2 := u2) with
          | intro bits hb =>
            exact ⟨_, hb.2, mkSintVal_denote (absVal_topInit_sound hb.1)⟩
    | shrUnchecked =>
      have hOp : op = .shrUnchecked := hOpEq; subst hOp
      dsimp only at h
      cases hNN : sintNonneg i a1 with
      | true =>
        rw [hNN] at h; dsimp only at h
        cases hB : binOpUintAbs .shrUnchecked (intTwin i) a1 none u2 a2 none with
        | none => rw [hB] at h; nomatch h
        | some av0 =>
          rw [hB] at h
          cases binOpUintAbs_sound mem hB hi1 hi2 hx hy
              (fun _ hr => nomatch hr) (fun _ hr => nomatch hr) with
          | intro v hv =>
            rw [evalScalarBinOp_sint_shrUnchecked_nonneg locals mem
              (sintNonneg_sound hNN hx)]
            exact ⟨v, hv.1, retypeSintResult_denote h hv.2⟩
      | false =>
        rw [hNN] at h; dsimp only at h
        have hFallback :
            (match AbsVal.shiftInBounds (uintWidth (intTwin i)) (uintWidth u2) a2 with
              | true => some (mkSintVal i (AbsVal.topInit (uintWidth (intTwin i))))
              | false => none) = some av →
            ∃ v, evalScalarBinOp .shrUnchecked ⟨x, uintBytes (intTwin i)⟩
                ⟨y, uintBytes u2⟩ locals mem true = .ok v locals mem ∧
              av.denote locals v := by
          intro hF
          cases hS : AbsVal.shiftInBounds (uintWidth (intTwin i)) (uintWidth u2) a2 with
          | false => rw [hS] at hF; nomatch hF
          | true =>
            rw [hS] at hF; cases hF
            cases absVal_shiftInBounds_sound hS hy with
            | intro y' hy' =>
              injection hy'.1 with hyEq; subst hyEq
              cases evalScalarBinOp_sint_shrUnchecked locals mem
                  (u := intTwin i) (a := x) (u2 := u2) hy'.2.1 with
              | intro bits hb =>
                exact ⟨_, hb.2, mkSintVal_denote (absVal_topInit_sound hb.1)⟩
        cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
        | some c1 =>
          cases hE2 : a2.exactVal? (uintWidth u2) with
          | some c2 =>
            rw [hE1, hE2] at h; dsimp only at h
            cases hB : Nat.ble (uintWidth (intTwin i)) c2 with
            | true => rw [hB] at h; nomatch h
            | false =>
              rw [hB] at h; cases h
              have h1 := exactVal?_eq hE1 hx; have h2 := exactVal?_eq hE2 hy
              subst h1; subst h2
              exact ⟨_, evalScalarBinOp_sint_shrUnchecked_eq locals mem hB,
                mkSintVal_denote (sintShrConst_sound _ _ _)⟩
          | none => rw [hE1, hE2] at h; exact hFallback h
        | none => rw [hE1] at h; exact hFallback h

/-- Signed `evalSignedDiv` either always faults or always returns the same
scalar, independently of the threaded locals and memory. -/
theorem evalSignedDiv_cases (a b sz : Nat) :
    (∀ (l : List LocalSlot) (m : Memory), evalSignedDiv a b sz l m = .ub) ∨
      ∃ r, ∀ (l : List LocalSlot) (m : Memory),
        evalSignedDiv a b sz l m = .ok (.scalar ⟨r, sz⟩) l m := by
  cases h : Bool.and
      (Nat.beq (wrapScalarBits a (scalarModulus sz))
        (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
      (Nat.beq (wrapScalarBits b (scalarModulus sz))
        (Nat.sub (scalarModulus sz) 1)) with
  | true => exact Or.inl (fun _ _ => by simp only [evalSignedDiv, h])
  | false =>
    refine Or.inr ⟨?r, fun l m => ?h⟩
    case h =>
      simp only [evalSignedDiv, h]
      rfl

/-- Frame independence of `evalSignedRem` (see `evalSignedDiv_cases`). -/
theorem evalSignedRem_cases (a b sz : Nat) :
    (∀ (l : List LocalSlot) (m : Memory), evalSignedRem a b sz l m = .ub) ∨
      ∃ r, ∀ (l : List LocalSlot) (m : Memory),
        evalSignedRem a b sz l m = .ok (.scalar ⟨r, sz⟩) l m := by
  cases h : Bool.and
      (Nat.beq (wrapScalarBits a (scalarModulus sz))
        (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
      (Nat.beq (wrapScalarBits b (scalarModulus sz))
        (Nat.sub (scalarModulus sz) 1)) with
  | true => exact Or.inl (fun _ _ => by simp only [evalSignedRem, h])
  | false =>
    refine Or.inr ⟨?r, fun l m => ?h⟩
    case h =>
      simp only [evalSignedRem, h]
      rfl

/-- A signed `div` / `rem` result computed in the empty frame is the result
in every frame. -/
theorem evalScalarBinOp_sint_divrem_frame {op : BinOp} {u : UintTy} {a b : Nat}
    {sc : ScalarInt} {l : List LocalSlot} {m : Memory}
    (hop : op = .div ∨ op = .rem)
    (h : evalScalarBinOp op ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ [] {} true =
      .ok (.scalar sc) l m) :
    ∃ r, sc = ⟨r, uintBytes u⟩ ∧ ∀ (locals : List LocalSlot) (mem : Memory),
      evalScalarBinOp op ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
        .ok (.scalar ⟨r, uintBytes u⟩) locals mem := by
  have hCases : ∀ (f : Nat → Nat → Nat → List LocalSlot → Memory →
      RvalueEvalResult),
      ((∀ l m, f a b (uintBytes u) l m = .ub) ∨
        ∃ r, ∀ l m, f a b (uintBytes u) l m =
          .ok (.scalar ⟨r, uintBytes u⟩) l m) →
      (∀ locals mem, evalScalarBinOp op ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩
        locals mem true =
          match Nat.beq b 0 with
          | true => .ub
          | false => f a b (uintBytes u) locals mem) →
      ∃ r, sc = ⟨r, uintBytes u⟩ ∧ ∀ (locals : List LocalSlot) (mem : Memory),
        evalScalarBinOp op ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
          .ok (.scalar ⟨r, uintBytes u⟩) locals mem := by
    intro f hf hEq
    rw [hEq] at h
    cases hb : Nat.beq b 0 with
    | true => rw [hb] at h; nomatch h
    | false =>
      rw [hb] at h
      cases hf with
      | inl hU => rw [hU] at h; nomatch h
      | inr hR =>
        cases hR with
        | intro r hR =>
          rw [hR] at h
          injection h with h1
          injection h1 with h1
          refine ⟨r, h1.symm, fun locals mem => ?_⟩
          rw [hEq, hb]
          exact hR locals mem
  cases hop with
  | inl hop =>
    subst hop
    refine hCases evalSignedDiv (evalSignedDiv_cases a b (uintBytes u)) ?_
    intro locals mem
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
    cases Nat.beq b 0 <;> rfl
  | inr hop =>
    subst hop
    refine hCases evalSignedRem (evalSignedRem_cases a b (uintBytes u)) ?_
    intro locals mem
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
    cases Nat.beq b 0 <;> rfl


/-- Exact signed `div` / `rem` of two exact operands, evaluated with the
ground `evalScalarBinOp` (whose result is frame-independent). -/
def sintDivRemConst? (op : BinOp) (i : IntTy) (a1 a2 : AbsVal) : Option Nat :=
  match a1.exactVal? (uintWidth (intTwin i)),
      a2.exactVal? (uintWidth (intTwin i)) with
  | some c1, some c2 =>
    match evalScalarBinOp op ⟨c1, uintBytes (intTwin i)⟩
        ⟨c2, uintBytes (intTwin i)⟩ [] {} true with
    | .ok (.scalar sc) _ _ => some sc.bits
    | _ => none
  | _, _ => none

theorem sintDivRemConst?_sound {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {x y r : Nat} (hop : op = .div ∨ op = .rem)
    (h : sintDivRemConst? op i a1 a2 = some r)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩ ⟨y, uintBytes (intTwin i)⟩
      locals mem true = .ok (.scalar ⟨r, uintBytes (intTwin i)⟩) locals mem := by
  unfold sintDivRemConst? at h
  cases hE1 : a1.exactVal? (uintWidth (intTwin i)) with
  | none => rw [hE1] at h; nomatch h
  | some c1 =>
    cases hE2 : a2.exactVal? (uintWidth (intTwin i)) with
    | none => rw [hE1, hE2] at h; nomatch h
    | some c2 =>
      rw [hE1, hE2] at h
      dsimp only at h
      have h1 := (absVal_exactVal?_sound hE1 hx).1
      have h2 := (absVal_exactVal?_sound hE2 hy).1
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      cases hEv : evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩
          ⟨y, uintBytes (intTwin i)⟩ [] {} true with
      | ub => rw [hEv] at h; nomatch h
      | unsupported => rw [hEv] at h; nomatch h
      | ok v l m =>
        rw [hEv] at h
        cases v with
        | scalar sc =>
          injection h with h
          subst h
          cases evalScalarBinOp_sint_divrem_frame hop hEv with
          | intro r' hr =>
            rw [hr.1]
            exact hr.2 locals mem
        | _ => nomatch h

/-- Abstract signed `div` / `rem` on operands of equal type `i`, certified
UB-free by `sintDivRemOk`: exact unsigned transfer on non-negative operands,
constant folding on exact operands, and `topInit` otherwise. -/
def sintDivRemAbs (op : BinOp) (i : IntTy) (a1 a2 : AbsVal) :
    Option MirAbsVal :=
  match sintDivRemOk i a1 a2 with
  | false => none
  | true =>
    match sintNonneg i a1 && sintNonneg i a2 with
    | true =>
      match op with
      | .div => some (mkSintVal i (divUintAbs (uintWidth (intTwin i)) a1 a2))
      | _ => some (mkSintVal i (remUintAbs (uintWidth (intTwin i)) a1 a2))
    | false =>
      match sintDivRemConst? op i a1 a2 with
      | some r => some (mkSintVal i (AbsVal.const (uintWidth (intTwin i)) r))
      | none => some (mkSintVal i (AbsVal.topInit (uintWidth (intTwin i))))

/-- Soundness of `sintDivRemAbs`; the operator (`div` or `rem`) is selected by
unification against `hop`. -/
theorem sintDivRemAbs_sound {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {av : MirAbsVal} {locals : List LocalSlot} {x y : Nat} (mem : Memory)
    (hop : op = .div ∨ op = .rem)
    (h : sintDivRemAbs op i a1 a2 = some av)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y)) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩
        ⟨y, uintBytes (intTwin i)⟩ locals mem true = .ok v locals mem ∧
      av.denote locals v := by
  have hw := uintWidth_valid (intTwin i)
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  unfold sintDivRemAbs at h
  cases hOk : sintDivRemOk i a1 a2 with
  | false => rw [hOk] at h; nomatch h
  | true =>
    rw [hOk] at h
    dsimp only at h
    have hS := sintDivRemOk_sound hOk hx hy
    cases hNN : (sintNonneg i a1 && sintNonneg i a2) with
    | true =>
      rw [hNN] at h
      have hx' := sintNonneg_sound (bool_and_true_left hNN) hx
      have hy' := sintNonneg_sound (bool_and_true_right hNN) hy
      have hyPos : 0 < y := Nat.pos_of_ne_zero hS.1
      cases hop with
      | inl hD =>
        subst hD
        injection h with h
        subst h
        have hDiv := divUintAbs_sound hw hx hy hyPos
        rw [wrapVal_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxLt)]
          at hDiv
        exact ⟨_, evalScalarBinOp_sint_div_nonneg locals mem hx' hy' hS.1,
          mkSintVal_denote hDiv⟩
      | inr hR =>
        subst hR
        injection h with h
        subst h
        have hRem := remUintAbs_sound hw hx hy hyPos
        rw [wrapVal_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le x y) hxLt)] at hRem
        exact ⟨_, evalScalarBinOp_sint_rem_nonneg locals mem hx' hy' hS.1,
          mkSintVal_denote hRem⟩
    | false =>
      rw [hNN] at h
      dsimp only at h
      cases evalScalarBinOp_sint_divrem_safe locals mem hop hxLt hyLt hS.1
          hS.2 with
      | intro bits hb =>
        cases hC : sintDivRemConst? op i a1 a2 with
        | none =>
          rw [hC] at h; cases h
          exact ⟨_, hb.2, mkSintVal_denote (absVal_topInit_sound hb.1)⟩
        | some r =>
          rw [hC] at h; cases h
          have hEv := sintDivRemConst?_sound hop hC hx hy locals mem
          have hbr : bits = r := by rw [hb.2] at hEv; cases hEv; rfl
          subst hbr
          exact ⟨_, hb.2, mkSintVal_denote (absVal_const_denote_lt hw hb.1)⟩

/-- Abstract signed `BinOp` transfer on operands of equal type `i`, tracked by
two's-complement bit pattern and dispatched by operator group:
comparisons (`sintCmpAbs`: biased static decision plus `RelGuard` synthesis),
sign-agnostic operators (the unsigned transfer on the twin type), arithmetic
right shifts (`shiftSintAbs`), UB-free `div` / `rem` (`sintDivRemAbs`), and
checked (`*WithOverflow`) / unchecked (`*Unchecked`) arithmetic certified by
`sintAddOk` / `sintSubOk` / `sintMulOk`. -/
def binOpSintAbs (op : BinOp) (i : IntTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  match op with
  | .eq | .ne | .lt | .le | .gt | .ge => sintCmpAbs op i a1 srcL a2 srcR
  | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor | .shl | .shlUnchecked =>
    retypeSintResult i
      (binOpUintAbs op (intTwin i) a1 srcL (intTwin i) a2 srcR)
  | .shr | .shrUnchecked => shiftSintAbs op i a1 (intTwin i) a2
  | .div | .rem => sintDivRemAbs op i a1 a2
  | .addUnchecked =>
    match sintAddOk i a1 a2 with
    | true => some (mkSintVal i (addUintAbs (uintWidth (intTwin i)) a1 a2))
    | false => none
  | .subUnchecked =>
    match sintSubOk i a1 a2 with
    | true => some (mkSintVal i (subUintAbs (uintWidth (intTwin i)) a1 a2))
    | false => none
  | .mulUnchecked =>
    match sintMulOk i a1 a2 with
    | true => some (mkSintVal i (mulUintAbs (uintWidth (intTwin i)) a1 a2))
    | false => none
  | .addWithOverflow =>
    some (mkSintBoolPairVal i (addUintAbs (uintWidth (intTwin i)) a1 a2)
      (sintAddOverflowBoolAbs i srcL srcR a1 a2))
  | .subWithOverflow =>
    some (mkSintBoolPairVal i (subUintAbs (uintWidth (intTwin i)) a1 a2)
      (sintSubOverflowBoolAbs i srcL srcR a1 a2))
  | .mulWithOverflow =>
    some (mkSintBoolPairVal i (mulUintAbs (uintWidth (intTwin i)) a1 a2)
      (sintMulOverflowBoolAbs i a1 a2))
  | _ => none

theorem binOpSintAbs_not_offset {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal}
    (h : binOpSintAbs op i a1 srcL a2 srcR = some av) : op ≠ .offset := by
  intro hOp
  subst hOp
  nomatch h

/-- Scalar-level soundness of `binOpSintAbs` against `evalScalarBinOp` at
`isSigned = true`. Each operator group is discharged by one group lemma, and
the operator inside a group is selected by unification. -/
theorem binOpSintAbs_sound {op : BinOp} {i : IntTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal} {locals : List LocalSlot}
    {x y : Nat} (mem : Memory)
    (h : binOpSintAbs op i a1 srcL a2 srcR = some av)
    (hi1 : a1.isInit = true) (hi2 : a2.isInit = true)
    (hx : a1.denote (uintWidth (intTwin i)) (some x))
    (hy : a2.denote (uintWidth (intTwin i)) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r (intTwin i) = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r (intTwin i) = some y) :
    ∃ v, evalScalarBinOp op ⟨x, uintBytes (intTwin i)⟩
        ⟨y, uintBytes (intTwin i)⟩ locals mem true = .ok v locals mem ∧
      av.denote locals v := by
  have hw := uintWidth_valid (intTwin i)
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  have hAgn : ∀ (op' : BinOp), binOpSignAgnostic op' = true →
      retypeSintResult i
        (binOpUintAbs op' (intTwin i) a1 srcL (intTwin i) a2 srcR) = some av →
      ∃ v, evalScalarBinOp op' ⟨x, uintBytes (intTwin i)⟩
          ⟨y, uintBytes (intTwin i)⟩ locals mem true = .ok v locals mem ∧
        av.denote locals v := by
    intro op' hAg h'
    cases hB : binOpUintAbs op' (intTwin i) a1 srcL (intTwin i) a2 srcR with
    | none => rw [hB] at h'; nomatch h'
    | some av0 =>
      rw [hB] at h'
      cases binOpUintAbs_sound mem hB hi1 hi2 hx hy hL hR with
      | intro v hv =>
        rw [evalScalarBinOp_signAgnostic locals mem hAg]
        exact ⟨v, hv.1, retypeSintResult_denote h' hv.2⟩
  have hSub := subUintAbs_sound hw hi1 hi2 hx hy
  rw [Nat.add_comm (modPow2 (uintWidth (intTwin i))) x] at hSub
  cases op with
  | eq | ne | lt | le | gt | ge => exact sintCmpAbs_sound mem rfl h hx hy hL hR
  | add | sub | mul | bitAnd | bitOr | bitXor | shl | shlUnchecked =>
    exact hAgn _ rfl h
  | shr | shrUnchecked => exact shiftSintAbs_sound mem h hi1 hi2 hx hy
  | div => exact sintDivRemAbs_sound mem (Or.inl rfl) h hx hy
  | rem => exact sintDivRemAbs_sound mem (Or.inr rfl) h hx hy
  | addUnchecked =>
    unfold binOpSintAbs at h
    cases hNo : sintAddOk i a1 a2 with
    | false => rw [hNo] at h; nomatch h
    | true =>
      rw [hNo] at h; cases h
      exact ⟨_, evalScalarBinOp_sint_addUnchecked locals mem
        (sintAddOk_sound hNo hx hy),
        mkSintVal_denote (addUintAbs_sound hw hi1 hi2 hx hy)⟩
  | subUnchecked =>
    unfold binOpSintAbs at h
    cases hNo : sintSubOk i a1 a2 with
    | false => rw [hNo] at h; nomatch h
    | true =>
      rw [hNo] at h; cases h
      exact ⟨_, evalScalarBinOp_sint_subUnchecked locals mem hxLt hyLt
        (sintSubOk_sound hNo hx hy), mkSintVal_denote hSub⟩
  | mulUnchecked =>
    unfold binOpSintAbs at h
    cases hNo : sintMulOk i a1 a2 with
    | false => rw [hNo] at h; nomatch h
    | true =>
      rw [hNo] at h; cases h
      exact ⟨_, evalScalarBinOp_sint_mulUnchecked locals mem
        (sintMulOk_sound hNo hx hy),
        mkSintVal_denote (mulUintAbs_sound hw hx hy)⟩
  | addWithOverflow =>
    cases h
    exact ⟨_, evalScalarBinOp_sint_addWithOverflow locals mem,
      mkSintBoolPairVal_denote (sintAddOverflowBoolAbs_isInit i srcL srcR a1 a2)
        (addUintAbs_sound hw hi1 hi2 hx hy)
        (boolAbs_denote_of_bool (sintAddOverflowBoolAbs_sound hx hy hL hR))⟩
  | subWithOverflow =>
    cases h
    exact ⟨_, evalScalarBinOp_sint_subWithOverflow locals mem hxLt hyLt,
      mkSintBoolPairVal_denote (sintSubOverflowBoolAbs_isInit i srcL srcR a1 a2)
        hSub
        (boolAbs_denote_of_bool (sintSubOverflowBoolAbs_sound hx hy hL hR))⟩
  | mulWithOverflow =>
    cases h
    exact ⟨_, evalScalarBinOp_sint_mulWithOverflow locals mem,
      mkSintBoolPairVal_denote (sintMulOverflowBoolAbs_isInit i a1 a2)
        (mulUintAbs_sound hw hx hy)
        (boolAbs_denote_of_bool (sintMulOverflowBoolAbs_sound hx hy))⟩
  | _ => nomatch h

private def sintWidenBiasedIv (wSrc wDst sLo sHi : Nat) : AbsVal :=
  let shift := halfModPow2 wDst - halfModPow2 wSrc
  reduceAbsVal wDst
    ⟨.init, Tnum.top wDst,
      .iv (signedBias wDst (sLo + shift)) (signedBias wDst (sHi + shift)), .top⟩

private theorem sintWidenBiasedIv_sound {uSrc uDst : UintTy} {sLo sHi x : Nat}
    (hB : Nat.ble (uintWidth uDst) (uintWidth uSrc) = false)
    (hxLt : x < modPow2 (uintWidth uSrc))
    (hLo : sLo ≤ signedBias (uintWidth uSrc) x)
    (hHi : signedBias (uintWidth uSrc) x ≤ sHi)
    (hHiLtSrc : sHi < modPow2 (uintWidth uSrc)) :
    (sintWidenBiasedIv (uintWidth uSrc) (uintWidth uDst) sLo sHi).denote
      (uintWidth uDst)
      (some (signExtendBits x (uintBytes uSrc) (uintBytes uDst))) := by
  have hwDst := uintWidth_valid uDst
  have hyLt := signExtendBits_lt_uint uSrc uDst x
  have hShiftEq := signedBias_signExtendBits hxLt hB
  have hLoLe : sLo + (halfModPow2 (uintWidth uDst) - halfModPow2 (uintWidth uSrc)) ≤
      signedBias (uintWidth uDst) (signExtendBits x (uintBytes uSrc) (uintBytes uDst)) := by
    rw [hShiftEq]; exact Nat.add_le_add_right hLo _
  have hLeHi : signedBias (uintWidth uDst) (signExtendBits x (uintBytes uSrc) (uintBytes uDst)) ≤
      sHi + (halfModPow2 (uintWidth uDst) - halfModPow2 (uintWidth uSrc)) := by
    rw [hShiftEq]; exact Nat.add_le_add_right hHi _
  have hHiLt : sHi + (halfModPow2 (uintWidth uDst) - halfModPow2 (uintWidth uSrc)) <
      modPow2 (uintWidth uDst) := by
    have hS1 : sHi < halfModPow2 (uintWidth uDst) :=
      Nat.lt_of_lt_of_le hHiLtSrc (modPow2_le_halfModPow2_of_lt_width hB)
    rw [modPow2_eq_half_add_half hwDst]
    exact Nat.add_lt_add_of_lt_of_le hS1 (Nat.sub_le _ _)
  exact reduceAbsVal_sound hwDst
    ⟨⟨_, rfl, hyLt⟩, tnum_top_sound hyLt,
      signedBias_iv_denote hwDst hLoLe hLeHi hHiLt hyLt, True.intro⟩

/-- Signed-source integer cast transfer: narrowing or same-width casts wrap
the bit pattern (`castUintAbs` on the twin type); widening casts sign-extend,
preserving non-negative `castUintAbs` precision, folding exact constants
through `signExtendBits`, and mapping bounded signed intervals `[sLo, sHi]`
(or full source range `[0, 2^wSrc - 1]` on `topInit`) into biased target
coordinates via `signedBias_signExtendBits`. -/
def sintCastAbs (iSrc : IntTy) (uDst : UintTy) (a : AbsVal) : AbsVal :=
  let uSrc := intTwin iSrc
  let wSrc := uintWidth uSrc
  let wDst := uintWidth uDst
  match Nat.ble wDst wSrc with
  | true => castUintAbs uSrc uDst a
  | false =>
    match sintNonneg iSrc a with
    | true => castUintAbs uSrc uDst a
    | false =>
      match a.exactVal? wSrc with
      | some c =>
        AbsVal.const wDst (signExtendBits c (uintBytes uSrc) (uintBytes uDst))
      | none =>
        match a.signedBounds? wSrc with
        | some (sLo, sHi) => sintWidenBiasedIv wSrc wDst sLo sHi
        | none => sintWidenBiasedIv wSrc wDst 0 (modPow2 wSrc - 1)

theorem sintCastAbs_sound {iSrc : IntTy} {uDst : UintTy} {a : AbsVal} {x : Nat}
    (hai : a.isInit = true) (hx : a.denote (uintWidth (intTwin iSrc)) (some x)) :
    (sintCastAbs iSrc uDst a).denote (uintWidth uDst)
      (some (match Nat.ble (uintBytes uDst) (uintBytes (intTwin iSrc)) with
        | true => wrapScalarBits x (scalarModulus (uintBytes uDst))
        | false => signExtendBits x (uintBytes (intTwin iSrc)) (uintBytes uDst))) := by
  unfold sintCastAbs
  dsimp only
  rw [uintBytes_ble_eq_width]
  cases hB : Nat.ble (uintWidth uDst) (uintWidth (intTwin iSrc)) with
  | true =>
    dsimp only
    rw [wrapScalarBits_eq_wrapVal]
    exact castUintAbs_sound hai hx
  | false =>
    dsimp only
    have hBb : Nat.ble (uintBytes uDst) (uintBytes (intTwin iSrc)) = false := by
      rw [uintBytes_ble_eq_width]; exact hB
    cases hN : sintNonneg iSrc a with
    | true =>
      dsimp only
      rw [signExtendBits_nonneg (sintNonneg_sound hN hx) hBb]
      have hc := castUintAbs_sound (uDst := uDst) hai hx
      have hxLt := (absVal_some_elim hx).1
      have hLtW : uintWidth (intTwin iSrc) < uintWidth uDst :=
        Nat.lt_of_not_le (fun hle => by
          rw [Nat.ble_eq_true_of_le hle] at hB; nomatch hB)
      have hMono := modPow2_mono (Nat.le_of_lt hLtW)
      rw [wrapVal_of_lt (Nat.lt_of_lt_of_le hxLt hMono)] at hc
      exact hc
    | false =>
      dsimp only
      cases hE : a.exactVal? (uintWidth (intTwin iSrc)) with
      | some c =>
        have hc := exactVal?_eq hE hx
        subst hc
        exact absVal_const_denote_lt (uintWidth_valid uDst)
          (signExtendBits_lt_uint _ _ _)
      | none =>
        dsimp only
        have hxLt := (absVal_some_elim hx).1
        cases hSB : a.signedBounds? (uintWidth (intTwin iSrc)) with
        | none =>
          exact sintWidenBiasedIv_sound hB hxLt (Nat.zero_le _)
            (Nat.le_sub_one_of_lt (signedBias_lt x))
            (Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one)
        | some p =>
          cases p with
          | mk sLo sHi =>
            have hBounds := absVal_signedBounds?_sound hSB hx
            exact sintWidenBiasedIv_sound hB hxLt
              hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2

/-- Boolean negation transfer (negating the attached guard). -/
def negBoolAbs : BoolAbs → BoolAbs
  | .exact v g => .exact (!v) g.negate
  | .top g => .top g.negate
  | other => other

theorem negBoolAbs_sound {locals : List LocalSlot} {ba : BoolAbs} {b : Bool}
    (h : ba.denoteBool locals b) : (negBoolAbs ba).denoteBool locals (!b) := by
  cases ba with
  | bot => exact h
  | uninit => exact h
  | top g => exact relGuard_negate_sound h
  | exact v g =>
    refine ⟨?_, relGuard_negate_sound h.2⟩
    rw [h.1]

/-- Apply a unary boolean truth table `(f false, f true)` to a `BoolAbs`,
preserving exactness and guards for identity and negation. -/
def applyBoolUnary (fFalse fTrue : Bool) (b : BoolAbs) : BoolAbs :=
  match fFalse, fTrue with
  | false, false => .exact false .none
  | true, true => .exact true .none
  | false, true => b
  | true, false => negBoolAbs b

theorem applyBoolUnary_sound {locals : List LocalSlot} {b : BoolAbs}
    {x : Bool} (f : Bool → Bool) (h : b.denoteBool locals x) :
    (applyBoolUnary (f false) (f true) b).denoteBool locals (f x) := by
  cases x with
  | false =>
    cases hF : f false <;> cases hT : f true <;>
      simp only [applyBoolUnary]
    · exact ⟨rfl, True.intro⟩
    · exact h
    · exact negBoolAbs_sound h
    · exact ⟨rfl, True.intro⟩
  | true =>
    cases hF : f false <;> cases hT : f true <;>
      simp only [applyBoolUnary]
    · exact ⟨rfl, True.intro⟩
    · exact h
    · exact negBoolAbs_sound h
    · exact ⟨rfl, True.intro⟩

/-- Concrete result of a supported boolean binary operator. -/
def boolBinOpEval : BinOp → Option (Bool → Bool → Bool)
  | .bitAnd => some (fun c1 c2 => c1 && c2)
  | .bitOr => some (fun c1 c2 => c1 || c2)
  | .bitXor => some (fun c1 c2 => xor c1 c2)
  | .eq => some (fun c1 c2 => c1 == c2)
  | .ne => some (fun c1 c2 => c1 != c2)
  | .lt => some (fun c1 c2 => !c1 && c2)
  | .le => some (fun c1 c2 => !c1 || c2)
  | .gt => some (fun c1 c2 => c1 && !c2)
  | .ge => some (fun c1 c2 => c1 || !c2)
  | _ => none

/-- Abstract boolean `BinOp` transfer for bitwise and comparison operators. -/
def binOpBoolAbs (op : BinOp) (b1 b2 : BoolAbs) : Option BoolAbs :=
  match b1.isInit && b2.isInit, boolBinOpEval op with
  | true, some f =>
    match b2 with
    | .exact c2 _ => some (applyBoolUnary (f false c2) (f true c2) b1)
    | _ =>
      match b1 with
      | .exact c1 _ => some (applyBoolUnary (f c1 false) (f c1 true) b2)
      | _ => some (.top .none)
  | _, _ => none

theorem binOpBoolAbs_not_offset {op : BinOp} {b1 b2 ba : BoolAbs}
    (h : binOpBoolAbs op b1 b2 = some ba) : op ≠ .offset := by
  intro hOp
  subst hOp
  unfold binOpBoolAbs at h
  cases hI : (b1.isInit && b2.isInit) <;> (rw [hI] at h; nomatch h)

private theorem evalScalarBinOp_bool_of_eval {op : BinOp}
    {f : Bool → Bool → Bool} (locals : List LocalSlot) (mem : Memory)
    (c1 c2 : Bool) (hEv : boolBinOpEval op = some f) :
    evalScalarBinOp op (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (f c1 c2))) locals mem := by
  cases op with
  | bitAnd => cases hEv; exact evalScalarBinOp_bool_bitAnd locals mem c1 c2
  | bitOr => cases hEv; exact evalScalarBinOp_bool_bitOr locals mem c1 c2
  | bitXor => cases hEv; exact evalScalarBinOp_bool_bitXor locals mem c1 c2
  | eq => cases hEv; exact evalScalarBinOp_bool_eq locals mem c1 c2
  | ne => cases hEv; exact evalScalarBinOp_bool_ne locals mem c1 c2
  | lt => cases hEv; exact evalScalarBinOp_bool_lt locals mem c1 c2
  | le => cases hEv; exact evalScalarBinOp_bool_le locals mem c1 c2
  | gt => cases hEv; exact evalScalarBinOp_bool_gt locals mem c1 c2
  | ge => cases hEv; exact evalScalarBinOp_bool_ge locals mem c1 c2
  | _ => nomatch hEv

/-- Scalar-level soundness of `binOpBoolAbs` against `evalScalarBinOp`. -/
theorem binOpBoolAbs_sound {op : BinOp} {b1 b2 ba : BoolAbs}
    {locals : List LocalSlot} {c1 c2 : Bool} (mem : Memory)
    (h : binOpBoolAbs op b1 b2 = some ba)
    (h1 : b1.denoteBool locals c1) (h2 : b2.denoteBool locals c2) :
    ∃ v, evalScalarBinOp op (boolToScalar c1) (boolToScalar c2) locals mem
        false = .ok v locals mem ∧ ba.denote locals (some v) := by
  unfold binOpBoolAbs at h
  cases hI : (b1.isInit && b2.isInit) with
  | false => rw [hI] at h; nomatch h
  | true =>
    rw [hI] at h
    cases hEv : boolBinOpEval op with
    | none => rw [hEv] at h; nomatch h
    | some f =>
      rw [hEv] at h
      have hDen : ba.denoteBool locals (f c1 c2) := by
        cases b2 with
        | exact v2 g2 =>
          dsimp only at h
          injection h with h
          subst h
          have hc2 : c2 = v2 := h2.1
          subst hc2
          exact applyBoolUnary_sound (fun x => f x c2) h1
        | top g2 =>
          cases b1 with
          | exact v1 g1 =>
            dsimp only at h
            injection h with h
            subst h
            have hc1 : c1 = v1 := h1.1
            subst hc1
            exact applyBoolUnary_sound (fun y => f c1 y) h2
          | top g1 =>
            dsimp only at h
            injection h with h
            subst h
            exact True.intro
          | bot => exact False.elim h1
          | uninit =>
            simp only [BoolAbs.isInit, Bool.false_and] at hI
            nomatch hI
        | bot => exact False.elim h2
        | uninit =>
          simp only [BoolAbs.isInit, Bool.and_false] at hI
          nomatch hI
      exact ⟨_, evalScalarBinOp_bool_of_eval locals mem c1 c2 hEv,
        boolAbs_denote_of_bool hDen⟩

/-! ## 7. Rvalues -/

/-- Source register of the left operand once the right operand has been
evaluated: forgotten when the right operand moves that same local. -/
def srcAfterRhs (rhs : Operand) (srcL : Option Nat) : Option Nat :=
  match operandMovedLocal? rhs, srcL with
  | some l, some r =>
    match Nat.beq r l with
    | true => none
    | false => some r
  | _, _ => srcL

theorem srcAfterRhs_sound {locals₁ locals₂ : List LocalSlot} {rhs : Operand}
    {srcL : Option Nat} {u : UintTy} {x : Nat}
    (hSrc : ∀ r, srcL = some r → localUintNat? locals₁ r u = some x)
    (hNone : operandMovedLocal? rhs = none → locals₂ = locals₁)
    (hSome : ∀ l, operandMovedLocal? rhs = some l →
      ∃ newCs, set? locals₁ l newCs = some locals₂) :
    ∀ r, srcAfterRhs rhs srcL = some r →
      localUintNat? locals₂ r u = some x := by
  intro r hr
  unfold srcAfterRhs at hr
  cases srcL with
  | none =>
    cases hMv : operandMovedLocal? rhs <;> (rw [hMv] at hr; nomatch hr)
  | some r0 =>
    cases hMv : operandMovedLocal? rhs with
    | none =>
      rw [hMv] at hr
      injection hr with hr
      subst hr
      rw [hNone hMv]
      exact hSrc r0 rfl
    | some l =>
      rw [hMv] at hr
      dsimp only at hr
      cases hEqRL : Nat.beq r0 l with
      | true => rw [hEqRL] at hr; nomatch hr
      | false =>
        rw [hEqRL] at hr
        injection hr with hr
        subst hr
        cases hSome l hMv with
        | intro newCs hSet =>
          rw [localUintNat?_set?_ne u hSet
            (fun hE => nat_ne_of_beq_false hEqRL hE.symm)]
          exact hSrc r0 rfl

/-- A denoted unsigned (or, through `mirAbsVal_sint_denote_iff`, signed)
operand value is a scalar of the type's byte width. -/
theorem mirAbsVal_uint_denote_scalar {locals : List LocalSlot} {u : UintTy}
    {a : AbsVal} {src : Option Nat} {v : Value}
    (h : (MirAbsVal.uint u a src).denote locals v) :
    ∃ x, v = .scalar ⟨x, uintBytes u⟩ ∧ a.isInit = true ∧
      a.denote (uintWidth u) (some x) ∧
      ∀ r, src = some r → localUintNat? locals r u = some x := by
  cases v with
  | scalar sc =>
    cases sc with
    | mk x sz =>
      have hSz : sz = uintBytes u := h.2.1
      subst hSz
      refine ⟨x, rfl, h.1, h.2.2.1, fun r hr => ?_⟩
      have h2 := h.2.2.2
      rw [hr] at h2
      exact h2
  | _ => exact False.elim h.2

/-- `UnOp.not` on an evaluated operand: boolean negation (negating the
attached guard) and bitwise complement (`AbsVal.bitNot`) on `.uint` /
`.sint`. -/
def unaryNotAbs : MirAbsVal → Option MirAbsVal
  | .bool ba => some (.bool (negBoolAbs ba))
  | .uint u a _ => some (mkUintVal u (AbsVal.bitNot (uintWidth u) a))
  | .sint i a _ =>
    some (mkSintVal i (AbsVal.bitNot (uintWidth (intTwin i)) a))
  | _ => none

/-- `UnOp.neg` on an evaluated operand: two's-complement wrapping negation
(`0 - x` modulo `2^w`, so `iN::MIN` maps to itself) on `.sint` only. Negation
of an unsigned operand is not valid Rust and has no abstract successor. -/
def unaryNegAbs : MirAbsVal → Option MirAbsVal
  | .sint i a _ =>
    some (mkSintVal i (AbsVal.subWrap (uintWidth (intTwin i))
      (AbsVal.const (uintWidth (intTwin i)) 0) a))
  | _ => none

/-- Abstract `CastKind.intToInt` of an evaluated `uint` / `bool` / `sint`
operand to an integer type of twin width `uDst`. -/
def castSrcAbs (uDst : UintTy) : MirAbsVal → Option AbsVal
  | .uint uSrc a _ => some (castUintAbs uSrc uDst a)
  | .bool ba => some (boolToUintAbs uDst ba)
  | .sint iSrc a _ => some (sintCastAbs iSrc uDst a)
  | _ => none

/-- Checked-arithmetic tuple `(integer, bool)` built from two evaluated
operands. -/
def pairAbs : MirAbsVal → MirAbsVal → Option MirAbsVal
  | .uint u a _, .bool ov =>
    match ov.isInit with
    | true => some (.uintBoolPair u a ov)
    | false => none
  | .sint i a _, .bool ov =>
    match ov.isInit with
    | true => some (.sintBoolPair i a ov)
    | false => none
  | _, _ => none

/-- Abstract `BinOp` transfer on two evaluated operands (`rhs` is the
right-hand operand expression, whose `Move` invalidates the left source
register and guards). Shifts accept mixed widths and signedness; every other
operator requires equal operand types. -/
def binOpAbs (op : BinOp) (rhs : Operand) :
    MirAbsVal → MirAbsVal → Option MirAbsVal
  | .uint u1 a1 srcL, .uint u2 a2 srcR =>
    binOpUintAbs op u1 a1 (srcAfterRhs rhs srcL) u2 a2 srcR
  | .uint u1 a1 _, .sint i2 a2 _ =>
    match binOpIsShift op with
    | true => binOpUintAbs op u1 a1 none (intTwin i2) a2 none
    | false => none
  | .bool ba1, .bool ba2 =>
    match binOpBoolAbs op
        (match operandMovedLocal? rhs with
         | some l => ba1.clearGuardIf l
         | none => ba1) ba2 with
    | some baOut => some (.bool baOut)
    | none => none
  | .sint i1 a1 srcL, .sint i2 a2 srcR =>
    match binOpIsShift op with
    | true => shiftSintAbs op i1 a1 (intTwin i2) a2
    | false =>
      match intTyBeq i1 i2 with
      | true => binOpSintAbs op i1 a1 (srcAfterRhs rhs srcL) a2 srcR
      | false => none
  | .sint i1 a1 _, .uint u2 a2 _ =>
    match binOpIsShift op with
    | true => shiftSintAbs op i1 a1 u2 a2
    | false => none
  | _, _ => none

/-- Abstract rvalue evaluation: `use`, `copyForDeref`, `UnOp.not`
(`unaryNotAbs`), signed `UnOp.neg` (`unaryNegAbs`), `CastKind.intToInt`
between `uint` / `bool` / `sint` sources and `uint` / `sint` targets
(`castSrcAbs`), unsigned, signed, and boolean binary operations (`binOpAbs`),
and `()` / `(integer, bool)` tuple aggregates (`pairAbs`). -/
def evalRvalueAbs (env : MirAbsEnv) : Rvalue → Option (MirAbsVal × MirAbsEnv)
  | .use op => evalOperandAbs env op
  | .copyForDeref p => evalOperandAbs env (.copy p)
  | .unaryOp .not op =>
    match evalOperandAbs env op with
    | some (av, env₁) =>
      match unaryNotAbs av with
      | some r => some (r, env₁)
      | none => none
    | none => none
  | .unaryOp .neg op =>
    match evalOperandAbs env op with
    | some (av, env₁) =>
      match unaryNegAbs av with
      | some r => some (r, env₁)
      | none => none
    | none => none
  | .cast .intToInt op targetTy =>
    match evalOperandAbs env op with
    | some (av, env₁) =>
      match rigidTyToAi? targetTy.kind with
      | some (.uint uDst) =>
        match castSrcAbs uDst av with
        | some a => some (mkUintVal uDst a, env₁)
        | none => none
      | some (.int iDst) =>
        match castSrcAbs (intTwin iDst) av with
        | some a => some (mkSintVal iDst a, env₁)
        | none => none
      | _ => none
    | none => none
  | .aggregate .tuple [] => some (.unit, env)
  | .aggregate .tuple [op0, op1] =>
    match evalOperandAbs env op0 with
    | some (av0, env₁) =>
      match evalOperandAbs env₁ op1 with
      | some (av1, env₂) =>
        match pairAbs av0 av1 with
        | some av => some (av, env₂)
        | none => none
      | none => none
    | none => none
  | .binaryOp op lhs rhs =>
    match evalOperandAbs env lhs with
    | some (av1, env₁) =>
      match evalOperandAbs env₁ rhs with
      | some (av2, env₂) =>
        match binOpAbs op rhs av1 av2 with
        | some av => some (av, env₂)
        | none => none
      | none => none
    | none => none
  | _ => none

theorem evalOperandAbs_not_deref {env : MirAbsEnv} {op : Operand}
    {r : MirAbsVal × MirAbsEnv} (h : evalOperandAbs env op = some r) :
    ∀ p rest, (op = .copy p ∨ op = .move p) → p.projection ≠ .deref :: rest := by
  intro p rest hp hProj
  cases hp with
  | inl hc =>
    subst hc
    cases p with
    | mk l proj =>
      have hProj : proj = .deref :: rest := hProj
      subst hProj
      nomatch h
  | inr hm =>
    subst hm
    cases p with
    | mk l proj =>
      have hProj : proj = .deref :: rest := hProj
      subst hProj
      nomatch h

theorem evalOperandAbs_not_opaqueCast_move {env : MirAbsEnv} {op : Operand}
    {r : MirAbsVal × MirAbsEnv} (h : evalOperandAbs env op = some r) :
    operandIsLeadingOpaqueCastMove op = false := by
  cases op with
  | constant _ => rfl
  | copy _ => rfl
  | move p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil => rfl
      | cons pe rest =>
        cases pe with
        | field _ _ => rfl
        | _ => nomatch h

theorem validateLoadedValue_ok {layouts : LayoutTable} {decls : List LocalDecl}
    {op : Operand} {v : Value} {av : MirAbsVal} {locals : List LocalSlot}
    (hDen : av.denote locals v)
    (hTy : ∃ ty, operandTy decls layouts op = some ty ∧ av.kindOk ty.kind) :
    validateLoadedValue layouts decls op v = true := by
  cases hTy with
  | intro ty hty =>
    cases op with
    | constant c => rfl
    | copy p =>
      unfold validateLoadedValue
      dsimp only
      rw [hty.1]
      dsimp only
      cases av with
      | uint u a src => rw [show ty.kind = .uint u from hty.2]
      | bool ba =>
        rw [show ty.kind = .bool from hty.2]
        cases boolAbs_denote_some hDen with
        | intro b hb =>
          rw [hb.1]
          cases b <;> rfl
      | unit => rw [show ty.kind = .tuple [] from hty.2]
      | uintBoolPair u a ov =>
        rw [show ty.kind = .tuple [.uint u, .bool] from hty.2]
      | sint i a src => rw [show ty.kind = .int i from hty.2]
      | sintBoolPair i a ov =>
        rw [show ty.kind = .tuple [.int i, .bool] from hty.2]
    | move p =>
      unfold validateLoadedValue
      dsimp only
      rw [hty.1]
      dsimp only
      cases av with
      | uint u a src => rw [show ty.kind = .uint u from hty.2]
      | bool ba =>
        rw [show ty.kind = .bool from hty.2]
        cases boolAbs_denote_some hDen with
        | intro b hb =>
          rw [hb.1]
          cases b <;> rfl
      | unit => rw [show ty.kind = .tuple [] from hty.2]
      | uintBoolPair u a ov =>
        rw [show ty.kind = .tuple [.uint u, .bool] from hty.2]
      | sint i a src => rw [show ty.kind = .int i from hty.2]
      | sintBoolPair i a ov =>
        rw [show ty.kind = .tuple [.int i, .bool] from hty.2]

theorem operandIsSigned_of_ty {decls : List LocalDecl} {op : Operand}
    {layouts : LayoutTable} {ty : Ty}
    (hTy : operandTy decls layouts op = some ty) :
    operandIsSigned decls op layouts = tyIsSigned ty := by
  unfold operandIsSigned
  rw [hTy]

theorem operandIsSigned_of_kind {decls : List LocalDecl} {op : Operand}
    {layouts : LayoutTable} {ty : Ty}
    (hTy : operandTy decls layouts op = some ty)
    (hK : tyIsSigned ty = false) :
    operandIsSigned decls op layouts = false := by
  rw [operandIsSigned_of_ty hTy]
  exact hK

theorem operandIsSigned_of_kind_true {decls : List LocalDecl} {op : Operand}
    {layouts : LayoutTable} {ty : Ty}
    (hTy : operandTy decls layouts op = some ty)
    (hK : tyIsSigned ty = true) :
    operandIsSigned decls op layouts = true := by
  rw [operandIsSigned_of_ty hTy]
  exact hK

theorem tyIsSigned_of_uint {ty : Ty} {u : UintTy} (h : ty.kind = .uint u) :
    tyIsSigned ty = false := by
  unfold tyIsSigned
  rw [h]

theorem tyIsSigned_of_bool {ty : Ty} (h : ty.kind = .bool) :
    tyIsSigned ty = false := by
  unfold tyIsSigned
  rw [h]

theorem tyIsSigned_of_int {ty : Ty} {i : IntTy} (h : ty.kind = .int i) :
    tyIsSigned ty = true := by
  unfold tyIsSigned
  rw [h]

/-- `evalRvalue` on a binary operation over two scalar operands is
`evalScalarBinOp` for every operator other than `offset`. -/
theorem evalRvalue_binaryOp_scalar {locals locals₁ locals₂ : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op : BinOp} {lhsOp rhsOp : Operand} {lhs rhs : ScalarInt}
    (hNe : op ≠ .offset)
    (hL : evalOperand locals lhsOp mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok (.scalar lhs) locals₁)
    (hR : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok (.scalar rhs) locals₂) :
    evalRvalue locals (.binaryOp op lhsOp rhsOp) mem decls layouts =
      evalScalarBinOp op lhs rhs locals₂ mem
        (operandIsSigned decls lhsOp layouts) := by
  conv => lhs; whnf
  rw [hL]
  conv => lhs; whnf
  rw [hR]
  cases op with
  | offset => exact absurd rfl hNe
  | _ => rfl

/-- `evalRvalue` on `use op` for an operand that is not a dereference. -/
theorem evalRvalue_use_no_deref {locals locals' : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {v : Value}
    (hEv : evalOperand locals op mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok v locals')
    (hVal : validateLoadedValue layouts decls op v = true)
    (hNoDeref : ∀ p rest, (op = .copy p ∨ op = .move p) →
      p.projection ≠ .deref :: rest) :
    evalRvalue locals (.use op) mem decls layouts = .ok v locals' mem := by
  conv => lhs; whnf
  rw [hEv]
  conv => lhs; whnf
  rw [hVal]
  cases op with
  | constant _ => rfl
  | copy p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil => rfl
      | cons pe rest =>
        cases pe with
        | deref => exact False.elim (hNoDeref _ _ (Or.inl rfl) rfl)
        | _ => rfl
  | move p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil => rfl
      | cons pe rest =>
        cases pe with
        | deref => exact False.elim (hNoDeref _ _ (Or.inr rfl) rfl)
        | _ => rfl

/-- `evalRvalue` on `copyForDeref p` for a place that is not a dereference. -/
theorem evalRvalue_copyForDeref_no_deref {locals locals' : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {p : Place} {v : Value}
    (hEv : evalOperand locals (.copy p) mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok v locals')
    (hNoDeref : ∀ rest, p.projection ≠ .deref :: rest) :
    evalRvalue locals (.copyForDeref p) mem decls layouts =
      .ok v locals' mem := by
  conv => lhs; whnf
  rw [hEv]
  cases p with
  | mk l proj =>
    cases proj with
    | nil => rfl
    | cons pe rest =>
      cases pe with
      | deref => exact False.elim (hNoDeref rest rfl)
      | _ => rfl

/-- `evalRvalue` on `UnOp.not` of a scalar operand is `evalUnaryNot`. -/
theorem evalRvalue_unaryOp_not_scalar {locals locals' : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {sc : ScalarInt}
    (hEv : evalOperand locals op mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok (.scalar sc) locals') :
    evalRvalue locals (.unaryOp .not op) mem decls layouts =
      evalUnaryNot sc (operandTy decls layouts op) locals' mem := by
  conv => lhs; whnf
  rw [hEv]

/-- `evalRvalue` on `UnOp.neg` of an in-range integer scalar is two's
complement wrapping negation. -/
theorem evalRvalue_unaryOp_neg_scalar {locals locals' : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {u : UintTy} {x : Nat}
    (hEv : evalOperand locals op mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack =
        .ok (.scalar ⟨x, uintBytes u⟩) locals')
    (hx : x < modPow2 (uintWidth u)) :
    evalRvalue locals (.unaryOp .neg op) mem decls layouts =
      .ok (.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) - x),
        uintBytes u⟩) locals' mem := by
  conv => lhs; whnf
  rw [hEv]
  conv => lhs; whnf
  rw [uintBytes_beq_zero]
  conv => lhs; whnf
  rw [wrapScalarBits_of_lt_uint hx, wrapScalarBits_eq_wrapVal,
    scalarModulus_uintBytes]
  rfl

/-- `evalRvalue` on `CastKind.intToInt` of an integer scalar of width `uSrc`
to a target of byte width `uintBytes uDst` produces `intCastBits`. -/
theorem evalRvalue_cast_intToInt_scalar {locals locals' : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {targetTy : Ty} {uSrc uDst : UintTy} {x : Nat}
    (hEv : evalOperand locals op mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack =
        .ok (.scalar ⟨x, uintBytes uSrc⟩) locals')
    (hTgt : intCastTargetBytes targetTy.kind = some (uintBytes uDst)) :
    evalRvalue locals (.cast .intToInt op targetTy) mem decls layouts =
      .ok (.scalar ⟨intCastBits (operandIsSigned decls op layouts) uSrc uDst x,
        uintBytes uDst⟩) locals' mem := by
  conv => lhs; whnf
  rw [hEv]
  conv => lhs; whnf
  rw [uintBytes_beq_zero]
  conv => lhs; whnf
  rw [hTgt]
  rfl

/-- `evalRvalue` on a two-element tuple aggregate. -/
theorem evalRvalue_tuple_pair {locals locals₁ locals₂ : List LocalSlot}
    {mem : Memory} {decls : List LocalDecl} {layouts : LayoutTable}
    {op0 op1 : Operand} {v0 v1 : Value}
    (hEv0 : evalOperand locals op0 mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok v0 locals₁)
    (hEv1 : evalOperand locals₁ op1 mem.borrows mem.globals layouts
      mem.callerLocals decls mem.callStack = .ok v1 locals₂) :
    evalRvalue locals (.aggregate .tuple [op0, op1]) mem decls layouts =
      .ok (.aggregate 0 [v0, v1]) locals₂ mem := by
  conv => lhs; whnf
  simp only [evalOperands, hEv0, hEv1]

theorem unaryNotAbs_sound {av r : MirAbsVal} {locals : List LocalSlot}
    {v : Value} {ty : Ty} (mem : Memory)
    (h : unaryNotAbs av = some r) (hD : av.denote locals v)
    (hK : av.kindOk ty.kind) :
    ∃ sc v', v = .scalar sc ∧
      evalUnaryNot sc (some ty) locals mem = .ok v' locals mem ∧
      r.denote locals v' := by
  cases av with
  | bool ba =>
    injection h with h
    subst h
    cases boolAbs_denote_some hD with
    | intro b hb =>
      exact ⟨_, _, hb.1, evalUnaryNot_bool locals mem hK b,
        boolAbs_denote_of_bool (negBoolAbs_sound hb.2)⟩
  | uint u a src =>
    injection h with h
    subst h
    cases mirAbsVal_uint_denote_scalar hD with
    | intro x hx =>
      have hxLt := (absVal_some_elim hx.2.2.1).1
      have hXor := absVal_bitNot_sound (uintWidth_valid u) hx.2.2.1 hx.2.1
      rw [nat_xor_mask_eq_sub hxLt] at hXor
      exact ⟨_, _, hx.1, evalUnaryNot_uint locals mem hK hxLt,
        mkUintVal_denote hXor⟩
  | sint i a src =>
    injection h with h
    subst h
    cases mirAbsVal_uint_denote_scalar (u := intTwin i) hD with
    | intro x hx =>
      have hxLt := (absVal_some_elim hx.2.2.1).1
      have hXor := absVal_bitNot_sound (uintWidth_valid (intTwin i)) hx.2.2.1
        hx.2.1
      rw [nat_xor_mask_eq_sub hxLt] at hXor
      exact ⟨_, _, hx.1, evalUnaryNot_int locals mem hK hxLt,
        mkSintVal_denote hXor⟩
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

theorem unaryNegAbs_sound {av r : MirAbsVal} {locals : List LocalSlot}
    {v : Value} (h : unaryNegAbs av = some r) (hD : av.denote locals v) :
    ∃ u x, v = .scalar ⟨x, uintBytes u⟩ ∧ x < modPow2 (uintWidth u) ∧
      r.denote locals (.scalar ⟨wrapVal (uintWidth u)
        (modPow2 (uintWidth u) - x), uintBytes u⟩) := by
  cases av with
  | sint i a src =>
    injection h with h
    subst h
    cases mirAbsVal_uint_denote_scalar (u := intTwin i) hD with
    | intro x hx =>
      have hw := uintWidth_valid (intTwin i)
      have hSub := absVal_subWrap_sound hw
        (absVal_const_denote_lt hw (modPow2_pos _)) hx.2.2.1
        (absVal_const_isInit hw) hx.2.1
      rw [Nat.add_zero] at hSub
      exact ⟨intTwin i, x, hx.1, (absVal_some_elim hx.2.2.1).1,
        mkSintVal_denote hSub⟩
  | uint _ _ _ => nomatch h
  | bool _ => nomatch h
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

theorem castSrcAbs_sound {uDst : UintTy} {av : MirAbsVal} {a : AbsVal}
    {locals : List LocalSlot} {v : Value} {ty : Ty}
    (h : castSrcAbs uDst av = some a) (hD : av.denote locals v)
    (hK : av.kindOk ty.kind) :
    ∃ uSrc x, v = .scalar ⟨x, uintBytes uSrc⟩ ∧
      a.denote (uintWidth uDst)
        (some (intCastBits (tyIsSigned ty) uSrc uDst x)) := by
  cases av with
  | uint uSrc a0 src =>
    injection h with h
    subst h
    cases mirAbsVal_uint_denote_scalar hD with
    | intro x hx =>
      refine ⟨uSrc, x, hx.1, ?_⟩
      rw [tyIsSigned_of_uint hK, intCastBits_wrap x (Or.inl rfl)]
      exact castUintAbs_sound hx.2.1 hx.2.2.1
  | bool ba =>
    injection h with h
    subst h
    cases boolAbs_denote_some hD with
    | intro b hb =>
      have hbLt : (boolToScalar b).bits < modPow2 (uintWidth uDst) :=
        Nat.lt_of_le_of_lt (boolToScalar_bits_le_one b)
          (one_lt_modPow2_uint uDst)
      refine ⟨.u8, (boolToScalar b).bits,
        Eq.trans hb.1 (by cases b <;> rfl), ?_⟩
      rw [tyIsSigned_of_bool hK, intCastBits_wrap _ (Or.inl rfl),
        wrapVal_of_lt hbLt]
      exact boolToUintAbs_sound hb.2
  | sint iSrc a0 src =>
    injection h with h
    subst h
    cases mirAbsVal_uint_denote_scalar (u := intTwin iSrc) hD with
    | intro x hx =>
      refine ⟨intTwin iSrc, x, hx.1, ?_⟩
      rw [tyIsSigned_of_int hK]
      exact sintCastAbs_sound hx.2.1 hx.2.2.1
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

theorem pairAbs_sound {av0 av1 av : MirAbsVal} {locals₁ locals₂ : List LocalSlot}
    {v0 v1 : Value} (h : pairAbs av0 av1 = some av)
    (hD0 : av0.denote locals₁ v0) (hD1 : av1.denote locals₂ v1) :
    av.denote locals₂ (.aggregate 0 [v0, v1]) := by
  cases av0 with
  | uint u a src =>
    cases av1 with
    | bool ov =>
      unfold pairAbs at h
      dsimp only at h
      cases hOvI : ov.isInit with
      | false => rw [hOvI] at h; nomatch h
      | true =>
        rw [hOvI] at h
        injection h with h
        subst h
        cases mirAbsVal_uint_denote_scalar hD0 with
        | intro x hx =>
          have e := hx.1
          subst e
          exact ⟨hx.2.1, hOvI, rfl, hx.2.2.1, hD1⟩
    | _ => nomatch h
  | sint i a src =>
    cases av1 with
    | bool ov =>
      unfold pairAbs at h
      dsimp only at h
      cases hOvI : ov.isInit with
      | false => rw [hOvI] at h; nomatch h
      | true =>
        rw [hOvI] at h
        injection h with h
        subst h
        cases mirAbsVal_uint_denote_scalar (u := intTwin i) hD0 with
        | intro x hx =>
          have e := hx.1
          subst e
          exact ⟨hx.2.1, hOvI, rfl, hx.2.2.1, hD1⟩
    | _ => nomatch h
  | bool _ => nomatch h
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

/-- Scalar-level soundness of `binOpAbs`: both operand values are scalars,
the operator is not `offset`, and `evalScalarBinOp` (signed iff the left
operand type is) succeeds with a value denoted by the abstract result. -/
theorem binOpAbs_sound {op : BinOp} {rhs : Operand} {av1 av2 av : MirAbsVal}
    {locals₁ locals₂ : List LocalSlot} {v1 v2 : Value} {ty1 : Ty}
    (mem : Memory) (h : binOpAbs op rhs av1 av2 = some av)
    (hD1 : av1.denote locals₁ v1) (hD2 : av2.denote locals₂ v2)
    (hK : av1.kindOk ty1.kind)
    (hNone : operandMovedLocal? rhs = none → locals₂ = locals₁)
    (hSome : ∀ l, operandMovedLocal? rhs = some l →
      ∃ newCs, set? locals₁ l newCs = some locals₂) :
    op ≠ .offset ∧ ∃ sc1 sc2 v, v1 = .scalar sc1 ∧ v2 = .scalar sc2 ∧
      evalScalarBinOp op sc1 sc2 locals₂ mem (tyIsSigned ty1) =
        .ok v locals₂ mem ∧
      av.denote locals₂ v := by
  cases av1 with
  | uint u1 a1 srcL =>
    rw [tyIsSigned_of_uint hK]
    cases av2 with
    | uint u2 a2 srcR =>
      cases mirAbsVal_uint_denote_scalar hD1 with
      | intro x hx =>
        cases mirAbsVal_uint_denote_scalar hD2 with
        | intro y hy =>
          cases binOpUintAbs_sound mem h hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1
              (srcAfterRhs_sound hx.2.2.2 hNone hSome) hy.2.2.2 with
          | intro v hv =>
            exact ⟨binOpUintAbs_not_offset h, _, _, v, hx.1, hy.1, hv.1, hv.2⟩
    | sint i2 a2 srcR =>
      dsimp only [binOpAbs] at h
      cases hSh : binOpIsShift op with
      | false => rw [hSh] at h; nomatch h
      | true =>
        rw [hSh] at h; dsimp only at h
        cases mirAbsVal_uint_denote_scalar hD1 with
        | intro x hx =>
          cases mirAbsVal_uint_denote_scalar (u := intTwin i2) hD2 with
          | intro y hy =>
            cases binOpUintAbs_sound mem h hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1
                (fun _ hr => nomatch hr) (fun _ hr => nomatch hr) with
            | intro v hv =>
              exact ⟨binOpUintAbs_not_offset h, _, _, v, hx.1, hy.1, hv.1, hv.2⟩
    | _ => nomatch h
  | bool ba1 =>
    cases av2 with
    | bool ba2 =>
      dsimp only [binOpAbs] at h
      cases hB : binOpBoolAbs op
          (match operandMovedLocal? rhs with
           | some l => ba1.clearGuardIf l
           | none => ba1) ba2 with
      | none => rw [hB] at h; nomatch h
      | some baOut =>
        rw [hB] at h; cases h
        have hBa1' : (match operandMovedLocal? rhs with
            | some l => ba1.clearGuardIf l
            | none => ba1).denote locals₂ (some v1) := by
          cases hMv : operandMovedLocal? rhs with
          | none => rw [hNone hMv]; exact hD1
          | some l =>
            cases hSome l hMv with
            | intro newCs hSet => exact boolAbs_clearGuardIf_denote_update hSet hD1
        cases boolAbs_denote_some hBa1' with
        | intro c1 hc1 =>
          cases boolAbs_denote_some hD2 with
          | intro c2 hc2 =>
            rw [tyIsSigned_of_bool hK]
            cases binOpBoolAbs_sound mem hB hc1.2 hc2.2 with
            | intro v hv =>
              exact ⟨binOpBoolAbs_not_offset hB, _, _, v, hc1.1, hc2.1, hv.1, hv.2⟩
    | _ => nomatch h
  | sint i1 a1 srcL =>
    rw [tyIsSigned_of_int hK]
    cases av2 with
    | sint i2 a2 srcR =>
      dsimp only [binOpAbs] at h
      cases mirAbsVal_uint_denote_scalar (u := intTwin i1) hD1 with
      | intro x hx =>
        cases mirAbsVal_uint_denote_scalar (u := intTwin i2) hD2 with
        | intro y hy =>
          cases hSh : binOpIsShift op with
          | true =>
            rw [hSh] at h; dsimp only at h
            cases shiftSintAbs_sound mem h hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1 with
            | intro v hv =>
              exact ⟨shiftSintAbs_not_offset h, _, _, v, hx.1, hy.1, hv.1, hv.2⟩
          | false =>
            rw [hSh] at h; dsimp only at h
            cases hII : intTyBeq i1 i2 with
            | false => rw [hII] at h; nomatch h
            | true =>
              rw [hII] at h; dsimp only at h
              have hi := intTy_eq_of_beq hII; subst hi
              cases binOpSintAbs_sound mem h hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1
                  (srcAfterRhs_sound hx.2.2.2 hNone hSome) hy.2.2.2 with
              | intro v hv =>
                exact ⟨binOpSintAbs_not_offset h, _, _, v, hx.1, hy.1, hv.1, hv.2⟩
    | uint u2 a2 srcR =>
      dsimp only [binOpAbs] at h
      cases hSh : binOpIsShift op with
      | false => rw [hSh] at h; nomatch h
      | true =>
        rw [hSh] at h; dsimp only at h
        cases mirAbsVal_uint_denote_scalar (u := intTwin i1) hD1 with
        | intro x hx =>
          cases mirAbsVal_uint_denote_scalar hD2 with
          | intro y hy =>
            cases shiftSintAbs_sound mem h hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1 with
            | intro v hv =>
              exact ⟨shiftSintAbs_not_offset h, _, _, v, hx.1, hy.1, hv.1, hv.2⟩
    | _ => nomatch h
  | unit => nomatch h
  | uintBoolPair _ _ _ => nomatch h
  | sintBoolPair _ _ _ => nomatch h

/-- Soundness of `evalRvalueAbs` against `evalRvalue` (memory is unchanged on
every supported rvalue). -/
theorem evalRvalueAbs_sound {decls : List LocalDecl} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {rv : Rvalue} {av : MirAbsVal}
    (mem : Memory) (layouts : LayoutTable)
    (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalRvalueAbs env rv = some (av, env')) :
    ∃ v locals', evalRvalue locals rv mem decls layouts = .ok v locals' mem ∧
      av.denote locals' v ∧ mirAbsEnvDenote decls env' locals' := by
  cases rv with
  | use op =>
    have hAbs : evalOperandAbs env op = some (av, env') := hAbs
    cases evalOperandAbs_sound hEnv hAbs with
    | intro v hv =>
      cases hv with
      | intro locals' hv =>
        exact ⟨v, locals', evalRvalue_use_no_deref
          (hv.1 mem.borrows mem.globals layouts mem.callerLocals decls
            mem.callStack (Or.inl rfl))
          (validateLoadedValue_ok (layouts := layouts) hv.2.1
            (hv.2.2.2.2.2 layouts))
          (evalOperandAbs_not_deref hAbs), hv.2.1, hv.2.2.1⟩
  | copyForDeref p =>
    have hAbs : evalOperandAbs env (.copy p) = some (av, env') := hAbs
    cases evalOperandAbs_sound hEnv hAbs with
    | intro v hv =>
      cases hv with
      | intro locals' hv =>
        exact ⟨v, locals', evalRvalue_copyForDeref_no_deref
          (hv.1 mem.borrows mem.globals layouts mem.callerLocals decls
            mem.callStack (Or.inl rfl))
          (fun rest => evalOperandAbs_not_deref hAbs p rest (Or.inl rfl)),
          hv.2.1, hv.2.2.1⟩
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueAbs] at hAbs
      cases hO : evalOperandAbs env op with
      | none => rw [hO] at hAbs; nomatch hAbs
      | some r0 =>
        rw [hO] at hAbs; cases r0 with | mk av1 env₁ =>
        dsimp only at hAbs
        cases hU : unaryNotAbs av1 with
        | none => rw [hU] at hAbs; nomatch hAbs
        | some r =>
          rw [hU] at hAbs; cases hAbs
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              cases hv.2.2.2.2.2 layouts with
              | intro ty hty =>
                cases unaryNotAbs_sound mem hU hv.2.1 hty.2 with
                | intro sc hs =>
                  cases hs with
                  | intro v' hs =>
                    have e := hs.1; subst e
                    have hEval := evalRvalue_unaryOp_not_scalar
                      (hv.1 mem.borrows mem.globals layouts mem.callerLocals
                        decls mem.callStack (Or.inl rfl))
                    rw [hty.1] at hEval
                    exact ⟨v', locals', Eq.trans hEval hs.2.1, hs.2.2, hv.2.2.1⟩
    | neg =>
      dsimp only [evalRvalueAbs] at hAbs
      cases hO : evalOperandAbs env op with
      | none => rw [hO] at hAbs; nomatch hAbs
      | some r0 =>
        rw [hO] at hAbs; cases r0 with | mk av1 env₁ =>
        dsimp only at hAbs
        cases hU : unaryNegAbs av1 with
        | none => rw [hU] at hAbs; nomatch hAbs
        | some r =>
          rw [hU] at hAbs; cases hAbs
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              cases unaryNegAbs_sound hU hv.2.1 with
              | intro u hs =>
                cases hs with
                | intro x hs =>
                  have e := hs.1; subst e
                  exact ⟨_, locals', evalRvalue_unaryOp_neg_scalar
                    (hv.1 mem.borrows mem.globals layouts mem.callerLocals
                      decls mem.callStack (Or.inl rfl)) hs.2.1, hs.2.2, hv.2.2.1⟩
    | ptrMetadata => nomatch hAbs
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      dsimp only [evalRvalueAbs] at hAbs
      cases hO : evalOperandAbs env op with
      | none => rw [hO] at hAbs; nomatch hAbs
      | some r0 =>
        rw [hO] at hAbs; cases r0 with | mk av1 env₁ =>
        dsimp only at hAbs
        cases evalOperandAbs_sound hEnv hO with
        | intro v hv =>
          cases hv with
          | intro locals' hv =>
            cases hv.2.2.2.2.2 layouts with
            | intro ty hty =>
              have hGo : ∀ (uDst : UintTy) (a : AbsVal) (avOut : MirAbsVal),
                  intCastTargetBytes targetTy.kind = some (uintBytes uDst) →
                  castSrcAbs uDst av1 = some a →
                  (∀ bits, a.denote (uintWidth uDst) (some bits) →
                    avOut.denote locals' (.scalar ⟨bits, uintBytes uDst⟩)) →
                  ∃ v', evalRvalue locals (.cast .intToInt op targetTy) mem
                      decls layouts = .ok v' locals' mem ∧
                    avOut.denote locals' v' := by
                intro uDst a avOut hTgt hC hOut
                cases castSrcAbs_sound hC hv.2.1 hty.2 with
                | intro uSrc hs =>
                  cases hs with
                  | intro x hs =>
                    have e := hs.1; subst e
                    have hEval := evalRvalue_cast_intToInt_scalar
                      (hv.1 mem.borrows mem.globals layouts mem.callerLocals
                        decls mem.callStack (Or.inl rfl)) hTgt
                    rw [operandIsSigned_of_ty hty.1] at hEval
                    exact ⟨_, hEval, hOut _ hs.2⟩
              cases hK : rigidTyToAi? targetTy.kind with
              | none => rw [hK] at hAbs; nomatch hAbs
              | some ak =>
                rw [hK] at hAbs
                cases ak with
                | uint uDst =>
                  dsimp only at hAbs
                  cases hC : castSrcAbs uDst av1 with
                  | none => rw [hC] at hAbs; nomatch hAbs
                  | some a =>
                    rw [hC] at hAbs; cases hAbs
                    cases hGo uDst a _
                        (by rw [rigidTyToAi?_eq hK]; exact intCastTargetBytes_uint uDst) hC
                        (fun _ hb => mkUintVal_denote hb) with
                    | intro v' hv' => exact ⟨v', locals', hv'.1, hv'.2, hv.2.2.1⟩
                | int iDst =>
                  dsimp only at hAbs
                  cases hC : castSrcAbs (intTwin iDst) av1 with
                  | none => rw [hC] at hAbs; nomatch hAbs
                  | some a =>
                    rw [hC] at hAbs; cases hAbs
                    cases hGo (intTwin iDst) a _
                        (by rw [rigidTyToAi?_eq hK]; exact intCastTargetBytes_int iDst) hC
                        (fun _ hb => mkSintVal_denote hb) with
                    | intro v' hv' => exact ⟨v', locals', hv'.1, hv'.2, hv.2.2.1⟩
                | bool => nomatch hAbs
                | tuple _ => nomatch hAbs
    | _ => nomatch hAbs
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      cases ops with
      | nil => cases hAbs; exact ⟨.aggregate 0 [], locals, rfl, Or.inr rfl, hEnv⟩
      | cons op0 rest =>
        cases rest with
        | nil => nomatch hAbs
        | cons op1 rest2 =>
          cases rest2 with
          | cons _ _ => nomatch hAbs
          | nil =>
            dsimp only [evalRvalueAbs] at hAbs
            cases hO0 : evalOperandAbs env op0 with
            | none => rw [hO0] at hAbs; nomatch hAbs
            | some r0 =>
              rw [hO0] at hAbs; cases r0 with | mk av0 env₁ =>
              dsimp only at hAbs
              cases hO1 : evalOperandAbs env₁ op1 with
              | none => rw [hO1] at hAbs; nomatch hAbs
              | some r1 =>
                rw [hO1] at hAbs; cases r1 with | mk av1 env₂ =>
                dsimp only at hAbs
                cases hP : pairAbs av0 av1 with
                | none => rw [hP] at hAbs; nomatch hAbs
                | some avP =>
                  rw [hP] at hAbs; cases hAbs
                  cases evalOperandAbs_sound hEnv hO0 with
                  | intro v0 hv0 =>
                    cases hv0 with
                    | intro locals₁ hv0 =>
                      cases evalOperandAbs_sound hv0.2.2.1 hO1 with
                      | intro v1 hv1 =>
                        cases hv1 with
                        | intro locals₂ hv1 =>
                          exact ⟨_, locals₂, evalRvalue_tuple_pair
                            (hv0.1 mem.borrows mem.globals layouts
                              mem.callerLocals decls mem.callStack (Or.inl rfl))
                            (hv1.1 mem.borrows mem.globals layouts
                              mem.callerLocals decls mem.callStack (Or.inl rfl)),
                            pairAbs_sound hP hv0.2.1 hv1.2.1, hv1.2.2.1⟩
    | _ => nomatch hAbs
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalueAbs] at hAbs
    cases hO1 : evalOperandAbs env lhs with
    | none => rw [hO1] at hAbs; nomatch hAbs
    | some r1 =>
      rw [hO1] at hAbs; cases r1 with | mk av1 env₁ =>
      dsimp only at hAbs
      cases hO2 : evalOperandAbs env₁ rhs with
      | none => rw [hO2] at hAbs; nomatch hAbs
      | some r2 =>
        rw [hO2] at hAbs; cases r2 with | mk av2 env₂ =>
        dsimp only at hAbs
        cases hB : binOpAbs op rhs av1 av2 with
        | none => rw [hB] at hAbs; nomatch hAbs
        | some av0 =>
          rw [hB] at hAbs; cases hAbs
          cases evalOperandAbs_sound hEnv hO1 with
          | intro v1 hv1 =>
            cases hv1 with
            | intro locals₁ hv1 =>
              cases evalOperandAbs_sound hv1.2.2.1 hO2 with
              | intro v2 hv2 =>
                cases hv2 with
                | intro locals₂ hv2 =>
                  cases hv1.2.2.2.2.2 layouts with
                  | intro ty1 hty1 =>
                    have hS := binOpAbs_sound mem hB hv1.2.1 hv2.2.1
                      hty1.2 hv2.2.2.2.1 hv2.2.2.2.2.1
                    cases hS.2 with
                    | intro sc1 hs =>
                      cases hs with
                      | intro sc2 hs =>
                        cases hs with
                        | intro v hs =>
                          have e1 := hs.1; have e2 := hs.2.1; subst e1; subst e2
                          have hEval := evalRvalue_binaryOp_scalar hS.1
                            (hv1.1 mem.borrows mem.globals layouts
                              mem.callerLocals decls mem.callStack (Or.inl rfl))
                            (hv2.1 mem.borrows mem.globals layouts
                              mem.callerLocals decls mem.callStack (Or.inl rfl))
                          rw [operandIsSigned_of_ty hty1.1] at hEval
                          exact ⟨v, locals₂, Eq.trans hEval hs.2.2.1,
                            hs.2.2.2, hv2.2.2.1⟩
  | _ => nomatch hAbs

/-! ## 8. Statements -/

/-- Abstract transfer for a single MIR statement. Assignments, `deinit`, and
`placeMention` are supported on unprojected places; `intrinsic (.assume op)`
is certified when `op` evaluates to `true`. -/
def stepStmtAbs (decls : List LocalDecl) (env : MirAbsEnv) (stmt : Statement) :
    Option MirAbsEnv :=
  match stmt.kind with
  | .nop => some env
  | .coverage => some env
  | .constEvalCounter => some env
  | .backwardIncompatibleDropHint _ => some env
  | .placeMention p =>
    match p.projection, get? env p.local_ with
    | [], some sl =>
      match sl.isLive with
      | true => some env
      | false => none
    | _, _ => none
  | .retag _ p =>
    match evalOperandAbs env (.copy p) with
    | some _ => some env
    | none => none
  | .storageLive l =>
    match get? decls l, get? env l with
    | some d, some _ => setMirAbsSlot l (uninitSlotFor d.ty) env
    | _, _ => none
  | .storageDead l =>
    match get? env l with
    | some _ => setMirAbsSlot l .dead env
    | none => none
  | .deinit p =>
    match p.projection, get? decls p.local_, get? env p.local_ with
    | [], some d, some sl =>
      match sl.isLive with
      | true => setMirAbsSlot p.local_ (uninitSlotFor d.ty) env
      | false => none
    | _, _, _ => none
  | .intrinsic (.assume op) =>
    match evalOperandAbs env op with
    | some (.bool (.exact true g), env₁) => some (refineEnvByGuard env₁ g true)
    | _ => none
  | .assign dst rv =>
    match dst.projection, get? decls dst.local_ with
    | [], some d =>
      match evalRvalueAbs env rv with
      | some (av, env₁) =>
        match av.kindMatches d.ty.kind, get? env₁ dst.local_ with
        | true, some sl =>
          match sl.isLive with
          | true => setMirAbsSlot dst.local_ av.toSlot env₁
          | false => none
        | _, _ => none
      | none => none
    | _, _ => none
  | _ => none

/-- Locate a live concrete slot behind a live abstract slot. -/
theorem env_live_lookup {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {i : Nat} {sl : MirAbsSlot}
    (hEnv : mirAbsEnvDenote decls env locals) (hGet : get? env i = some sl)
    (hLive : sl.isLive = true) :
    ∃ d cs, get? decls i = some d ∧ get? locals i = some cs ∧ cs ≠ .dead ∧
      sl.denote d.ty locals cs := by
  cases mirAbsEnv_lookup hEnv hGet with
  | intro d hd =>
    cases hd with
    | intro cs hcs =>
      exact ⟨d, cs, hcs.1, hcs.2.1, mirAbsSlot_live hLive hcs.2.2, hcs.2.2⟩

/-- Non-borrow memory fields preserved by every AI-PCC-supported statement and
terminator (supported scalar/control steps only update `borrows`). -/
def MirMemFrame (m₁ m₂ : Memory) : Prop :=
  m₁.nextAllocId = m₂.nextAllocId ∧
  m₁.globals = m₂.globals ∧
  m₁.nextTag = m₂.nextTag ∧
  m₁.callStack = m₂.callStack ∧
  m₁.activeCallee = m₂.activeCallee ∧
  m₁.activeProtectors = m₂.activeProtectors

/-- `MirMemFrame` is reflexive. -/
theorem MirMemFrame.refl (m : Memory) : MirMemFrame m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `MirMemFrame` is transitive. -/
theorem MirMemFrame.trans {m₁ m₂ m₃ : Memory}
    (h₁ : MirMemFrame m₁ m₂) (h₂ : MirMemFrame m₂ m₃) : MirMemFrame m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
   h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1,
   h₁.2.2.2.2.2.trans h₂.2.2.2.2.2⟩

private theorem evalStmt_placeMention_live {s : MachineState} {span : String}
    {l : Nat} {cs : LocalSlot} {decls : List LocalDecl} {layouts : LayoutTable}
    (hL : get? s.frame.locals l = some cs) (hLive : cs ≠ .dead) :
    evalStmt s ⟨.placeMention ⟨l, []⟩, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals s.memory) := by
  conv => lhs; whnf
  rw [hL]
  cases cs with
  | dead => exact absurd rfl hLive
  | uninit => rfl
  | init _ => rfl

private theorem evalStmt_retag_scalar {s : MachineState} {span : String}
    {rk : RetagKind} {p : Place} {decls : List LocalDecl} {layouts : LayoutTable}
    {sc : ScalarInt} {ty : Ty}
    (hEv : evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals
      layouts s.memory.callerLocals decls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals)
    (hPl : placeTy decls layouts p = some ty)
    (hTy : (∃ u, ty.kind = .uint u) ∨ ty.kind = .bool ∨ (∃ i, ty.kind = .int i)) :
    evalStmt s ⟨.retag rk p, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals s.memory) := by
  conv => lhs; whnf
  rw [hEv]
  conv => lhs; whnf
  rw [hPl]
  cases ty with
  | mk k lIdx =>
    cases hTy with
    | inl hU => cases hU with | intro u hu => subst hu; rfl
    | inr hTy =>
      cases hTy with
      | inl hB => subst hB; rfl
      | inr hI => cases hI with | intro i hi => subst hi; rfl

private theorem evalStmt_retag_tuple {s : MachineState} {span : String}
    {rk : RetagKind} {p : Place} {decls : List LocalDecl} {layouts : LayoutTable}
    {val : Value} {ty : Ty} {ts : List RigidTy}
    (hEv : evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals
      layouts s.memory.callerLocals decls s.memory.callStack = .ok val s.frame.locals)
    (hPl : placeTy decls layouts p = some ty)
    (hTy : ty.kind = .tuple ts)
    (hVal : val = .unit ∨ ∃ tag fs, val = .aggregate tag fs) :
    evalStmt s ⟨.retag rk p, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals s.memory) := by
  conv => lhs; whnf
  rw [hEv]
  conv => lhs; whnf
  rw [hPl]
  cases ty with
  | mk k lIdx =>
    have hk : k = .tuple ts := hTy; subst hk
    cases hVal with
    | inl hUn => subst hUn; rfl
    | inr hA =>
      cases hA with
      | intro tag hA => cases hA with | intro fs ha => subst ha; rfl

private theorem evalStmt_storageLive_noProt {s : MachineState} {span : String}
    {l : Nat} {cs : LocalSlot} {locals' : List LocalSlot}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hL : get? s.frame.locals l = some cs)
    (hSet : set? s.frame.locals l .uninit = some locals')
    (hProt : s.memory.activeProtectors = []) :
    evalStmt s ⟨.storageLive l, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s locals'
        { s.memory with
          borrows := disableLocalBorrows s.memory.borrows l
            (length s.memory.callStack) }) := by
  conv => lhs; whnf
  rw [hL]; (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]

private theorem evalStmt_storageDead_noProt {s : MachineState} {span : String}
    {l : Nat} {cs : LocalSlot} {locals' : List LocalSlot}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hL : get? s.frame.locals l = some cs)
    (hSet : set? s.frame.locals l .dead = some locals')
    (hProt : s.memory.activeProtectors = []) :
    evalStmt s ⟨.storageDead l, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s locals'
        { s.memory with
          borrows := disableLocalBorrows s.memory.borrows l
            (length s.memory.callStack) }) := by
  conv => lhs; whnf
  rw [hL]; (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]

private theorem evalStmt_deinit_local_noProt {s : MachineState} {span : String}
    {l : Nat} {cs : LocalSlot} {locals' : List LocalSlot}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hL : get? s.frame.locals l = some cs) (hLive : cs ≠ .dead)
    (hSet : set? s.frame.locals l .uninit = some locals')
    (hProt : s.memory.activeProtectors = []) :
    evalStmt s ⟨.deinit ⟨l, []⟩, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s locals'
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows l .none
            (length s.memory.callStack) }) := by
  conv => lhs; whnf
  rw [hL]
  cases cs with
  | dead => exact absurd rfl hLive
  | uninit => (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]
  | init _ => (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]

private theorem evalStmt_assume_true {s : MachineState} {span : String}
    {op : Operand} {locals' : List LocalSlot}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hEv : evalOperand s.frame.locals op s.memory.borrows s.memory.globals
      layouts s.memory.callerLocals decls s.memory.callStack =
        .ok (.scalar (boolToScalar true)) locals') :
    evalStmt s ⟨.intrinsic (.assume op), span⟩ decls layouts =
      MirStepNode.step (advanceStmt s locals' s.memory) := by
  conv => lhs; whnf
  rw [hEv]
  rfl

private theorem evalStmt_assign_local_noProt {s : MachineState} {span : String}
    {l : Nat} {rv : Rvalue} {val : Value} {cs : LocalSlot}
    {locals₁ locals₂ : List LocalSlot}
    {decls : List LocalDecl} {layouts : LayoutTable}
    (hEv : evalRvalue s.frame.locals rv s.memory decls layouts =
      .ok val locals₁ s.memory)
    (hL : get? locals₁ l = some cs) (hLive : cs ≠ .dead)
    (hSet : set? locals₁ l (.init val) = some locals₂)
    (hProt : s.memory.activeProtectors = []) :
    evalStmt s ⟨.assign ⟨l, []⟩ rv, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s locals₂
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows l .none
            (length s.memory.callStack) }) := by
  conv => lhs; whnf
  rw [hEv]; (conv => lhs; whnf); rw [hL]
  cases cs with
  | dead => exact absurd rfl hLive
  | uninit =>
    (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); dsimp only; rw [hProt]
  | init _ =>
    (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); dsimp only; rw [hProt]

/-- One-step soundness of `stepStmtAbs` against `evalStmt` from a frame with
no active function-entry protectors. The successor frame advances `stmtIdx`,
and `MirMemFrame` is preserved. -/
theorem stepStmtAbs_sound {decls : List LocalDecl} {layouts : LayoutTable}
    {env env' : MirAbsEnv} {s : MachineState} {stmt : Statement}
    (hEnv : mirAbsEnvDenote decls env s.frame.locals)
    (hProt : s.memory.activeProtectors = [])
    (hStep : stepStmtAbs decls env stmt = some env') :
    ∃ locals' mem',
      evalStmt s stmt decls layouts = MirStepNode.step (advanceStmt s locals' mem') ∧
      MirMemFrame mem' s.memory ∧
      mirAbsEnvDenote decls env' locals' := by
  cases stmt with
  | mk kind span =>
    cases kind with
    | nop =>
      cases hStep
      exact ⟨s.frame.locals, s.memory, rfl, MirMemFrame.refl _, hEnv⟩
    | coverage =>
      cases hStep
      exact ⟨s.frame.locals, s.memory, rfl, MirMemFrame.refl _, hEnv⟩
    | constEvalCounter =>
      cases hStep
      exact ⟨s.frame.locals, s.memory, rfl, MirMemFrame.refl _, hEnv⟩
    | backwardIncompatibleDropHint _ =>
      cases hStep
      exact ⟨s.frame.locals, s.memory, rfl, MirMemFrame.refl _, hEnv⟩
    | placeMention p =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          dsimp only [stepStmtAbs] at hStep
          cases hS : get? env l with
          | none => rw [hS] at hStep; nomatch hStep
          | some sl =>
            rw [hS] at hStep; dsimp only at hStep
            cases hLv : sl.isLive with
            | false => rw [hLv] at hStep; nomatch hStep
            | true =>
              rw [hLv] at hStep; cases hStep
              cases env_live_lookup hEnv hS hLv with
              | intro d hd =>
                cases hd with
                | intro cs hcs =>
                  exact ⟨s.frame.locals, s.memory,
                    evalStmt_placeMention_live hcs.2.1 hcs.2.2.1,
                    MirMemFrame.refl _, hEnv⟩
    | retag rk p =>
      dsimp only [stepStmtAbs] at hStep
      cases hO : evalOperandAbs env (.copy p) with
      | none => rw [hO] at hStep; nomatch hStep
      | some r =>
        rw [hO] at hStep; cases hStep
        cases r with
        | mk av env₁ =>
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              have hLocEq : locals' = s.frame.locals := hv.2.2.2.1 rfl
              subst hLocEq
              have hEv := hv.1 s.memory.borrows s.memory.globals layouts
                s.memory.callerLocals decls s.memory.callStack (Or.inl rfl)
              cases hv.2.2.2.2.2 layouts with
              | intro ty hty =>
                have hPl : placeTy decls layouts p = some ty := hty.1
                refine ⟨s.frame.locals, s.memory, ?_, MirMemFrame.refl _, hEnv⟩
                cases av with
                | uint u a src =>
                  cases v with
                  | scalar sc => exact evalStmt_retag_scalar hEv hPl (Or.inl ⟨u, hty.2⟩)
                  | _ => exact False.elim hv.2.1.2
                | bool ba =>
                  cases boolAbs_denote_some hv.2.1 with
                  | intro b hb =>
                    rw [hb.1] at hEv
                    exact evalStmt_retag_scalar hEv hPl (Or.inr (Or.inl hty.2))
                | unit =>
                  cases hv.2.1 with
                  | inl hU => exact evalStmt_retag_tuple hEv hPl hty.2 (Or.inl hU)
                  | inr hA => exact evalStmt_retag_tuple hEv hPl hty.2 (Or.inr ⟨0, [], hA⟩)
                | uintBoolPair u a ov =>
                  cases v with
                  | aggregate tag fs =>
                    exact evalStmt_retag_tuple hEv hPl hty.2 (Or.inr ⟨tag, fs, rfl⟩)
                  | _ => exact False.elim hv.2.1.2.2
                | sint i a src =>
                  cases v with
                  | scalar sc =>
                    exact evalStmt_retag_scalar hEv hPl (Or.inr (Or.inr ⟨i, hty.2⟩))
                  | _ => exact False.elim hv.2.1.2
                | sintBoolPair i a ov =>
                  cases v with
                  | aggregate tag fs =>
                    exact evalStmt_retag_tuple hEv hPl hty.2 (Or.inr ⟨tag, fs, rfl⟩)
                  | _ => exact False.elim hv.2.1.2.2
    | storageLive l =>
      dsimp only [stepStmtAbs] at hStep
      cases hD : get? decls l with
      | none => rw [hD] at hStep; nomatch hStep
      | some d =>
        rw [hD] at hStep
        cases hS : get? env l with
        | none => rw [hS] at hStep; nomatch hStep
        | some sl =>
          rw [hS] at hStep
          cases mirAbsEnv_lookup hEnv hS with
          | intro d' hd =>
            cases hd with
            | intro cs hcs =>
              cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
              | intro locals' hSetC =>
                exact ⟨locals', { s.memory with
                  borrows := disableLocalBorrows s.memory.borrows l
                    (length s.memory.callStack) },
                  evalStmt_storageLive_noProt hcs.2.1 hSetC hProt,
                  MirMemFrame.refl _,
                  setMirAbsSlot_sound hEnv hD hStep hSetC
                    (uninitSlotFor_denote d.ty s.frame.locals)⟩
    | storageDead l =>
      dsimp only [stepStmtAbs] at hStep
      cases hS : get? env l with
      | none => rw [hS] at hStep; nomatch hStep
      | some sl =>
        rw [hS] at hStep
        cases mirAbsEnv_lookup hEnv hS with
        | intro d hd =>
          cases hd with
          | intro cs hcs =>
            cases set?_some_of_get? LocalSlot.dead hcs.2.1 with
            | intro locals' hSetC =>
              exact ⟨locals', { s.memory with
                borrows := disableLocalBorrows s.memory.borrows l
                  (length s.memory.callStack) },
                evalStmt_storageDead_noProt hcs.2.1 hSetC hProt,
                MirMemFrame.refl _,
                setMirAbsSlot_sound hEnv hcs.1 hStep hSetC rfl⟩
    | deinit p =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          dsimp only [stepStmtAbs] at hStep
          cases hD : get? decls l with
          | none => rw [hD] at hStep; nomatch hStep
          | some d =>
            rw [hD] at hStep
            cases hS : get? env l with
            | none => rw [hS] at hStep; nomatch hStep
            | some sl =>
              rw [hS] at hStep; dsimp only at hStep
              cases hLv : sl.isLive with
              | false => rw [hLv] at hStep; nomatch hStep
              | true =>
                rw [hLv] at hStep; dsimp only at hStep
                cases env_live_lookup hEnv hS hLv with
                | intro d' hd =>
                  cases hd with
                  | intro cs hcs =>
                    cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
                    | intro locals' hSetC =>
                      exact ⟨locals', { s.memory with
                        borrows := invalidateConflictingBorrows s.memory.borrows l
                          .none (length s.memory.callStack) },
                        evalStmt_deinit_local_noProt hcs.2.1 hcs.2.2.1 hSetC hProt,
                        MirMemFrame.refl _,
                        setMirAbsSlot_sound hEnv hD hStep hSetC
                          (uninitSlotFor_denote d.ty s.frame.locals)⟩
    | intrinsic intr =>
      cases intr with
      | assume op =>
        dsimp only [stepStmtAbs] at hStep
        cases hO : evalOperandAbs env op with
        | none => rw [hO] at hStep; nomatch hStep
        | some r =>
          rw [hO] at hStep
          cases r with
          | mk av env₁ =>
            cases av with
            | bool ba =>
              cases ba with
              | exact c g =>
                cases c with
                | false => nomatch hStep
                | true =>
                  cases hStep
                  cases evalOperandAbs_sound hEnv hO with
                  | intro v hv =>
                    cases hv with
                    | intro locals' hv =>
                      cases boolAbs_denote_some hv.2.1 with
                      | intro b hb =>
                        have hbt : b = true := hb.2.1; subst hbt
                        have hEv := hv.1 s.memory.borrows s.memory.globals layouts
                          s.memory.callerLocals decls s.memory.callStack
                          (Or.inl rfl)
                        rw [hb.1] at hEv
                        exact ⟨locals', s.memory, evalStmt_assume_true hEv,
                          MirMemFrame.refl _,
                          refineEnvByGuard_sound hv.2.2.1 hb.2.2⟩
              | _ => nomatch hStep
            | _ => nomatch hStep
      | _ => nomatch hStep
    | assign dst rv =>
      cases dst with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          dsimp only [stepStmtAbs] at hStep
          cases hD : get? decls l with
          | none => rw [hD] at hStep; nomatch hStep
          | some d =>
            rw [hD] at hStep; dsimp only at hStep
            cases hR : evalRvalueAbs env rv with
            | none => rw [hR] at hStep; nomatch hStep
            | some r =>
              cases r with
              | mk av env₁ =>
                rw [hR] at hStep; dsimp only at hStep
                cases hK : av.kindMatches d.ty.kind with
                | false => rw [hK] at hStep; nomatch hStep
                | true =>
                  rw [hK] at hStep
                  cases hS : get? env₁ l with
                  | none => rw [hS] at hStep; nomatch hStep
                  | some sl =>
                    rw [hS] at hStep; dsimp only at hStep
                    cases hLv : sl.isLive with
                    | false => rw [hLv] at hStep; nomatch hStep
                    | true =>
                      rw [hLv] at hStep; dsimp only at hStep
                      cases evalRvalueAbs_sound s.memory layouts hEnv hR with
                      | intro v hv =>
                        cases hv with
                        | intro locals₁ hv =>
                          cases env_live_lookup hv.2.2 hS hLv with
                          | intro d' hd =>
                            cases hd with
                            | intro cs hcs =>
                              cases set?_some_of_get? (LocalSlot.init v) hcs.2.1 with
                              | intro locals₂ hSetC =>
                                exact ⟨locals₂, { s.memory with
                                  borrows := invalidateConflictingBorrows
                                    s.memory.borrows l .none
                                    (length s.memory.callStack) },
                                  evalStmt_assign_local_noProt hv.1 hcs.2.1
                                    hcs.2.2.1 hSetC hProt,
                                  MirMemFrame.refl _,
                                  setMirAbsSlot_sound hv.2.2 hD hStep hSetC
                                    (mirAbsVal_toSlot_denote hv.2.1
                                      (mirAbsVal_kindOk_of_kindMatches hK))⟩
    | _ => nomatch hStep

/-! ## 9. Terminators -/

/-- Drop outgoing CFG edges whose refined abstract environment is bottom. -/
def filterFeasibleEdges : List (Nat × MirAbsEnv) → List (Nat × MirAbsEnv)
  | [] => []
  | e :: rest =>
    match mirAbsEnvIsBot e.2 with
    | true => filterFeasibleEdges rest
    | false => e :: filterFeasibleEdges rest

theorem filterFeasibleEdges_mem {decls : List LocalDecl}
    {locals : List LocalSlot} {tgt : Nat} {env : MirAbsEnv}
    {es : List (Nat × MirAbsEnv)}
    (hMem : List.Mem (tgt, env) es)
    (hEnv : mirAbsEnvDenote decls env locals) :
    List.Mem (tgt, env) (filterFeasibleEdges es) := by
  induction hMem with
  | head rest =>
    simp only [filterFeasibleEdges]
    cases hBot : mirAbsEnvIsBot env with
    | true => exact False.elim (mirAbsEnv_not_isBot hBot hEnv)
    | false => exact List.Mem.head _
  | tail hd _ ih =>
    simp only [filterFeasibleEdges]
    cases mirAbsEnvIsBot hd.2 with
    | true => exact ih
    | false => exact List.Mem.tail _ ih

/-- Unsigned twin type carrying the discriminant's bit pattern. -/
def SwitchIntTy.twin : SwitchIntTy → UintTy
  | .unsigned u => u
  | .signed i => intTwin i

/-- Guard recording `_r == v` on a taken `switchInt` branch (`.ueqConst` on
unsigned discriminants, `.seqConst` on signed ones). -/
def SwitchIntTy.eqGuard (t : SwitchIntTy) (r v : Nat) : RelGuard :=
  match t with
  | .unsigned u => .ueqConst r u v
  | .signed i => .seqConst r i v

/-- Guard recording `_r != v` on a skipped `switchInt` branch (`.uneConst` on
unsigned discriminants, `.sneConst` on signed ones). -/
def SwitchIntTy.neGuard (t : SwitchIntTy) (r v : Nat) : RelGuard :=
  match t with
  | .unsigned u => .uneConst r u v
  | .signed i => .sneConst r i v

/-- Refine `env` assuming source local `src?` equals `v`. -/
def refineBySwitchEq (t : SwitchIntTy) (src? : Option Nat) (v : Nat)
    (env : MirAbsEnv) : MirAbsEnv :=
  match src? with
  | some r => refineEnvByGuard env (t.eqGuard r v) true
  | none => env

/-- Refine `env` assuming source local `src?` does not equal `v`. -/
def refineBySwitchNe (t : SwitchIntTy) (src? : Option Nat) (v : Nat)
    (env : MirAbsEnv) : MirAbsEnv :=
  match src? with
  | some r => refineEnvByGuard env (t.neGuard r v) true
  | none => env

/-- Refine `env` assuming unsigned source local `src?` equals `v`. -/
def refineBySrcEq (src? : Option Nat) (u : UintTy) (v : Nat) (env : MirAbsEnv) :
    MirAbsEnv :=
  refineBySwitchEq (.unsigned u) src? v env

/-- Refine `env` assuming unsigned source local `src?` does not equal `v`. -/
def refineBySrcNe (src? : Option Nat) (u : UintTy) (v : Nat) (env : MirAbsEnv) :
    MirAbsEnv :=
  refineBySwitchNe (.unsigned u) src? v env

private theorem reduceAbsVal_init_or_bot (w : Nat) (t : Tnum)
    (wi : WrappedInterval) (sc : StridedCong) :
    reduceAbsVal w ⟨.init, t, wi, sc⟩ = AbsVal.bot ∨
      (reduceAbsVal w ⟨.init, t, wi, sc⟩).isInit = true := by
  unfold reduceAbsVal
  cases validWidth w with
  | false => exact Or.inl rfl
  | true =>
    dsimp only
    cases wi.isBot || sc.isBot with
    | true => exact Or.inl rfl
    | false =>
      dsimp only
      cases t.wf && wi.wf (modPow2 w) && sc.wf with
      | false => exact Or.inl rfl
      | true =>
        dsimp only
        cases (reduceStageWi1 (modPow2 w) t wi).isBot with
        | true => exact Or.inl rfl
        | false =>
          dsimp only
          cases reduceStageT1 w t (reduceStageWi1 (modPow2 w) t wi) with
          | none => exact Or.inl rfl
          | some t1 =>
            dsimp only
            cases (reduceStageSc1 w t1 sc).isBot with
            | true => exact Or.inl rfl
            | false =>
              dsimp only
              cases reduceStageT2 w t1 (reduceStageSc1 w t1 sc) with
              | none => exact Or.inl rfl
              | some t2 =>
                dsimp only
                cases (reduceStageWi2
                    (reduceStageWi1 (modPow2 w) t2
                      (reduceStageWi1 (modPow2 w) t wi))
                    (reduceStageSc1 w t1 sc)).isBot with
                | true => exact Or.inl rfl
                | false => exact Or.inr rfl

private theorem reduceAbsVal_isInit_of_denote {w x : Nat} {t : Tnum}
    {wi : WrappedInterval} {sc : StridedCong}
    (h : (reduceAbsVal w ⟨.init, t, wi, sc⟩).denote w (some x)) :
    (reduceAbsVal w ⟨.init, t, wi, sc⟩).isInit = true := by
  cases reduceAbsVal_init_or_bot w t wi sc with
  | inl hBot => rw [hBot] at h; exact False.elim h.1
  | inr hOk => exact hOk

private theorem absVal_refineUneConst_isInit {w x v : Nat} {a : AbsVal}
    (hai : a.isInit = true)
    (h : (AbsVal.refineUneConst w a v).denote w (some x)) :
    (AbsVal.refineUneConst w a v).isInit = true := by
  unfold AbsVal.refineUneConst at h ⊢
  cases hV : (validWidth w && a.isInit) with
  | false => rw [hV] at h; exact False.elim h.1
  | true =>
    rw [hV] at h; dsimp only at h ⊢
    cases hB : Nat.blt v (modPow2 w) with
    | false => exact hai
    | true =>
      rw [hB] at h; dsimp only at h ⊢
      exact reduceAbsVal_isInit_of_denote h

/-- Unfiltered `switchInt` edges for an integer discriminant of type `t`
(unsigned or signed): skips out-of-range branch values (`v ≥ 2^w`), prunes
remaining branches and `otherwise` on exact match (`decideEq? = some true`),
and refines remaining branches and `otherwise` by `x ≠ v`
(`refineUneConst` / `refineBySwitchNe`). Taken branches record
`.ueqConst` / `.seqConst` and skipped ones `.uneConst` / `.sneConst`
according to the signedness of `t`. -/
def evalIntSwitchEdges (t : SwitchIntTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) :
    List (Nat × BasicBlockIdx) → BasicBlockIdx → List (Nat × MirAbsEnv)
  | [], otherwise =>
    match a.isBot with
    | true => []
    | false => [(otherwise, env)]
  | (v, tgt) :: rest, otherwise =>
    match Nat.blt v (modPow2 (uintWidth t.twin)) with
    | false => evalIntSwitchEdges t a src? env rest otherwise
    | true =>
      match AbsVal.decideEq? (uintWidth t.twin) a
          (AbsVal.const (uintWidth t.twin) v) with
      | some true => [(tgt, refineBySwitchEq t src? v env)]
      | some false =>
        evalIntSwitchEdges t (AbsVal.refineUneConst (uintWidth t.twin) a v)
          src? (refineBySwitchNe t src? v env) rest otherwise
      | none =>
        (tgt, refineBySwitchEq t src? v env) ::
          evalIntSwitchEdges t (AbsVal.refineUneConst (uintWidth t.twin) a v)
            src? (refineBySwitchNe t src? v env) rest otherwise

/-- Feasible `switchInt` edges for an integer discriminant (with bottom
environments filtered out). -/
def intSwitchEdges (t : SwitchIntTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) : List (Nat × MirAbsEnv) :=
  filterFeasibleEdges (evalIntSwitchEdges t a src? env branches otherwise)

/-- Unfiltered `switchInt` edges for an unsigned discriminant
(`evalIntSwitchEdges` at `.unsigned u`). -/
def uintSwitchEdgesRaw (u : UintTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) : List (Nat × MirAbsEnv) :=
  evalIntSwitchEdges (.unsigned u) a src? env branches otherwise

/-- Feasible `switchInt` edges for an unsigned discriminant (with bottom
environments filtered out; `intSwitchEdges` at `.unsigned u`). -/
def uintSwitchEdges (u : UintTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) : List (Nat × MirAbsEnv) :=
  intSwitchEdges (.unsigned u) a src? env branches otherwise

/-- Feasible `switchInt` edges for a boolean discriminant (with bottom
environments filtered out). -/
def boolSwitchEdges (env : MirAbsEnv) (targets : SwitchTargets) :
    BoolAbs → Option (List (Nat × MirAbsEnv))
  | .exact c g =>
    some (filterFeasibleEdges
      [(lookupSwitchTarget (boolToScalar c).bits targets.branches
        targets.otherwise, refineEnvByGuard env g c)])
  | .top g =>
    some (filterFeasibleEdges
      [(lookupSwitchTarget (boolToScalar false).bits targets.branches
          targets.otherwise, refineEnvByGuard env g false),
       (lookupSwitchTarget (boolToScalar true).bits targets.branches
          targets.otherwise, refineEnvByGuard env g true)])
  | _ => none

/-- Abstract transfer for a basic block terminator. -/
def stepTermAbs (env : MirAbsEnv) (term : Terminator) : Option TermAbsOutcome :=
  match term.kind with
  | .goto target => some (.edges [(target, env)])
  | .return_ =>
    match get? env 0 with
    | some sl =>
      match sl.isInit with
      | true => some (.ret sl)
      | false => none
    | none => none
  | .drop p target _ =>
    match p.projection, get? env p.local_ with
    | [], some sl =>
      match sl.isLive with
      | true =>
        match setMirAbsSlot p.local_ sl.toUninit env with
        | some env' => some (.edges [(target, env')])
        | none => none
      | false => none
    | _, _ => none
  | .switchInt discr targets =>
    match evalOperandAbs env discr with
    | some (.bool ba, env₁) =>
      match boolSwitchEdges env₁ targets ba with
      | some es => some (.edges es)
      | none => none
    | some (.uint u a src?, env₁) =>
      some (.edges (intSwitchEdges (.unsigned u) a src? env₁ targets.branches
        targets.otherwise))
    | some (.sint i a src?, env₁) =>
      some (.edges (intSwitchEdges (.signed i) a src? env₁ targets.branches
        targets.otherwise))
    | _ => none
  | .assert cond expected target _ =>
    match evalOperandAbs env cond with
    | some (.bool (.exact c g), env₁) =>
      match boolBeq c expected with
      | true => some (.edges (filterFeasibleEdges
          [(target, refineEnvByGuard env₁ g c)]))
      | false => none
    | _ => none
  | _ => none

theorem refineBySwitchEq_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {t : SwitchIntTy} {src? : Option Nat} {x : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r t.twin = some x) :
    mirAbsEnvDenote decls (refineBySwitchEq t src? x env) locals := by
  cases src? with
  | none => exact hEnv
  | some r =>
    cases t with
    | unsigned u =>
      have hS : localUintNat? locals r u = some x := hSrc r rfl
      show mirAbsEnvDenote decls
        (refineEnvByGuard env (.ueqConst r u x) true) locals
      apply refineEnvByGuard_sound hEnv
      intro y hy
      rw [hS] at hy
      injection hy with hy
      subst hy
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    | signed i =>
      have hS : localUintNat? locals r (intTwin i) = some x := hSrc r rfl
      show mirAbsEnvDenote decls
        (refineEnvByGuard env (.seqConst r i x) true) locals
      apply refineEnvByGuard_sound hEnv
      intro y hy
      rw [hS] at hy
      injection hy with hy
      subst hy
      exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem refineBySwitchNe_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {t : SwitchIntTy} {src? : Option Nat} {x v : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r t.twin = some x)
    (hNe : x ≠ v) :
    mirAbsEnvDenote decls (refineBySwitchNe t src? v env) locals := by
  cases src? with
  | none => exact hEnv
  | some r =>
    cases t with
    | unsigned u =>
      have hS : localUintNat? locals r u = some x := hSrc r rfl
      show mirAbsEnvDenote decls
        (refineEnvByGuard env (.uneConst r u v) true) locals
      apply refineEnvByGuard_sound hEnv
      intro y hy
      rw [hS] at hy
      injection hy with hy
      subst hy
      exact ⟨fun _ => hNe, fun _ => rfl⟩
    | signed i =>
      have hS : localUintNat? locals r (intTwin i) = some x := hSrc r rfl
      show mirAbsEnvDenote decls
        (refineEnvByGuard env (.sneConst r i v) true) locals
      apply refineEnvByGuard_sound hEnv
      intro y hy
      rw [hS] at hy
      injection hy with hy
      subst hy
      exact ⟨fun _ => hNe, fun _ => rfl⟩

theorem refineBySrcEq_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {src? : Option Nat} {u : UintTy} {x : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x) :
    mirAbsEnvDenote decls (refineBySrcEq src? u x env) locals :=
  refineBySwitchEq_sound (t := .unsigned u) hEnv hSrc

theorem refineBySrcNe_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {src? : Option Nat} {u : UintTy} {x v : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x)
    (hNe : x ≠ v) :
    mirAbsEnvDenote decls (refineBySrcNe src? u v env) locals :=
  refineBySwitchNe_sound (t := .unsigned u) hEnv hSrc hNe

theorem evalIntSwitchEdges_nil (t : SwitchIntTy) (a : AbsVal)
    (src? : Option Nat) (env : MirAbsEnv) (otherwise : BasicBlockIdx) :
    evalIntSwitchEdges t a src? env [] otherwise =
      (match a.isBot with
       | true => []
       | false => [(otherwise, env)]) := rfl

theorem evalIntSwitchEdges_cons (t : SwitchIntTy) (a : AbsVal)
    (src? : Option Nat) (env : MirAbsEnv) (v : Nat) (tgt : BasicBlockIdx)
    (rest : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    evalIntSwitchEdges t a src? env ((v, tgt) :: rest) otherwise =
      (match Nat.blt v (modPow2 (uintWidth t.twin)) with
       | false => evalIntSwitchEdges t a src? env rest otherwise
       | true =>
         match AbsVal.decideEq? (uintWidth t.twin) a
             (AbsVal.const (uintWidth t.twin) v) with
         | some true => [(tgt, refineBySwitchEq t src? v env)]
         | some false =>
           evalIntSwitchEdges t (AbsVal.refineUneConst (uintWidth t.twin) a v)
             src? (refineBySwitchNe t src? v env) rest otherwise
         | none =>
           (tgt, refineBySwitchEq t src? v env) ::
             evalIntSwitchEdges t
               (AbsVal.refineUneConst (uintWidth t.twin) a v)
               src? (refineBySwitchNe t src? v env) rest otherwise) := rfl

theorem lookupSwitchTarget_cons (x v : Nat) (tgt : BasicBlockIdx)
    (rest : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    lookupSwitchTarget x ((v, tgt) :: rest) otherwise =
      (match Nat.beq x v with
       | true => tgt
       | false => lookupSwitchTarget x rest otherwise) := rfl

/-- Soundness of `evalIntSwitchEdges`: the concrete `switchInt` target of the
discriminant value is among the abstract edges, with a sound refined
environment. -/
theorem evalIntSwitchEdges_sound {decls : List LocalDecl}
    {locals : List LocalSlot} {t : SwitchIntTy} {src? : Option Nat} {x : Nat}
    (hSrc : ∀ r, src? = some r → localUintNat? locals r t.twin = some x) :
    ∀ (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx)
      (a : AbsVal) (env : MirAbsEnv),
      mirAbsEnvDenote decls env locals →
      a.denote (uintWidth t.twin) (some x) →
      a.isInit = true →
      ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
          (evalIntSwitchEdges t a src? env branches otherwise) ∧
        mirAbsEnvDenote decls envT locals
  | [], otherwise, a, env, hEnv, ha, _ => by
    rw [evalIntSwitchEdges_nil]
    cases hBot : a.isBot with
    | true => exact False.elim (absVal_not_isBot hBot ha)
    | false => exact ⟨env, List.Mem.head _, hEnv⟩
  | (v, tgt) :: rest, otherwise, a, env, hEnv, ha, hai => by
    have hw := uintWidth_valid t.twin
    have hxLt := (absVal_some_elim ha).1
    rw [evalIntSwitchEdges_cons, lookupSwitchTarget_cons]
    cases hRange : Nat.blt v (modPow2 (uintWidth t.twin)) with
    | false =>
      have hGe : modPow2 (uintWidth t.twin) ≤ v :=
        Nat.le_of_not_lt (fun hLt => by
          rw [blt_true_of_lt hLt] at hRange; nomatch hRange)
      have hNe : x ≠ v := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt hGe)
      have hBeqF : Nat.beq x v = false := by
        cases hB : Nat.beq x v with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hB) hNe
      rw [hBeqF]
      exact evalIntSwitchEdges_sound hSrc rest otherwise a env hEnv ha hai
    | true =>
      have hvLt : v < modPow2 (uintWidth t.twin) := lt_of_blt_true hRange
      dsimp only
      cases hXV : Nat.beq x v with
      | true =>
        have hEq := Nat.eq_of_beq_eq_true hXV
        subst hEq
        have hNotFalse : AbsVal.decideEq? (uintWidth t.twin) a
            (AbsVal.const (uintWidth t.twin) x) ≠ some false := by
          intro hDec
          have h := absVal_decideEq?_sound hDec ha
            (absVal_const_denote_lt hw hxLt)
          rw [nat_beq_refl] at h
          nomatch h
        dsimp only
        cases hDec : AbsVal.decideEq? (uintWidth t.twin) a
            (AbsVal.const (uintWidth t.twin) x) with
        | none =>
          exact ⟨_, List.Mem.head _, refineBySwitchEq_sound hEnv hSrc⟩
        | some r =>
          cases r with
          | false => exact absurd hDec hNotFalse
          | true => exact ⟨_, List.Mem.head _, refineBySwitchEq_sound hEnv hSrc⟩
      | false =>
        have hNe : x ≠ v := nat_ne_of_beq_false hXV
        have hNotTrue : AbsVal.decideEq? (uintWidth t.twin) a
            (AbsVal.const (uintWidth t.twin) v) ≠ some true := by
          intro hDec
          have h := absVal_decideEq?_sound hDec ha
            (absVal_const_denote_lt hw hvLt)
          rw [hXV] at h
          nomatch h
        have ha' : (AbsVal.refineUneConst (uintWidth t.twin) a v).denote
            (uintWidth t.twin) (some x) :=
          absVal_refineUneConst_sound hw ha hai hNe
        have hai' : (AbsVal.refineUneConst (uintWidth t.twin) a v).isInit =
            true := absVal_refineUneConst_isInit hai ha'
        have hEnv' : mirAbsEnvDenote decls (refineBySwitchNe t src? v env)
            locals := refineBySwitchNe_sound hEnv hSrc hNe
        have ih := evalIntSwitchEdges_sound hSrc rest otherwise
          (AbsVal.refineUneConst (uintWidth t.twin) a v)
          (refineBySwitchNe t src? v env) hEnv' ha' hai'
        dsimp only
        cases hDec : AbsVal.decideEq? (uintWidth t.twin) a
            (AbsVal.const (uintWidth t.twin) v) with
        | none =>
          cases ih with
          | intro envT hT => exact ⟨envT, List.Mem.tail _ hT.1, hT.2⟩
        | some r =>
          cases r with
          | true => exact absurd hDec hNotTrue
          | false => exact ih

/-- Soundness of `intSwitchEdges` for unsigned and signed discriminants. -/
theorem intSwitchEdges_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {t : SwitchIntTy} {a : AbsVal}
    {src? : Option Nat} {x : Nat} (hEnv : mirAbsEnvDenote decls env locals)
    (ha : a.denote (uintWidth t.twin) (some x)) (hai : a.isInit = true)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r t.twin = some x)
    (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
        (intSwitchEdges t a src? env branches otherwise) ∧
      mirAbsEnvDenote decls envT locals := by
  cases evalIntSwitchEdges_sound hSrc branches otherwise a env hEnv ha hai with
  | intro envT hT =>
    exact ⟨envT, filterFeasibleEdges_mem hT.1 hT.2, hT.2⟩

theorem uintSwitchEdgesRaw_sound {decls : List LocalDecl}
    {locals : List LocalSlot} {u : UintTy} {src? : Option Nat} {x : Nat}
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x) :
    ∀ (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx)
      (a : AbsVal) (env : MirAbsEnv),
      mirAbsEnvDenote decls env locals →
      a.denote (uintWidth u) (some x) →
      a.isInit = true →
      ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
          (uintSwitchEdgesRaw u a src? env branches otherwise) ∧
        mirAbsEnvDenote decls envT locals :=
  evalIntSwitchEdges_sound (t := .unsigned u) hSrc

theorem uintSwitchEdges_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {u : UintTy} {a : AbsVal} {src? : Option Nat}
    {x : Nat} (hEnv : mirAbsEnvDenote decls env locals)
    (ha : a.denote (uintWidth u) (some x)) (hai : a.isInit = true)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x)
    (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
        (uintSwitchEdges u a src? env branches otherwise) ∧
      mirAbsEnvDenote decls envT locals :=
  intSwitchEdges_sound (t := .unsigned u) hEnv ha hai hSrc branches otherwise

private theorem evalTerminator_return_root {s : MachineState} {span : String}
    {cb : Option CapturedMir} {retVal : Value}
    (hL : get? s.frame.locals 0 = some (.init retVal))
    (hProt : s.memory.activeProtectors = [])
    (hStack : s.memory.callStack = [])
    (hU : valueContainsUninit retVal = false) :
    evalTerminator s ⟨.return_, span⟩ cb =
      MirStepNode.retNormal retVal
        { s.memory with
          borrows := disableFrameBorrows s.memory.borrows
            (length s.memory.callStack) (length s.frame.locals) } := by
  conv => lhs; whnf
  rw [hL]; (conv => lhs; whnf); rw [hProt]
  have hConf : hasFrameDeallocProtectorConflict s.memory.borrows []
      (length s.memory.callStack) (length s.frame.locals) = false := by
    unfold hasFrameDeallocProtectorConflict; rfl
  rw [hConf]; (conv => lhs; whnf); rw [hStack]; (conv => lhs; whnf); rw [hU]

private theorem evalTerminator_drop_local_noProt {s : MachineState}
    {span : String} {l target : Nat} {unwind : UnwindAction}
    {cb : Option CapturedMir} {cs : LocalSlot} {locals' : List LocalSlot}
    (hL : get? s.frame.locals l = some cs) (hLive : cs ≠ .dead)
    (hSet : set? s.frame.locals l .uninit = some locals')
    (hProt : s.memory.activeProtectors = []) :
    evalTerminator s ⟨.drop ⟨l, []⟩ target unwind, span⟩ cb =
      MirStepNode.emitStep .silent
        { frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          memory := { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows l .none
              (length s.memory.callStack) } } := by
  conv => lhs; whnf
  rw [hL]
  cases cs with
  | dead => exact absurd rfl hLive
  | uninit => (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]; rfl
  | init _ => (conv => lhs; whnf); rw [hSet]; (conv => lhs; whnf); rw [hProt]; rfl

private theorem evalTerminator_switchInt_scalar {s : MachineState}
    {span : String} {discr : Operand} {targets : SwitchTargets}
    {cb : Option CapturedMir} {sc : ScalarInt} {locals' : List LocalSlot}
    (hEv : ∀ (lay : LayoutTable) (bd : List LocalDecl),
      evalOperandWithBodyCast s.frame.locals discr s.memory.borrows
        s.memory.globals lay s.memory.callerLocals bd s.memory.callStack =
          .ok (.scalar sc) locals') :
    evalTerminator s ⟨.switchInt discr targets, span⟩ cb =
      MirStepNode.emitStep (.event sc.bits)
        { frame := {
            blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
            stmtIdx := 0
            locals := locals' }
          memory := s.memory } := by
  conv => lhs; whnf
  rw [hEv]

private theorem evalTerminator_assert_eq {s : MachineState}
    {span : String} {cond : Operand} {b : Bool} {target : Nat}
    {unwind : UnwindAction} {cb : Option CapturedMir} {locals' : List LocalSlot}
    (hEv : ∀ (lay : LayoutTable) (bd : List LocalDecl),
      evalOperandWithBodyCast s.frame.locals cond s.memory.borrows
        s.memory.globals lay s.memory.callerLocals bd s.memory.callStack =
          .ok (.scalar (boolToScalar b)) locals') :
    evalTerminator s ⟨.assert cond b target unwind, span⟩ cb =
      MirStepNode.emitStep .silent
        { frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          memory := s.memory } := by
  conv => lhs; whnf
  rw [hEv]
  cases b <;> rfl

/-- One-step soundness of `stepTermAbs` against `evalTerminator` from a root
frame (`callStack = []`) with no active protectors. Edges are taken via
`MirStepNode.emitStep obs` (`.silent` for `goto` / `assert` / `drop`,
`.event bits` for `switchInt`) preserving `callStack`, `activeCallee`, and
`activeProtectors`, and `return` yields `MirStepNode.retNormal`. -/
theorem stepTermAbs_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {s : MachineState} {term : Terminator} {out : TermAbsOutcome}
    (cb : Option CapturedMir)
    (hEnv : mirAbsEnvDenote decls env s.frame.locals)
    (hProt : s.memory.activeProtectors = [])
    (hStack : s.memory.callStack = [])
    (hTerm : stepTermAbs env term = some out) :
    match out with
    | .ret retSlot =>
      ∃ retVal mem' d, get? decls 0 = some d ∧
        evalTerminator s term cb = MirStepNode.retNormal retVal mem' ∧
        MirMemFrame mem' s.memory ∧
        retSlot.denote d.ty s.frame.locals (.init retVal)
    | .edges succs =>
      ∃ target envT obs locals' mem', List.Mem (target, envT) succs ∧
        evalTerminator s term cb =
          MirStepNode.emitStep obs
            { frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
              memory := mem' } ∧
        MirMemFrame mem' s.memory ∧
        mirAbsEnvDenote decls envT locals' := by
  cases term with
  | mk kind span =>
    cases kind with
    | goto target =>
      cases hTerm
      exact ⟨target, env, .silent, s.frame.locals, s.memory, List.Mem.head _,
        rfl, MirMemFrame.refl _, hEnv⟩
    | return_ =>
      dsimp only [stepTermAbs] at hTerm
      cases hS : get? env 0 with
      | none => rw [hS] at hTerm; nomatch hTerm
      | some sl =>
        rw [hS] at hTerm; dsimp only at hTerm
        cases hI : sl.isInit with
        | false => rw [hI] at hTerm; nomatch hTerm
        | true =>
          rw [hI] at hTerm; cases hTerm
          cases mirAbsEnv_lookup hEnv hS with
          | intro d hd =>
            cases hd with
            | intro cs hcs =>
              cases mirAbsSlot_init hI hcs.2.2 with
              | intro v hv =>
                have hL : get? s.frame.locals 0 = some (.init v) := by
                  rw [hcs.2.1, hv.1]
                refine ⟨v, { s.memory with
                  borrows := disableFrameBorrows s.memory.borrows
                    (length s.memory.callStack) (length s.frame.locals) },
                  d, hcs.1, evalTerminator_return_root hL hProt hStack hv.2,
                  MirMemFrame.refl _, ?_⟩
                rw [← hv.1]
                exact hcs.2.2
    | drop p target unwind =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hTerm
        | nil =>
          dsimp only [stepTermAbs] at hTerm
          cases hS : get? env l with
          | none => rw [hS] at hTerm; nomatch hTerm
          | some sl =>
            rw [hS] at hTerm; dsimp only at hTerm
            cases hLv : sl.isLive with
            | false => rw [hLv] at hTerm; nomatch hTerm
            | true =>
              rw [hLv] at hTerm; dsimp only at hTerm
              cases hSetA : setMirAbsSlot l sl.toUninit env with
              | none => rw [hSetA] at hTerm; nomatch hTerm
              | some env' =>
                rw [hSetA] at hTerm; cases hTerm
                cases env_live_lookup hEnv hS hLv with
                | intro d hd =>
                  cases hd with
                  | intro cs hcs =>
                    cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
                    | intro locals' hSetC =>
                      exact ⟨target, env', .silent, locals',
                        { s.memory with
                          borrows := invalidateConflictingBorrows
                            s.memory.borrows l .none
                            (length s.memory.callStack) },
                        List.Mem.head _,
                        evalTerminator_drop_local_noProt hcs.2.1 hcs.2.2.1
                          hSetC hProt,
                        MirMemFrame.refl _,
                        setMirAbsSlot_sound hEnv hcs.1 hSetA hSetC
                          (mirAbsSlot_toUninit_denote hLv hcs.2.2.2)⟩
    | switchInt discr targets =>
      dsimp only [stepTermAbs] at hTerm
      cases hO : evalOperandAbs env discr with
      | none => rw [hO] at hTerm; nomatch hTerm
      | some r =>
        rw [hO] at hTerm
        cases r with
        | mk av env₁ =>
          have hNoCast := evalOperandAbs_not_opaqueCast_move hO
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              have hEvalT : ∀ (lay : LayoutTable) (bd : List LocalDecl),
                  evalOperandWithBodyCast s.frame.locals discr s.memory.borrows
                    s.memory.globals lay s.memory.callerLocals bd
                    s.memory.callStack = .ok v locals' := by
                intro lay bd
                simp only [evalOperandWithBodyCast, hNoCast]
                exact hv.1 _ _ _ _ _ _ (Or.inr rfl)
              cases av with
              | bool ba =>
                dsimp only at hTerm
                cases hB : boolSwitchEdges env₁ targets ba with
                | none => rw [hB] at hTerm; nomatch hTerm
                | some es =>
                  rw [hB] at hTerm; cases hTerm
                  cases boolAbs_denote_some hv.2.1 with
                  | intro b hb =>
                    have hEv := evalTerminator_switchInt_scalar (cb := cb)
                      (targets := targets) (span := span)
                      (fun lay bd => by rw [← hb.1]; exact hEvalT lay bd)
                    cases ba with
                    | exact c g =>
                      cases hB
                      have hc : b = c := hb.2.1; subst hc
                      have hRef := refineEnvByGuard_sound hv.2.2.1 hb.2.2
                      exact ⟨_, _, _, locals', s.memory,
                        filterFeasibleEdges_mem (List.Mem.head _) hRef,
                        hEv, MirMemFrame.refl _, hRef⟩
                    | top g =>
                      cases hB
                      have hRef := refineEnvByGuard_sound hv.2.2.1 hb.2
                      cases b with
                      | false =>
                        exact ⟨_, _, _, locals', s.memory,
                          filterFeasibleEdges_mem (List.Mem.head _) hRef,
                          hEv, MirMemFrame.refl _, hRef⟩
                      | true =>
                        exact ⟨_, _, _, locals', s.memory,
                          filterFeasibleEdges_mem
                            (List.Mem.tail _ (List.Mem.head _)) hRef,
                          hEv, MirMemFrame.refl _, hRef⟩
                    | bot => nomatch hB
                    | uninit => nomatch hB
              | uint u a src? =>
                cases hTerm
                have hDen := hv.2.1
                cases v with
                | scalar sc =>
                  have hSrc : ∀ r, src? = some r →
                      localUintNat? locals' r u = some sc.bits := by
                    intro r hr; have h := hDen.2.2.2; rw [hr] at h; exact h
                  cases intSwitchEdges_sound (t := .unsigned u) hv.2.2.1
                      hDen.2.2.1 hDen.1 hSrc targets.branches
                      targets.otherwise with
                  | intro envT hT =>
                    exact ⟨_, envT, .event sc.bits, locals', s.memory, hT.1,
                      evalTerminator_switchInt_scalar hEvalT,
                      MirMemFrame.refl _, hT.2⟩
                | _ => exact False.elim hDen.2
              | sint i a src? =>
                cases hTerm
                have hDen := hv.2.1
                cases v with
                | scalar sc =>
                  have hSrc : ∀ r, src? = some r →
                      localUintNat? locals' r (intTwin i) = some sc.bits := by
                    intro r hr; have h := hDen.2.2.2; rw [hr] at h; exact h
                  cases intSwitchEdges_sound (t := .signed i) hv.2.2.1
                      hDen.2.2.1 hDen.1 hSrc targets.branches
                      targets.otherwise with
                  | intro envT hT =>
                    exact ⟨_, envT, .event sc.bits, locals', s.memory, hT.1,
                      evalTerminator_switchInt_scalar hEvalT,
                      MirMemFrame.refl _, hT.2⟩
                | _ => exact False.elim hDen.2
              | unit => nomatch hTerm
              | uintBoolPair _ _ _ => nomatch hTerm
              | sintBoolPair _ _ _ => nomatch hTerm
    | assert cond expected target unwind =>
      dsimp only [stepTermAbs] at hTerm
      cases hO : evalOperandAbs env cond with
      | none => rw [hO] at hTerm; nomatch hTerm
      | some r =>
        rw [hO] at hTerm
        cases r with
        | mk av env₁ =>
          cases av with
          | bool ba =>
            cases ba with
            | exact c g =>
              dsimp only at hTerm
              cases hBq : boolBeq c expected with
              | false => rw [hBq] at hTerm; nomatch hTerm
              | true =>
                rw [hBq] at hTerm; cases hTerm
                have hCE := bool_eq_of_boolBeq hBq; subst hCE
                have hNoCast := evalOperandAbs_not_opaqueCast_move hO
                cases evalOperandAbs_sound hEnv hO with
                | intro v hv =>
                  cases hv with
                  | intro locals' hv =>
                    have hEvalT : ∀ (lay : LayoutTable) (bd : List LocalDecl),
                        evalOperandWithBodyCast s.frame.locals cond s.memory.borrows
                          s.memory.globals lay s.memory.callerLocals bd
                          s.memory.callStack = .ok v locals' := by
                      intro lay bd
                      simp only [evalOperandWithBodyCast, hNoCast]
                      exact hv.1 _ _ _ _ _ _ (Or.inr rfl)
                    cases boolAbs_denote_some hv.2.1 with
                    | intro b hb =>
                      have hbc : b = c := hb.2.1; subst hbc
                      have hRef := refineEnvByGuard_sound hv.2.2.1 hb.2.2
                      exact ⟨target, _, .silent, locals', s.memory,
                        filterFeasibleEdges_mem (List.Mem.head _) hRef,
                        evalTerminator_assert_eq
                          (fun lay bd => by rw [← hb.1]; exact hEvalT lay bd),
                        MirMemFrame.refl _, hRef⟩
            | _ => nomatch hTerm
          | _ => nomatch hTerm
    | _ => nomatch hTerm

/-! ## 10. Machine-Level Step Bridge (`stepMirFn`) -/

/-- `if c = true then a else b` reduces to `a` when `c = true`, for any
`Decidable` instance (avoids classical `ite` congruence in `simp`). Proofs in
this file eliminate `ite` with the `@Decidable.casesOn`-based
`Anneal.Firewall.ite_eq_true_imp`, which never reduces the guard or the
untaken branch. -/
theorem ite_bool_true_eq {α : Sort _} {c : Bool} {d : Decidable (c = true)}
    (hc : c = true) (a b : α) : @ite α (c = true) d a b = a :=
  @Decidable.casesOn (c = true) (fun d => @ite α (c = true) d a b = a) d
    (fun h => False.elim (h hc)) (fun _ => rfl)

/-- `phase` admits stepping (`stepMirFn` fails closed on `.other _`). -/
def mirPhaseSupported : MirPhaseTag → Bool
  | .other _ => false
  | _ => true

/-- `stepMirFn` on a root frame (`activeCallee = none`) dispatches on `body`. -/
theorem stepMirFn_root {body : CapturedMir} {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hCallee : s.memory.activeCallee = none) :
    stepMirFn body s =
      match get? body.basicBlocks s.frame.blockIdx with
      | none => MirStepNode.fail .ub
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => evalStmt s stmt body.localDecls body.layouts
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminator s bb.terminator (some body)
          else
            MirStepNode.fail .ub := by
  unfold stepMirFn
  rw [hCallee]
  simp only [Option.getD]
  cases hP : body.phase with
  | other n => rw [hP] at hPhase; nomatch hPhase
  | runtimePostCleanup => rfl
  | runtimeOptimized => rfl

/-- Statement-position `stepMirFn` soundness: from a root frame at statement
`stmt` of block `bb`, a successful `stepStmtAbs` certifies a silent step to
the next statement with the abstract frame updated to `env'`. -/
theorem stepMirFn_stmt_sound {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {stmt : Statement} {env env' : MirAbsEnv}
    (hPhase : mirPhaseSupported body.phase = true)
    (hCallee : s.memory.activeCallee = none)
    (hBb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hEnv : mirAbsEnvDenote body.localDecls env s.frame.locals)
    (hProt : s.memory.activeProtectors = [])
    (hStep : stepStmtAbs body.localDecls env stmt = some env') :
    ∃ locals' mem',
      stepMirFn body s = MirStepNode.step (advanceStmt s locals' mem') ∧
      MirMemFrame mem' s.memory ∧
      mirAbsEnvDenote body.localDecls env' locals' := by
  rw [stepMirFn_root hPhase hCallee, hBb]
  simp only [hSt]
  exact stepStmtAbs_sound (layouts := body.layouts) hEnv hProt hStep

/-- Terminator-position `stepMirFn` soundness: once `stmtIdx` reaches the end
of block `bb`, a successful `stepTermAbs` certifies either a root-frame
`retNormal` or a step to one of the abstract successor edges. -/
theorem stepMirFn_term_sound {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {env : MirAbsEnv} {out : TermAbsOutcome}
    (hPhase : mirPhaseSupported body.phase = true)
    (hCallee : s.memory.activeCallee = none)
    (hBb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hEnd : s.frame.stmtIdx = length bb.statements)
    (hEnv : mirAbsEnvDenote body.localDecls env s.frame.locals)
    (hProt : s.memory.activeProtectors = [])
    (hStack : s.memory.callStack = [])
    (hTerm : stepTermAbs env bb.terminator = some out) :
    match out with
    | .ret retSlot =>
      ∃ retVal mem' d, get? body.localDecls 0 = some d ∧
        stepMirFn body s = MirStepNode.retNormal retVal mem' ∧
        MirMemFrame mem' s.memory ∧
        retSlot.denote d.ty s.frame.locals (.init retVal)
    | .edges succs =>
      ∃ target envT obs locals' mem', List.Mem (target, envT) succs ∧
        stepMirFn body s =
          MirStepNode.emitStep obs
            { frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
              memory := mem' } ∧
        MirMemFrame mem' s.memory ∧
        mirAbsEnvDenote body.localDecls envT locals' := by
  have hNone : get? bb.statements s.frame.stmtIdx = none := by
    rw [hEnd]
    exact List.getElem?_eq_none (Nat.le_refl _)
  have hEq : (s.frame.stmtIdx == length bb.statements) = true := by
    rw [hEnd]
    exact decide_eq_true rfl
  have hStep : stepMirFn body s = evalTerminator s bb.terminator (some body) := by
    rw [stepMirFn_root hPhase hCallee, hBb]
    dsimp only
    rw [hNone]
    exact Anneal.Firewall.ite_eq_true_imp hEq (fun h => h.symm) rfl
  have hT := stepTermAbs_sound (some body) hEnv hProt hStack hTerm
  rw [hStep]
  cases out with
  | ret r => exact hT
  | edges es => exact hT

/-! ## 11. Entry Frame (`initLocalsAux`) -/

theorem boolAbs_denote_reframe {l1 l2 : List LocalSlot} {ba : BoolAbs}
    {opt : Option Value} (hNoG : ba.noRelGuard = true)
    (h : ba.denote l1 opt) : ba.denote l2 opt := by
  cases opt with
  | none => exact h
  | some v =>
    simp only [BoolAbs.denote] at h ⊢
    cases hB : boolOfValue? v with
    | none => rw [hB] at h; exact h
    | some b =>
      rw [hB] at h
      cases ba with
      | bot => exact h
      | uninit => exact True.intro
      | top g =>
        simp only [BoolAbs.noRelGuard] at hNoG
        simp only [BoolAbs.denoteBool]
        rw [relGuard_eq_of_beq hNoG]
        exact True.intro
      | exact c g =>
        simp only [BoolAbs.noRelGuard] at hNoG
        simp only [BoolAbs.denoteBool] at h ⊢
        rw [relGuard_eq_of_beq hNoG]
        exact ⟨h.1, True.intro⟩

/-- A slot without frame-relative guards or aliases denotes the same concrete
slot in every frame. -/
theorem mirAbsSlot_denote_reframe {ty : Ty} {l1 l2 : List LocalSlot}
    {slot : MirAbsSlot} {cs : LocalSlot} (hNoG : slot.noRelGuard = true)
    (h : slot.denote ty l1 cs) : slot.denote ty l2 cs := by
  cases slot with
  | top => exact h
  | dead => exact h
  | uint _ _ => exact h
  | unit _ => exact h
  | uintCopy _ _ _ => nomatch hNoG
  | sint _ _ => exact h
  | sintCopy _ _ _ => nomatch hNoG
  | bool ba =>
    refine ⟨h.1, ?_⟩
    cases cs with
    | dead => exact h.2
    | uninit => exact boolAbs_denote_reframe hNoG h.2
    | init v => exact boolAbs_denote_reframe hNoG h.2
  | uintBoolPair u a ov =>
    refine ⟨h.1, ?_⟩
    cases cs with
    | dead => exact h.2
    | uninit => exact ⟨h.2.1, boolAbs_denote_reframe hNoG h.2.2⟩
    | init v =>
      cases v with
      | aggregate tag fs =>
        cases tag with
        | succ _ => exact h.2
        | zero =>
          cases fs with
          | nil => exact h.2
          | cons v0 rest =>
            cases v0 with
            | scalar sc =>
              cases rest with
              | nil => exact h.2
              | cons vb rest2 =>
                cases rest2 with
                | cons _ _ => exact h.2
                | nil =>
                  exact ⟨h.2.1, h.2.2.1, boolAbs_denote_reframe hNoG h.2.2.2⟩
            | _ => exact h.2
      | _ => exact h.2
  | sintBoolPair i a ov =>
    refine ⟨h.1, ?_⟩
    cases cs with
    | dead => exact h.2
    | uninit => exact ⟨h.2.1, boolAbs_denote_reframe hNoG h.2.2⟩
    | init v =>
      cases v with
      | aggregate tag fs =>
        cases tag with
        | succ _ => exact h.2
        | zero =>
          cases fs with
          | nil => exact h.2
          | cons v0 rest =>
            cases v0 with
            | scalar sc =>
              cases rest with
              | nil => exact h.2
              | cons vb rest2 =>
                cases rest2 with
                | cons _ _ => exact h.2
                | nil =>
                  exact ⟨h.2.1, h.2.2.1, boolAbs_denote_reframe hNoG h.2.2.2⟩
            | _ => exact h.2
      | _ => exact h.2

/-- Abstract entry frame mirroring `initLocalsAux`: the return place `_0` is
live and uninitialized, parameter `_(i+1)` is described by `argSlots[i]`, and
every local past the supplied arguments is `.dead`. -/
def entryEnvAux : Nat → List LocalDecl → List MirAbsSlot → MirAbsEnv
  | _, [], _ => []
  | 0, d :: ds, args => uninitSlotFor d.ty :: entryEnvAux 1 ds args
  | k + 1, _ :: ds, a :: as => a :: entryEnvAux (k + 1) ds as
  | k + 1, _ :: ds, [] => .dead :: entryEnvAux (k + 1) ds []

/-- Abstract entry frame for `initLocalsAux 0 decls args`. -/
def entryEnv (decls : List LocalDecl) (argSlots : List MirAbsSlot) : MirAbsEnv :=
  entryEnvAux 0 decls argSlots

/-- Argument slots are guard-free and describe the argument values at the
parameter declarations (`decls` here starts at `_1`). -/
def entryArgsOk : List LocalDecl → List MirAbsSlot → List Value → Prop
  | [], _, _ => True
  | _ :: _, [], [] => True
  | d :: ds, a :: as, v :: vs =>
    a.noRelGuard = true ∧ a.valDenote d.ty v ∧ entryArgsOk ds as vs
  | _ :: _, _, _ => False

private theorem entryEnvAux_spec :
    ∀ (k : Nat) (ds : List LocalDecl) (as : List MirAbsSlot) (vs : List Value),
      (match k with
        | 0 => entryArgsOk (ds.drop 1) as vs
        | _ + 1 => entryArgsOk ds as vs) →
      length (entryEnvAux k ds as) = length ds ∧
      length (initLocalsAux k ds vs) = length ds ∧
      ∀ (i : Nat) (d : LocalDecl) (s : MirAbsSlot) (cs : LocalSlot),
        get? ds i = some d → get? (entryEnvAux k ds as) i = some s →
        get? (initLocalsAux k ds vs) i = some cs →
        ∀ locals, s.denote d.ty locals cs
  | _, [], _, _, _ =>
    ⟨rfl, rfl, fun _ _ _ _ hD _ _ _ => nomatch hD⟩
  | 0, d :: ds, as, vs, hOk => by
    have ih := entryEnvAux_spec 1 ds as vs hOk
    refine ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2.1, ?_⟩
    intro i d' s cs hD hS hCs locals
    cases i with
    | zero =>
      cases hD; cases hS; cases hCs
      exact uninitSlotFor_denote d.ty locals
    | succ i => exact ih.2.2 i d' s cs hD hS hCs locals
  | k + 1, d :: ds, [], [], _ => by
    have ih := entryEnvAux_spec (k + 1) ds [] []
      (by cases ds <;> exact True.intro)
    refine ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2.1, ?_⟩
    intro i d' s cs hD hS hCs locals
    cases i with
    | zero => cases hS; cases hCs; rfl
    | succ i => exact ih.2.2 i d' s cs hD hS hCs locals
  | k + 1, d :: ds, a :: as, v :: vs, hOk => by
    have ih := entryEnvAux_spec (k + 1) ds as vs hOk.2.2
    refine ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2.1, ?_⟩
    intro i d' s cs hD hS hCs locals
    cases i with
    | zero =>
      cases hD; cases hS; cases hCs
      exact mirAbsSlot_denote_reframe hOk.1 hOk.2.1
    | succ i => exact ih.2.2 i d' s cs hD hS hCs locals
  | _ + 1, _ :: _, [], _ :: _, hOk => nomatch hOk
  | _ + 1, _ :: _, _ :: _, [], hOk => nomatch hOk

/-- The abstract entry frame has one slot per declared local. -/
theorem length_entryEnv (decls : List LocalDecl) (argSlots : List MirAbsSlot) :
    length (entryEnv decls argSlots) = length decls := by
  have hAux : ∀ k ds as, length (entryEnvAux k ds as) = length ds := by
    intro k ds
    induction ds generalizing k with
    | nil => intro _; rfl
    | cons d rest ih =>
      intro as
      cases k with
      | zero => exact congrArg Nat.succ (ih 1 as)
      | succ k' =>
        cases as with
        | nil => exact congrArg Nat.succ (ih (k' + 1) [])
        | cons _ as' => exact congrArg Nat.succ (ih (k' + 1) as')
  exact hAux 0 decls argSlots

/-- Zero-argument calls trivially satisfy `entryArgsOk`. -/
theorem entryArgsOk_nil (ds : List LocalDecl) : entryArgsOk ds [] [] := by
  cases ds <;> exact True.intro

/-- The abstract entry frame denotes the concrete initial frame
`initLocalsAux 0 decls args` built by `initMachineState`. -/
theorem entryEnv_sound {decls : List LocalDecl} {argSlots : List MirAbsSlot}
    {args : List Value} (hOk : entryArgsOk (decls.drop 1) argSlots args) :
    mirAbsEnvDenote decls (entryEnv decls argSlots) (initLocalsAux 0 decls args) := by
  have h := entryEnvAux_spec 0 decls argSlots args hOk
  exact ⟨h.1, h.2.1, fun i d s cs hD hS hCs => h.2.2 i d s cs hD hS hCs _⟩

/-- `initMachineState body args` is a root frame at `bb0[0]` with no callee,
call stack, or active protectors, over `initLocalsAux 0 body.localDecls args`
(the preconditions of `stepMirFn_stmt_sound` / `stepMirFn_term_sound`). -/
theorem initMachineState_root (body : CapturedMir) (args : List Value) :
    (initMachineState body args).memory.callStack = [] ∧
    (initMachineState body args).memory.activeCallee = none ∧
    (initMachineState body args).memory.activeProtectors = [] ∧
    (initMachineState body args).frame.blockIdx = 0 ∧
    (initMachineState body args).frame.stmtIdx = 0 ∧
    (initMachineState body args).frame.locals =
      initLocalsAux 0 body.localDecls args :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AiPcc
