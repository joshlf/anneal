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
directly against `Trusted.Rustc.V2026_06_01.MirSemantics.{evalOperand,
evalRvalue, evalStmt, evalTerminator}`.

Supported fragment (everything else has no abstract successor, so no
certificate passes if a reachable block uses it):

* integer (`UintTy`), `bool`, and `()` constants; `Copy` / `Move` of
  unprojected scalar/bool/unit/`(u, bool)` locals (`Move` leaves the source
  `LocalSlot.uninit` and clears guards mentioning it); and `.field 0` /
  `.field 1` projections on initialized `(u, bool)` checked-arithmetic tuples;
* unsigned wrapping, checked (`*WithOverflow`), unchecked (overflow-free), and
  `div` / `rem` (nonzero divisor) arithmetic, bitwise operations, shifts,
  boolean binary operations, comparisons recording `RelGuard`s, `UnOp.not` /
  `UnOp.neg`, `CastKind.intToInt` casts to unsigned targets, tuple `(u, bool)`
  aggregates, and `copyForDeref`;
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
supported step preserves.
-/

/-! ## 1. Abstract Operand Values -/

/-- Abstract evaluated operand, optionally remembering the copied source local
`srcReg?` (used to synthesize relational comparison guards). -/
inductive MirAbsVal where
  | uint (u : UintTy) (a : AbsVal) (srcReg? : Option Nat)
  | bool (b : BoolAbs)
  | unit
  | uintBoolPair (u : UintTy) (a : AbsVal) (ov : BoolAbs)

/-- Abstract slot stored by an assignment of `av` (a value copied from local
`r` records the copy alias `.uintCopy u a r`). -/
def MirAbsVal.toSlot : MirAbsVal → MirAbsSlot
  | .uint u a none => .uint u a
  | .uint u a (some r) => .uintCopy u a r
  | .bool b => .bool b
  | .unit => .unit true
  | .uintBoolPair u a ov => .uintBoolPair u a ov

/-- `av` has MIR type kind `k`. -/
def MirAbsVal.kindOk (av : MirAbsVal) (k : RigidTy) : Prop :=
  match av with
  | .uint u _ _ => k = .uint u
  | .bool _ => k = .bool
  | .unit => k = .tuple []
  | .uintBoolPair u _ _ => k = .tuple [.uint u, .bool]

/-- Decidable check that `av` has MIR type kind `k`. -/
def MirAbsVal.kindMatches (av : MirAbsVal) (k : RigidTy) : Bool :=
  match av, k with
  | .uint u _ _, .uint u' => uintTyBeq u u'
  | .bool _, .bool => true
  | .unit, .tuple [] => true
  | .uintBoolPair u _ _, .tuple [.uint u', .bool] => uintTyBeq u u'
  | _, _ => false

theorem mirAbsVal_kindOk_of_kindMatches {av : MirAbsVal} {k : RigidTy}
    (h : av.kindMatches k = true) : av.kindOk k := by
  cases av with
  | uint u a src =>
    cases k with
    | uint u' => exact congrArg RigidTy.uint (uintTy_eq_of_beq h).symm
    | _ => nomatch h
  | bool b =>
    cases k with
    | bool => rfl
    | _ => nomatch h
  | unit =>
    cases k with
    | tuple fs =>
      cases fs with
      | nil => rfl
      | cons _ _ => nomatch h
    | _ => nomatch h
  | uintBoolPair u a ov =>
    cases k with
    | tuple fs =>
      cases fs with
      | nil => nomatch h
      | cons t0 rest =>
        cases t0 with
        | uint u' =>
          cases rest with
          | nil => nomatch h
          | cons t1 rest2 =>
            cases t1 with
            | bool =>
              cases rest2 with
              | nil =>
                have hu := uintTy_eq_of_beq h
                subst hu
                rfl
              | cons _ _ => nomatch h
            | _ => nomatch h
        | _ => nomatch h
    | _ => nomatch h

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

/-- Abstract constant evaluator for unsigned integer, `bool`, and `()`
constants. -/
def evalConstLitAbs (c : ConstOperand) : Option MirAbsVal :=
  match c.val with
  | .scalar (.int sc) =>
    match c.ty.kind with
    | .uint u =>
      match Nat.beq sc.sizeBytes (uintBytes u) &&
          Nat.blt sc.bits (modPow2 (uintWidth u)) with
      | true => some (.uint u (AbsVal.const (uintWidth u) sc.bits) none)
      | false => none
    | .bool =>
      match boolOfValue? (.scalar sc) with
      | some b => some (.bool (.exact b .none))
      | none => none
    | _ => none
  | .zeroSized =>
    match c.ty.kind with
    | .tuple [] => some .unit
    | _ => none
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
        simp only [evalConstLitAbs] at h
        split at h
        · rename_i u hK
          split at h
          · rename_i hC
            injection h with h
            subst h
            have hSz := Nat.eq_of_beq_eq_true (bool_and_true_left hC)
            have hLt := lt_of_blt_true (bool_and_true_right hC)
            refine ⟨.scalar sc, ?_, ?_, hK⟩
            · intro locals borrows globals layouts callerLocals cdecls callStack
              simp only [evalOperand, evalConstValue]
            · intro locals
              exact ⟨absVal_const_isInit (uintWidth_valid u), hSz,
                absVal_const_denote_lt (uintWidth_valid u) hLt, True.intro⟩
          · nomatch h
        · rename_i hK
          split at h
          · rename_i b hB
            injection h with h
            subst h
            refine ⟨.scalar sc, ?_, ?_, hK⟩
            · intro locals borrows globals layouts callerLocals cdecls callStack
              simp only [evalOperand, evalConstValue]
            · intro locals
              simp only [MirAbsVal.denote, BoolAbs.denote, hB]
              constructor <;> trivial
          · nomatch h
        · nomatch h
      | ptr _ _ => nomatch h
    | zeroSized =>
      simp only [evalConstLitAbs] at h
      split at h
      · rename_i hK
        injection h with h
        subst h
        refine ⟨.unit, ?_, fun _ => Or.inl rfl, hK⟩
        intro locals borrows globals layouts callerLocals cdecls callStack
        simp only [evalOperand, evalConstValue]
      · nomatch h
    | slice _ _ => nomatch h
    | indirect _ _ => nomatch h
    | unevaluated _ => nomatch h

/-! ## 3. Operands -/

/-- Read field `idx` (`0` = unsigned scalar, `1` = overflow `bool`) from an
initialized `.uintBoolPair` slot. -/
def evalPairFieldAbs (env : MirAbsEnv) (l idx : Nat) (fty : Ty) :
    Option (MirAbsVal × MirAbsEnv) :=
  match get? env l with
  | some (.uintBoolPair u a ov) =>
    match a.isInit && ov.isInit with
    | false => none
    | true =>
      match idx, fty.kind with
      | 0, .uint u' =>
        match uintTyBeq u u' with
        | true => some (.uint u a none, env)
        | false => none
      | 1, .bool => some (.bool ov, env)
      | _, _ => none
  | _ => none

/-- Abstract operand evaluation for constants, `Copy` / `Move` of unprojected
locals (including `(u, bool)` pairs), and `.field 0` / `.field 1` projections
on initialized `(u, bool)` checked-arithmetic tuples. An unprojected `Move`
leaves the source slot uninitialized (clearing every guard mentioning it),
mirroring `evalOperand`'s `set? .. .uninit`. Reading a `.uintCopy u a src`
slot reports the alias root `src` as the source local. -/
def evalOperandAbs (env : MirAbsEnv) : Operand → Option (MirAbsVal × MirAbsEnv)
  | .copy p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some (.uint u a) =>
        match a.isInit with
        | true => some (.uint u a (some p.local_), env)
        | false => none
      | some (.uintCopy u a src) =>
        match a.isInit with
        | true => some (.uint u a (some src), env)
        | false => none
      | some (.bool ba) =>
        match ba.isInit with
        | true => some (.bool ba, env)
        | false => none
      | some (.unit true) => some (.unit, env)
      | some (.uintBoolPair u a ov) =>
        match a.isInit && ov.isInit with
        | true => some (.uintBoolPair u a ov, env)
        | false => none
      | _ => none
    | [.field idx fty] => evalPairFieldAbs env p.local_ idx fty
    | _ => none
  | .move p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some (.uint u a) =>
        match a.isInit,
            setMirAbsSlot p.local_ (.uint u (AbsVal.uninit (uintWidth u))) env with
        | true, some env' => some (.uint u a none, env')
        | _, _ => none
      | some (.uintCopy u a src) =>
        match a.isInit,
            setMirAbsSlot p.local_ (.uint u (AbsVal.uninit (uintWidth u))) env with
        | true, some env' =>
          match Nat.beq src p.local_ with
          | true => some (.uint u a none, env')
          | false => some (.uint u a (some src), env')
        | _, _ => none
      | some (.bool ba) =>
        match ba.isInit, setMirAbsSlot p.local_ (.bool .uninit) env with
        | true, some env' => some (.bool (ba.clearGuardIf p.local_), env')
        | _, _ => none
      | some (.unit true) =>
        match setMirAbsSlot p.local_ (.unit false) env with
        | some env' => some (.unit, env')
        | none => none
      | some (.uintBoolPair u a ov) =>
        match a.isInit && ov.isInit,
            setMirAbsSlot p.local_
              (.uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit) env with
        | true, some env' =>
          some (.uintBoolPair u a (ov.clearGuardIf p.local_), env')
        | _, _ => none
      | _ => none
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

private theorem evalPairFieldAbs_sound {decls : List LocalDecl}
    {env env' : MirAbsEnv} {locals : List LocalSlot} {l idx : Nat} {fty : Ty}
    {av : MirAbsVal} (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalPairFieldAbs env l idx fty = some (av, env')) :
    ∃ v d rootVal,
      get? decls l = some d ∧
      d.ty.kind = .tuple (match av with
        | .uint u _ _ => [.uint u, .bool]
        | _ => match get? env l with
          | some (.uintBoolPair u _ _) => [.uint u, .bool]
          | _ => []) ∧
      get? locals l = some (.init rootVal) ∧
      readProjectedValue locals rootVal [.field idx fty] = .ok v ∧
      env' = env ∧ av.denote locals v ∧ av.kindOk fty.kind := by
  unfold evalPairFieldAbs at hAbs
  cases hS : get? env l with
  | none => rw [hS] at hAbs; nomatch hAbs
  | some s =>
    rw [hS] at hAbs
    cases s with
    | uintBoolPair u a ov =>
      simp only at hAbs
      cases hI : (a.isInit && ov.isInit) with
      | false => rw [hI] at hAbs; nomatch hAbs
      | true =>
        rw [hI] at hAbs
        have hAi := bool_and_true_left hI
        cases mirAbsEnv_lookup hEnv hS with
        | intro d hd =>
          cases hd with
          | intro cs hcs =>
            cases uintBoolPair_slot_extract hI hcs.2.2 with
            | intro sc hsc =>
              cases hsc with
              | intro vb hsc =>
                have hL : get? locals l =
                    some (.init (.aggregate 0 [.scalar sc, vb])) := by
                  rw [hcs.2.1, hsc.1]
                cases idx with
                | zero =>
                  cases hFk : fty.kind with
                  | uint u' =>
                    rw [hFk] at hAbs
                    simp only at hAbs
                    cases hU : uintTyBeq u u' with
                    | false => rw [hU] at hAbs; nomatch hAbs
                    | true =>
                      rw [hU] at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      have hu := uintTy_eq_of_beq hU
                      subst hu
                      refine ⟨.scalar sc, d, .aggregate 0 [.scalar sc, vb],
                        hcs.1, hcs.2.2.1, hL, rfl, rfl, ?_, rfl⟩
                      exact ⟨hAi, hsc.2.1, hsc.2.2.1, True.intro⟩
                  | _ => rw [hFk] at hAbs; nomatch hAbs
                | succ idx' =>
                  cases idx' with
                  | zero =>
                    cases hFk : fty.kind with
                    | bool =>
                      rw [hFk] at hAbs
                      simp only at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      cases boolAbs_denote_some hsc.2.2.2 with
                      | intro b hb =>
                        refine ⟨vb, d, .aggregate 0 [.scalar sc, vb], hcs.1,
                          hcs.2.2.1, hL, ?_, rfl, hsc.2.2.2, rfl⟩
                        simp only [readProjectedValue, get?, hb.1]; rfl
                    | _ => rw [hFk] at hAbs; nomatch hAbs
                  | succ _ => nomatch hAbs
    | _ => nomatch hAbs

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
  cases op with
  | constant c =>
    simp only [evalOperandAbs] at hAbs
    cases hC : evalConstLitAbs c with
    | none => rw [hC] at hAbs; nomatch hAbs
    | some av0 =>
      rw [hC] at hAbs
      injection hAbs with hAbs
      injection hAbs with hAv hE
      subst hAv
      subst hE
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
        simp only [evalOperandAbs] at hAbs
        cases hS : get? env l with
        | none => rw [hS] at hAbs; nomatch hAbs
        | some s =>
          rw [hS] at hAbs
          cases mirAbsEnv_lookup hEnv hS with
          | intro d hd =>
            cases hd with
            | intro cs hcs =>
              cases s with
              | uint u a =>
                simp only at hAbs
                cases hI : a.isInit with
                | false => rw [hI] at hAbs; nomatch hAbs
                | true =>
                  rw [hI] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases uint_slot_extract hI hcs.2.2 with
                  | intro sc hsc =>
                    have hL : get? locals l = some (.init (.scalar sc)) := by
                      rw [hcs.2.1, hsc.1]
                    refine ⟨.scalar sc, locals, ?_, ?_, hEnv, fun _ => rfl,
                      hNoMove rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack _
                      simp only [evalOperand, hL, readProjectedValue]
                    · exact ⟨hI, hsc.2.1, hsc.2.2,
                        localUintNat?_of_get? hL hsc.2.1⟩
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | uintCopy u a src =>
                simp only at hAbs
                cases hI : a.isInit with
                | false => rw [hI] at hAbs; nomatch hAbs
                | true =>
                  rw [hI] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases uint_slot_extract hI (uintCopy_denote_uint hcs.2.2) with
                  | intro sc hsc =>
                    have hL : get? locals l = some (.init (.scalar sc)) := by
                      rw [hcs.2.1, hsc.1]
                    have hDen := hcs.2.2
                    rw [hsc.1] at hDen
                    refine ⟨.scalar sc, locals, ?_, ?_, hEnv, fun _ => rfl,
                      hNoMove rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack _
                      simp only [evalOperand, hL, readProjectedValue]
                    · exact ⟨hI, hsc.2.1, hsc.2.2, hDen.2.2.2⟩
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | bool ba =>
                simp only at hAbs
                cases hI : ba.isInit with
                | false => rw [hI] at hAbs; nomatch hAbs
                | true =>
                  rw [hI] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases mirAbsSlot_init (s := .bool ba) hI hcs.2.2 with
                  | intro v hv =>
                    have hL : get? locals l = some (.init v) := by
                      rw [hcs.2.1, hv.1]
                    have hDen := hcs.2.2
                    rw [hv.1] at hDen
                    refine ⟨v, locals, ?_, hDen.2, hEnv, fun _ => rfl,
                      hNoMove rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack _
                      simp only [evalOperand, hL, readProjectedValue, hv.2]
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | unit i =>
                cases i with
                | false => nomatch hAbs
                | true =>
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases mirAbsSlot_init (s := .unit true) rfl hcs.2.2 with
                  | intro v hv =>
                    have hL : get? locals l = some (.init v) := by
                      rw [hcs.2.1, hv.1]
                    have hDen := hcs.2.2
                    rw [hv.1] at hDen
                    refine ⟨v, locals, ?_, hDen.2, hEnv, fun _ => rfl,
                      hNoMove rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack _
                      simp only [evalOperand, hL, readProjectedValue, hv.2]
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | uintBoolPair u a ov =>
                simp only at hAbs
                cases hI : (a.isInit && ov.isInit) with
                | false => rw [hI] at hAbs; nomatch hAbs
                | true =>
                  rw [hI] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases mirAbsSlot_init (s := .uintBoolPair u a ov) hI hcs.2.2 with
                  | intro v hv =>
                    have hL : get? locals l = some (.init v) := by
                      rw [hcs.2.1, hv.1]
                    have hDen := hcs.2.2
                    rw [hv.1] at hDen
                    refine ⟨v, locals, ?_,
                      ⟨bool_and_true_left hI, bool_and_true_right hI, hDen.2⟩,
                      hEnv, fun _ => rfl, hNoMove rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack _
                      simp only [evalOperand, hL, readProjectedValue, hv.2]
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | top => nomatch hAbs
              | dead => nomatch hAbs
      | cons pe rest =>
        cases pe with
        | field idx fty =>
          cases rest with
          | cons _ _ => nomatch hAbs
          | nil =>
            simp only [evalOperandAbs] at hAbs
            cases evalPairFieldAbs_sound hEnv hAbs with
            | intro v hv =>
              cases hv with
              | intro d hd =>
                cases hd with
                | intro rootVal hr =>
                  have hE := hr.2.2.2.2.1
                  subst hE
                  refine ⟨v, locals, ?_, hr.2.2.2.2.2.1, hEnv, fun _ => rfl,
                    hNoMove rfl, ?_⟩
                  · intro borrows globals layouts callerLocals cdecls callStack hCd
                    have hNoU : placeTouchesUnion cdecls layouts
                        ⟨l, [.field idx fty]⟩ = false := by
                      cases hCd with
                      | inl hEq =>
                        subst hEq
                        exact placeTouchesUnion_tuple_field_false _ layouts
                          hr.1 hr.2.1
                      | inr hNil => subst hNil; rfl
                    simp only [evalOperand, hr.2.2.1, hNoU, hr.2.2.2.1]
                  · intro layouts
                    exact ⟨fty, (operandTy_field hr.1).1, hr.2.2.2.2.2.2⟩
        | _ => nomatch hAbs
  | move p =>
    cases p with
    | mk l proj =>
      cases proj with
      | nil =>
        simp only [evalOperandAbs] at hAbs
        cases hS : get? env l with
        | none => rw [hS] at hAbs; nomatch hAbs
        | some s =>
          rw [hS] at hAbs
          cases mirAbsEnv_lookup hEnv hS with
          | intro d hd =>
            cases hd with
            | intro cs hcs =>
              have hLc : get? locals l = some cs := hcs.2.1
              cases set?_some_of_get? LocalSlot.uninit hLc with
              | intro locals' hSetC =>
                have hMvNone : operandMovedLocal? (.move ⟨l, []⟩) = none →
                    locals' = locals := fun h => nomatch h
                have hMvSome : ∀ r, operandMovedLocal? (.move ⟨l, []⟩) = some r →
                    ∃ newCs, set? locals r newCs = some locals' := by
                  intro r hr
                  injection hr with hr
                  subst hr
                  exact ⟨.uninit, hSetC⟩
                cases s with
                | uint u a =>
                  simp only at hAbs
                  cases hI : a.isInit with
                  | false => rw [hI] at hAbs; nomatch hAbs
                  | true =>
                    cases hSA : setMirAbsSlot l
                        (.uint u (AbsVal.uninit (uintWidth u))) env with
                    | none => rw [hI, hSA] at hAbs; nomatch hAbs
                    | some envM =>
                      rw [hI, hSA] at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      cases uint_slot_extract hI hcs.2.2 with
                      | intro sc hsc =>
                        have hL : get? locals l = some (.init (.scalar sc)) := by
                          rw [hcs.2.1, hsc.1]
                        refine ⟨.scalar sc, locals', ?_, ?_, ?_, hMvNone,
                          hMvSome, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack _
                          simp only [evalOperand, hL, readProjectedValue, hSetC]
                        · exact ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩
                        · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                            ⟨hcs.2.2.1, absVal_uninit_sound_none⟩
                        · intro layouts
                          exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                | uintCopy u a src =>
                  simp only at hAbs
                  cases hI : a.isInit with
                  | false => rw [hI] at hAbs; nomatch hAbs
                  | true =>
                    cases hSA : setMirAbsSlot l
                        (.uint u (AbsVal.uninit (uintWidth u))) env with
                    | none => rw [hI, hSA] at hAbs; nomatch hAbs
                    | some envM =>
                      rw [hI, hSA] at hAbs
                      cases uint_slot_extract hI (uintCopy_denote_uint hcs.2.2) with
                      | intro sc hsc =>
                        have hL : get? locals l = some (.init (.scalar sc)) := by
                          rw [hcs.2.1, hsc.1]
                        have hDen := hcs.2.2
                        rw [hsc.1] at hDen
                        have hEnvM := setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                          ⟨hcs.2.2.1, absVal_uninit_sound_none⟩
                        have hTyM : ∀ layouts, ∃ ty,
                            operandTy decls layouts (.move ⟨l, []⟩) = some ty ∧
                            (MirAbsVal.uint u a none).kindOk ty.kind :=
                          fun _ => ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                        cases hB : Nat.beq src l with
                        | true =>
                          simp only [hB] at hAbs
                          injection hAbs with hAbs
                          injection hAbs with hAv hE
                          subst hAv
                          subst hE
                          refine ⟨.scalar sc, locals', ?_, ⟨hI, hsc.2.1, hsc.2.2,
                            True.intro⟩, hEnvM, hMvNone, hMvSome, hTyM⟩
                          intro borrows globals layouts callerLocals cdecls callStack _
                          simp only [evalOperand, hL, readProjectedValue, hSetC]
                        | false =>
                          simp only [hB] at hAbs
                          injection hAbs with hAbs
                          injection hAbs with hAv hE
                          subst hAv
                          subst hE
                          refine ⟨.scalar sc, locals', ?_, ⟨hI, hsc.2.1, hsc.2.2,
                            ?_⟩, hEnvM, hMvNone, hMvSome, hTyM⟩
                          · intro borrows globals layouts callerLocals cdecls
                              callStack _
                            simp only [evalOperand, hL, readProjectedValue, hSetC]
                          · show localUintNat? locals' src u = some sc.bits
                            rw [localUintNat?_set?_ne u hSetC
                              (fun hE => nat_ne_of_beq_false hB hE.symm)]
                            exact hDen.2.2.2
                | bool ba =>
                  simp only at hAbs
                  cases hI : ba.isInit with
                  | false => rw [hI] at hAbs; nomatch hAbs
                  | true =>
                    cases hSA : setMirAbsSlot l (.bool .uninit) env with
                    | none => rw [hI, hSA] at hAbs; nomatch hAbs
                    | some envM =>
                      rw [hI, hSA] at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      cases mirAbsSlot_init (s := .bool ba) hI hcs.2.2 with
                      | intro v hv =>
                        have hL : get? locals l = some (.init v) := by
                          rw [hcs.2.1, hv.1]
                        have hDen := hcs.2.2
                        rw [hv.1] at hDen
                        refine ⟨v, locals', ?_, ?_, ?_, hMvNone, hMvSome, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack _
                          simp only [evalOperand, hL, readProjectedValue, hv.2,
                            hSetC]
                        · exact boolAbs_clearGuardIf_denote_update hSetC hDen.2
                        · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                            ⟨hcs.2.2.1, True.intro⟩
                        · intro layouts
                          exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                | unit i =>
                  cases i with
                  | false => nomatch hAbs
                  | true =>
                    cases hSA : setMirAbsSlot l (.unit false) env with
                    | none => simp only [hSA] at hAbs; nomatch hAbs
                    | some envM =>
                      simp only [hSA] at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      cases mirAbsSlot_init (s := .unit true) rfl hcs.2.2 with
                      | intro v hv =>
                        have hL : get? locals l = some (.init v) := by
                          rw [hcs.2.1, hv.1]
                        have hDen := hcs.2.2
                        rw [hv.1] at hDen
                        refine ⟨v, locals', ?_, hDen.2, ?_, hMvNone, hMvSome, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack _
                          simp only [evalOperand, hL, readProjectedValue, hv.2,
                            hSetC]
                        · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                            ⟨hcs.2.2.1, rfl⟩
                        · intro layouts
                          exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                | uintBoolPair u a ov =>
                  simp only at hAbs
                  cases hI : (a.isInit && ov.isInit) with
                  | false => rw [hI] at hAbs; nomatch hAbs
                  | true =>
                    cases hSA : setMirAbsSlot l
                        (.uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit)
                        env with
                    | none => rw [hI, hSA] at hAbs; nomatch hAbs
                    | some envM =>
                      rw [hI, hSA] at hAbs
                      injection hAbs with hAbs
                      injection hAbs with hAv hE
                      subst hAv
                      subst hE
                      cases uintBoolPair_slot_extract hI hcs.2.2 with
                      | intro sc hsc =>
                        cases hsc with
                        | intro vb hsc =>
                          have hL : get? locals l =
                              some (.init (.aggregate 0 [.scalar sc, vb])) := by
                            rw [hcs.2.1, hsc.1]
                          cases boolAbs_denote_some hsc.2.2.2 with
                          | intro b hb =>
                            refine ⟨.aggregate 0 [.scalar sc, vb], locals', ?_,
                              ?_, ?_, hMvNone, hMvSome, ?_⟩
                            · intro borrows globals layouts callerLocals cdecls callStack _
                              simp only [evalOperand, hL, readProjectedValue,
                                hb.1, hSetC]
                            · exact ⟨bool_and_true_left hI,
                                by rw [boolAbs_clearGuardIf_isInit]
                                   exact bool_and_true_right hI,
                                hsc.2.1, hsc.2.2.1,
                                boolAbs_clearGuardIf_denote_update hSetC
                                  hsc.2.2.2⟩
                            · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                                ⟨hcs.2.2.1, absVal_uninit_sound_none, True.intro⟩
                            · intro layouts
                              exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                | top => nomatch hAbs
                | dead => nomatch hAbs
      | cons pe rest =>
        cases pe with
        | field idx fty =>
          cases rest with
          | cons _ _ => nomatch hAbs
          | nil =>
            simp only [evalOperandAbs] at hAbs
            cases evalPairFieldAbs_sound hEnv hAbs with
            | intro v hv =>
              cases hv with
              | intro d hd =>
                cases hd with
                | intro rootVal hr =>
                  have hE := hr.2.2.2.2.1
                  subst hE
                  refine ⟨v, locals, ?_, hr.2.2.2.2.2.1, hEnv, fun _ => rfl,
                    hNoMove rfl, ?_⟩
                  · intro borrows globals layouts callerLocals cdecls callStack hCd
                    have hNoU : placeTouchesUnion cdecls layouts
                        ⟨l, [.field idx fty]⟩ = false := by
                      cases hCd with
                      | inl hEq =>
                        subst hEq
                        exact placeTouchesUnion_tuple_field_false _ layouts
                          hr.1 hr.2.1
                      | inr hNil => subst hNil; rfl
                    simp only [evalOperand, hr.2.2.1, hNoU, hr.2.2.2.1]
                  · intro layouts
                    exact ⟨fty, (operandTy_field hr.1).2, hr.2.2.2.2.2.2⟩
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

/-- Overflow-freedom check for unsigned multiplication via interval bounds. -/
def AbsVal.noOverflowMul (w : Nat) (a b : AbsVal) : Bool :=
  match a.ubound?, b.ubound? with
  | some h1, some h2 => Nat.blt (h1 * h2) (modPow2 w)
  | _, _ => false

theorem absVal_noOverflowMul_sound {w x y : Nat} {a b : AbsVal}
    (h : AbsVal.noOverflowMul w a b = true) (hx : a.denote w (some x))
    (hy : b.denote w (some y)) : x * y < modPow2 w := by
  unfold AbsVal.noOverflowMul at h
  split at h
  · rename_i h1 h2 hU1 hU2
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (absVal_ubound?_sound hU1 hx) (absVal_ubound?_sound hU2 hy))
      (lt_of_blt_true h)
  · nomatch h

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

/-- Unsigned multiplication transfer: folds exact constants, propagates
non-wrapping product intervals `[lo1 * lo2, hi1 * hi2]`, and tracks stride
congruence `≡ 0 (mod c)` for constant factors (preserving alignment). -/
def mulUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (x * y)
  | _, _ =>
    match a1.lbound?, a1.ubound?, a2.lbound?, a2.ubound? with
    | some lo1, some hi1, some lo2, some hi2 =>
      match Nat.blt (hi1 * hi2) (modPow2 w) with
      | true =>
        reduceAbsVal w
          ⟨.init, Tnum.top w, .iv (lo1 * lo2) (hi1 * hi2),
            mulCongFactor w a1 a2 true⟩
      | false =>
        reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩
    | _, _, _, _ =>
      reduceAbsVal w ⟨.init, Tnum.top w, .top, mulCongFactor w a1 a2 false⟩

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
    injection h2 with h2
    subst h2
    exact hFactor y (Nat.mul_mod_left x y)
  | none =>
    cases hE1 : a1.exactVal? w with
    | none => exact True.intro
    | some c =>
      have h1 := (absVal_exactVal?_sound hE1 hx).1
      injection h1 with h1
      subst h1
      exact hFactor x (Nat.mul_mod_right x y)

theorem mulUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) :
    (mulUintAbs w a1 a2).denote w (some (wrapVal w (x * y))) := by
  have hWrapLt : wrapVal w (x * y) < modPow2 w := nat_mod_lt _ (modPow2_pos w)
  have hTopCase : (reduceAbsVal w ⟨.init, Tnum.top w, .top,
      mulCongFactor w a1 a2 false⟩).denote w (some (wrapVal w (x * y))) := by
    apply reduceAbsVal_sound hw
    exact ⟨⟨wrapVal w (x * y), rfl, hWrapLt⟩, tnum_top_sound hWrapLt, hWrapLt,
      mulCongFactor_sound hx hy (fun h => nomatch h)⟩
  unfold mulUintAbs
  split
  · rename_i cx cy hEx hEy
    have h1 := (absVal_exactVal?_sound hEx hx).1
    have h2 := (absVal_exactVal?_sound hEy hy).1
    injection h1 with h1
    injection h2 with h2
    subst h1
    subst h2
    exact absVal_const_sound hw
  · cases hLo1 : a1.lbound? with
    | none => exact hTopCase
    | some lo1 =>
      cases hHi1 : a1.ubound? with
      | none => exact hTopCase
      | some hi1 =>
        cases hLo2 : a2.lbound? with
        | none => exact hTopCase
        | some lo2 =>
          cases hHi2 : a2.ubound? with
          | none => exact hTopCase
          | some hi2 =>
            simp only
            cases hLtB : Nat.blt (hi1 * hi2) (modPow2 w) with
            | false =>
              exact hTopCase
            | true =>
              have hHiLt : hi1 * hi2 < modPow2 w := lt_of_blt_true hLtB
              have hLoLeX : lo1 ≤ x := absVal_lbound?_sound hLo1 hx
              have hXLeHi : x ≤ hi1 := absVal_ubound?_sound hHi1 hx
              have hLoLeY : lo2 ≤ y := absVal_lbound?_sound hLo2 hy
              have hYLeHi : y ≤ hi2 := absVal_ubound?_sound hHi2 hy
              have hLoProd : lo1 * lo2 ≤ x * y := Nat.mul_le_mul hLoLeX hLoLeY
              have hHiProd : x * y ≤ hi1 * hi2 := Nat.mul_le_mul hXLeHi hYLeHi
              have hProdLt : x * y < modPow2 w := Nat.lt_of_le_of_lt hHiProd hHiLt
              have hLoLeHi : lo1 * lo2 ≤ hi1 * hi2 := Nat.le_trans hLoProd hHiProd
              have hLoLt : lo1 * lo2 < modPow2 w := Nat.lt_of_le_of_lt hLoLeHi hHiLt
              apply reduceAbsVal_sound hw
              refine ⟨⟨wrapVal w (x * y), rfl, hWrapLt⟩, tnum_top_sound hWrapLt,
                ?_, mulCongFactor_sound hx hy (fun _ => hProdLt)⟩
              rw [wrapVal_of_lt hProdLt]
              exact wrapped_denote_iv_of_le hLoLt hHiLt hLoLeHi hLoProd hHiProd

private theorem nat_div_le_div_right_of_le {a b c : Nat} (h : a ≤ b) :
    a / c ≤ b / c :=
  Nat.div_le_div_right h

private theorem nat_div_le_div_left_of_le {a b c : Nat} (hbc : b ≤ c)
    (hb : 0 < b) : a / c ≤ a / b :=
  Nat.div_le_div_left hbc hb

/-- Unsigned division transfer: folds exact constants, otherwise bounds
`[lo1 / hi2, hi1 / lo2]` (defaulting an unconstrained dividend upper bound
to `2^w - 1`). -/
def divUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (x / y)
  | _, _ =>
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
      match a1.lbound?, a2.ubound? with
      | some lo1, some hi2 =>
        match Nat.blt 0 hi2 with
        | true => lo1 / hi2
        | false => 0
      | _, _ => 0
    match Nat.ble lo hi && Nat.blt hi (modPow2 w) with
    | true => reduceAbsVal w ⟨.init, Tnum.top w, .iv lo hi, .top⟩
    | false => topBelow w (some hi1)

theorem divUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (divUintAbs w a1 a2).denote w (some (wrapVal w (x / y))) := by
  have hxLt := (absVal_some_elim hx).1
  have hDivLt : x / y < modPow2 w := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxLt
  unfold divUintAbs
  split
  · rename_i cx cy hEx hEy
    have h1 := (absVal_exactVal?_sound hEx hx).1
    have h2 := (absVal_exactVal?_sound hEy hy).1
    injection h1 with h1
    injection h2 with h2
    subst h1
    subst h2
    exact absVal_const_sound hw
  · rw [wrapVal_of_lt hDivLt]
    let hi1 :=
      match a1.ubound? with
      | some h => h
      | none => modPow2 w - 1
    have hxHi1 : x ≤ hi1 := by
      dsimp only [hi1]
      cases hHi1 : a1.ubound? with
      | none => exact Nat.le_sub_one_of_lt hxLt
      | some h => exact absVal_ubound?_sound hHi1 hx
    let hi :=
      match a2.lbound? with
      | some lo2 =>
        match Nat.blt 0 lo2 with
        | true => hi1 / lo2
        | false => hi1
      | none => hi1
    let lo :=
      match a1.lbound?, a2.ubound? with
      | some lo1, some hi2 =>
        match Nat.blt 0 hi2 with
        | true => lo1 / hi2
        | false => 0
      | _, _ => 0
    have hDivLeHi : x / y ≤ hi := by
      dsimp only [hi]
      cases hLo2 : a2.lbound? with
      | none => exact Nat.le_trans (Nat.div_le_self x y) hxHi1
      | some lo2 =>
        simp only
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
        cases hHi2 : a2.ubound? with
        | none => exact Nat.zero_le _
        | some hi2 =>
          simp only
          cases hPos2 : Nat.blt 0 hi2 with
          | false => exact Nat.zero_le _
          | true =>
            exact Nat.le_trans
              (nat_div_le_div_left_of_le (absVal_ubound?_sound hHi2 hy) hyPos)
              (nat_div_le_div_right_of_le (absVal_lbound?_sound hLo1 hx))
    change (match Nat.ble lo hi && Nat.blt hi (modPow2 w) with
      | true => reduceAbsVal w ⟨.init, Tnum.top w, .iv lo hi, .top⟩
      | false => topBelow w (some hi1)).denote w (some (x / y))
    cases hOk : (Nat.ble lo hi && Nat.blt hi (modPow2 w)) with
    | false =>
      exact topBelow_sound hw hDivLt (fun hi' hE => by
        injection hE with hE
        subst hE
        exact Nat.le_trans (Nat.div_le_self x y) hxHi1)
    | true =>
      have hLoHi := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
      have hHiLt := lt_of_blt_true (bool_and_true_right hOk)
      have hLoLt := Nat.lt_of_le_of_lt hLoHi hHiLt
      apply reduceAbsVal_sound hw
      exact ⟨⟨x / y, rfl, hDivLt⟩, tnum_top_sound hDivLt,
        wrapped_denote_iv_of_le hLoLt hHiLt hLoHi hLoLeDiv hDivLeHi,
        True.intro⟩

/-- Unsigned remainder transfer: folds exact constants, returns `a1` unchanged
when `hi1 < lo2` (`x % y = x`), else bounds by `min hi1 (hi2 - 1)`. -/
def remUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (x % y)
  | _, _ =>
    match a1.ubound?, a2.lbound? with
    | some hi1, some lo2 =>
      match Nat.blt hi1 lo2 with
      | true => a1
      | false =>
        match a2.ubound? with
        | some hi2 => topBelow w (some (Nat.min hi1 (hi2 - 1)))
        | none => topBelow w (some hi1)
    | some hi1, none =>
      match a2.ubound? with
      | some hi2 => topBelow w (some (Nat.min hi1 (hi2 - 1)))
      | none => topBelow w (some hi1)
    | none, _ =>
      match a2.ubound? with
      | some hi2 => topBelow w (some (hi2 - 1))
      | none => AbsVal.topInit w

theorem remUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (remUintAbs w a1 a2).denote w (some (wrapVal w (x % y))) := by
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
      exact topBelow_sound hw hRemLt (fun h hE => by
        injection hE with hE; subst hE; exact hLe1)
    | some hi2 =>
      have hLe2 : x % y ≤ hi2 - 1 :=
        Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
          (absVal_ubound?_sound hU2 hy))
      exact topBelow_sound hw hRemLt (fun h hE => by
        injection hE with hE; subst hE; exact nat_le_min hLe1 hLe2)
  unfold remUintAbs
  split
  · rename_i cx cy hEx hEy
    have h1 := (absVal_exactVal?_sound hEx hx).1
    have h2 := (absVal_exactVal?_sound hEy hy).1
    injection h1 with h1
    injection h2 with h2
    subst h1
    subst h2
    exact absVal_const_sound hw
  · rw [wrapVal_of_lt hRemLt]
    cases hU1 : a1.ubound? with
    | none =>
      cases hU2 : a2.ubound? with
      | none => exact absVal_topInit_sound hRemLt
      | some hi2 =>
        exact topBelow_sound hw hRemLt (fun hi' hE => by
          injection hE with hE
          subst hE
          exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
            (absVal_ubound?_sound hU2 hy)))
    | some hi1 =>
      cases hL2 : a2.lbound? with
      | none => exact hBoundHi1 hi1 hU1
      | some lo2 =>
        simp only
        cases hLtB : Nat.blt hi1 lo2 with
        | false => exact hBoundHi1 hi1 hU1
        | true =>
          simp only
          have hXLtY : x < y :=
            Nat.lt_of_le_of_lt (absVal_ubound?_sound hU1 hx)
              (Nat.lt_of_lt_of_le (lt_of_blt_true hLtB)
                (absVal_lbound?_sound hL2 hy))
          rw [Nat.mod_eq_of_lt hXLtY]
          exact hx

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

/-- Unsigned comparison outcome computed by `evalScalarBinOp`. -/
def cmpResult (op : BinOp) (x y : Nat) : Bool :=
  match op with
  | .eq => Nat.beq x y
  | .ne => !(Nat.beq x y)
  | .lt => Nat.blt x y
  | .le => Nat.ble x y
  | .gt => Nat.blt y x
  | .ge => Nat.ble y x
  | _ => false

/-- Flip the operand direction of a comparison operator. -/
def flipCmpOp : BinOp → BinOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le
  | op => op

theorem cmpResult_flip (op : BinOp) (x y : Nat) :
    cmpResult (flipCmpOp op) y x = cmpResult op x y := by
  cases op with
  | eq =>
    simp only [flipCmpOp, cmpResult]
    cases h : Nat.beq y x with
    | true => rw [Nat.eq_of_beq_eq_true h, Nat.beq_refl]
    | false =>
      cases h2 : Nat.beq x y with
      | false => rfl
      | true => rw [Nat.eq_of_beq_eq_true h2, Nat.beq_refl] at h; nomatch h
  | ne =>
    simp only [flipCmpOp, cmpResult]
    cases h : Nat.beq y x with
    | true => rw [Nat.eq_of_beq_eq_true h, Nat.beq_refl]
    | false =>
      cases h2 : Nat.beq x y with
      | false => rfl
      | true => rw [Nat.eq_of_beq_eq_true h2, Nat.beq_refl] at h; nomatch h
  | lt | le | gt | ge => rfl
  | _ => rfl

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
  match op with
  | .eq => AbsVal.decideEq? w a1 a2
  | .ne =>
    match AbsVal.decideEq? w a1 a2 with
    | some r => some (!r)
    | none => none
  | .lt => AbsVal.decideLt? w a1 a2
  | .le => AbsVal.decideLe? w a1 a2
  | .gt => AbsVal.decideLt? w a2 a1
  | .ge => AbsVal.decideLe? w a2 a1
  | _ => none

theorem decideCmpAbs_sound {op : BinOp} {w x y : Nat} {a1 a2 : AbsVal}
    {r : Bool} (h : decideCmpAbs op w a1 a2 = some r)
    (hx : a1.denote w (some x)) (hy : a2.denote w (some y)) :
    cmpResult op x y = r := by
  cases op <;> simp only [decideCmpAbs, reduceCtorEq] at h
  · exact absVal_decideEq?_sound h hx hy
  · exact absVal_decideLt?_sound h hx hy
  · exact absVal_decideLe?_sound h hx hy
  · cases hD : AbsVal.decideEq? w a1 a2 with
    | none => rw [hD] at h; nomatch h
    | some r' =>
      rw [hD] at h
      injection h with h
      subst h
      simp only [cmpResult]
      rw [absVal_decideEq?_sound hD hx hy]
  · exact absVal_decideLe?_sound h hy hx
  · exact absVal_decideLt?_sound h hy hx

/-- Guard for `op(copy r, const v)`. -/
def cmpGuardConstR (op : BinOp) (r : Nat) (u : UintTy) (v : Nat) : RelGuard :=
  match op with
  | .eq => .ueqConst r u v
  | .ne => .uneConst r u v
  | .lt =>
    match v with
    | 0 => .none
    | k + 1 => .uleConst r u k
  | .le => .uleConst r u v
  | .gt => .ugtConst r u v
  | .ge =>
    match v with
    | 0 => .none
    | k + 1 => .ugtConst r u k
  | _ => .none

/-- Guard for `op(copy l, copy r)` across all six comparison operators. -/
def cmpGuardRegs (op : BinOp) (l r : Nat) (u : UintTy) : RelGuard :=
  match op with
  | .eq => .ueqReg l r u
  | .ne => .uneReg l r u
  | .lt => .ultReg l r u
  | .le => .ugeReg r l u
  | .gt => .ultReg r l u
  | .ge => .ugeReg l r u
  | _ => .none

/-- Guard for `op(const v, copy r)` across all six comparison operators. -/
def cmpGuardConstL (op : BinOp) (v : Nat) (r : Nat) (u : UintTy) : RelGuard :=
  cmpGuardConstR (flipCmpOp op) r u v

theorem cmpGuardConstR_sound {op : BinOp} {locals : List LocalSlot} {r : Nat}
    {u : UintTy} {x y : Nat} (hx : localUintNat? locals r u = some x) :
    (cmpGuardConstR op r u y).denote locals (cmpResult op x y) := by
  cases op <;> simp only [cmpGuardConstR] <;>
    first
    | exact True.intro
    | skip
  · intro x' hx'
    rw [hx] at hx'
    injection hx' with hx'
    subst hx'
    exact nat_beq_true_iff
  · cases y with
    | zero => exact True.intro
    | succ k =>
      intro x' hx'
      rw [hx] at hx'
      injection hx' with hx'
      subst hx'
      exact Iff.trans nat_blt_true_iff Nat.lt_succ_iff
  · intro x' hx'
    rw [hx] at hx'
    injection hx' with hx'
    subst hx'
    exact nat_ble_true_iff
  · intro x' hx'
    rw [hx] at hx'
    injection hx' with hx'
    subst hx'
    exact nat_not_beq_true_iff
  · cases y with
    | zero => exact True.intro
    | succ k =>
      intro x' hx'
      rw [hx] at hx'
      injection hx' with hx'
      subst hx'
      exact nat_ble_true_iff
  · intro x' hx'
    rw [hx] at hx'
    injection hx' with hx'
    subst hx'
    exact nat_blt_true_iff

theorem cmpGuardRegs_sound {op : BinOp} {locals : List LocalSlot} {l r : Nat}
    {u : UintTy} {x y : Nat} (hx : localUintNat? locals l u = some x)
    (hy : localUintNat? locals r u = some y) :
    (cmpGuardRegs op l r u).denote locals (cmpResult op x y) := by
  cases op <;> simp only [cmpGuardRegs] <;>
    first
    | exact True.intro
    | skip
  · intro x' y' hx' hy'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_beq_true_iff
  · intro x' y' hx' hy'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_blt_true_iff
  · intro y' x' hy' hx'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_ble_true_iff
  · intro x' y' hx' hy'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_not_beq_true_iff
  · intro x' y' hx' hy'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_ble_true_iff
  · intro y' x' hy' hx'
    rw [hx] at hx'
    rw [hy] at hy'
    injection hx' with hx'
    injection hy' with hy'
    subst hx'
    subst hy'
    exact nat_blt_true_iff

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

/-- Overflow boolean and optional guard for `addWithOverflow`. -/
def addOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  let w := uintWidth u
  let known? : Option Bool :=
    match a1.exactVal? w, a2.exactVal? w with
    | some 0, _ => some false
    | _, some 0 => some false
    | _, _ =>
      match AbsVal.noOverflowAdd w a1 a2 with
      | true => some false
      | false =>
        match a1.lbound?, a2.lbound? with
        | some lo1, some lo2 =>
          match Nat.ble (modPow2 w) (lo1 + lo2) with
          | true => some true
          | false => none
        | _, _ => none
  let guard : RelGuard :=
    match srcL, a2.exactVal? w with
    | some r, some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u (modPow2 w - v - 1)
      | false => .none
    | _, _ =>
      match srcR, a1.exactVal? w with
      | some r, some v =>
        match Nat.blt 0 v with
        | true => .ugtConst r u (modPow2 w - v - 1)
        | false => .none
      | _, _ => .none
  mkBoolAbs known? guard

theorem addOverflowBoolAbs_isInit (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (addOverflowBoolAbs u srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

theorem addOverflowBoolAbs_sound {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (addOverflowBoolAbs u srcL srcR a1 a2).denoteBool locals
      (Nat.ble (modPow2 (uintWidth u)) (x + y)) := by
  have hxLt := (absVal_some_elim hx).1
  have hyLt := (absVal_some_elim hy).1
  apply mkBoolAbs_sound
  · intro r hr
    have hFall : (match AbsVal.noOverflowAdd (uintWidth u) a1 a2 with
        | true => some false
        | false =>
          match a1.lbound?, a2.lbound? with
          | some lo1, some lo2 =>
            match Nat.ble (modPow2 (uintWidth u)) (lo1 + lo2) with
            | true => some true
            | false => none
          | _, _ => none) = some r →
        Nat.ble (modPow2 (uintWidth u)) (x + y) = r := by
      intro hF
      cases hNo : AbsVal.noOverflowAdd (uintWidth u) a1 a2 with
      | true =>
        rw [hNo] at hF
        injection hF with hF
        subst hF
        cases absVal_noOverflowAdd_sound hNo hx hy with
        | intro x' hxy =>
          cases hxy with
          | intro y' hxy =>
            injection hxy.1 with h1
            injection hxy.2.1 with h2
            subst h1
            subst h2
            cases hB : Nat.ble (modPow2 (uintWidth u)) (x + y) with
            | false => rfl
            | true =>
              exact False.elim (Nat.not_le_of_gt hxy.2.2.1 (Nat.le_of_ble_eq_true hB))
      | false =>
        rw [hNo] at hF
        cases hL1 : a1.lbound? with
        | none => rw [hL1] at hF; nomatch hF
        | some lo1 =>
          cases hL2 : a2.lbound? with
          | none => rw [hL1, hL2] at hF; nomatch hF
          | some lo2 =>
            rw [hL1, hL2] at hF
            simp only at hF
            cases hOv : Nat.ble (modPow2 (uintWidth u)) (lo1 + lo2) with
            | false => rw [hOv] at hF; nomatch hF
            | true =>
              rw [hOv] at hF
              injection hF with hF
              subst hF
              exact Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOv)
                (Nat.add_le_add (absVal_lbound?_sound hL1 hx)
                  (absVal_lbound?_sound hL2 hy)))
    cases hE1 : a1.exactVal? (uintWidth u) with
    | some c1 =>
      cases c1 with
      | zero =>
        rw [hE1] at hr
        injection hr with hr
        subst hr
        have h1 := (absVal_exactVal?_sound hE1 hx).1
        injection h1 with h1
        subst h1
        rw [Nat.zero_add]
        cases hB : Nat.ble (modPow2 (uintWidth u)) y with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt hyLt (Nat.le_of_ble_eq_true hB))
      | succ k1 =>
        cases hE2 : a2.exactVal? (uintWidth u) with
        | some c2 =>
          cases c2 with
          | zero =>
            rw [hE1, hE2] at hr
            injection hr with hr
            subst hr
            have h2 := (absVal_exactVal?_sound hE2 hy).1
            injection h2 with h2
            subst h2
            rw [Nat.add_zero]
            cases hB : Nat.ble (modPow2 (uintWidth u)) x with
            | false => rfl
            | true => exact False.elim (Nat.not_le_of_gt hxLt (Nat.le_of_ble_eq_true hB))
          | succ k2 =>
            rw [hE1, hE2] at hr
            exact hFall hr
        | none =>
          rw [hE1, hE2] at hr
          exact hFall hr
    | none =>
      cases hE2 : a2.exactVal? (uintWidth u) with
      | some c2 =>
        cases c2 with
        | zero =>
          rw [hE1, hE2] at hr
          injection hr with hr
          subst hr
          have h2 := (absVal_exactVal?_sound hE2 hy).1
          injection h2 with h2
          subst h2
          rw [Nat.add_zero]
          cases hB : Nat.ble (modPow2 (uintWidth u)) x with
          | false => rfl
          | true => exact False.elim (Nat.not_le_of_gt hxLt (Nat.le_of_ble_eq_true hB))
        | succ k2 =>
          rw [hE1, hE2] at hr
          exact hFall hr
      | none =>
        rw [hE1, hE2] at hr
        exact hFall hr
  · have hRight :
        (match srcR, a1.exactVal? (uintWidth u) with
         | some r, some v =>
           match Nat.blt 0 v with
           | true => RelGuard.ugtConst r u (modPow2 (uintWidth u) - v - 1)
           | false => RelGuard.none
         | _, _ => RelGuard.none).denote locals
          (Nat.ble (modPow2 (uintWidth u)) (x + y)) := by
      cases srcR with
      | none => exact True.intro
      | some r =>
        cases hE1 : a1.exactVal? (uintWidth u) with
        | none => exact True.intro
        | some v =>
          simp only
          cases hPos : Nat.blt 0 v with
          | false => exact True.intro
          | true =>
            have h1 := (absVal_exactVal?_sound hE1 hx).1
            injection h1 with h1
            subst h1
            intro y' hy'
            rw [hR r rfl] at hy'
            injection hy' with hy'
            subst hy'
            rw [Nat.add_comm x y]
            exact add_overflow_ugt_iff hxLt
    cases srcL with
    | none => exact hRight
    | some r =>
      cases hE2 : a2.exactVal? (uintWidth u) with
      | none => exact hRight
      | some v =>
        simp only
        cases hPos : Nat.blt 0 v with
        | false => exact True.intro
        | true =>
          have h2 := (absVal_exactVal?_sound hE2 hy).1
          injection h2 with h2
          subst h2
          intro x' hx'
          rw [hL r rfl] at hx'
          injection hx' with hx'
          subst hx'
          exact add_overflow_ugt_iff hyLt

/-- Overflow boolean and guard for `subWithOverflow` (underflow iff `x < y`). -/
def subOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  let w := uintWidth u
  let known? :=
    match AbsVal.noUnderflowSub w a1 a2 with
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
    cases hNo : AbsVal.noUnderflowSub (uintWidth u) a1 a2 with
    | true =>
      rw [hNo] at hr
      injection hr with hr
      subst hr
      cases absVal_noUnderflowSub_sound hNo hx hy with
      | intro x' hxy =>
        cases hxy with
        | intro y' hxy =>
          injection hxy.1 with h1
          injection hxy.2.1 with h2
          subst h1
          subst h2
          rw [nat_blt_eq_not_ble, Nat.ble_eq_true_of_le hxy.2.2.1]
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

/-- Overflow boolean and optional guard for `mulWithOverflow`. -/
def mulOverflowBoolAbs (u : UintTy) (srcL srcR : Option Nat) (a1 a2 : AbsVal) :
    BoolAbs :=
  let w := uintWidth u
  let known? : Option Bool :=
    match a1.exactVal? w, a2.exactVal? w with
    | some 0, _ => some false
    | _, some 0 => some false
    | _, _ =>
      match AbsVal.noOverflowMul w a1 a2 with
      | true => some false
      | false =>
        match a1.lbound?, a2.lbound? with
        | some lo1, some lo2 =>
          match Nat.ble (modPow2 w) (lo1 * lo2) with
          | true => some true
          | false => none
        | _, _ => none
  let guard : RelGuard :=
    match srcL, a2.exactVal? w with
    | some r, some v =>
      match Nat.blt 0 v with
      | true => .ugtConst r u ((modPow2 w - 1) / v)
      | false => .none
    | _, _ =>
      match srcR, a1.exactVal? w with
      | some r, some v =>
        match Nat.blt 0 v with
        | true => .ugtConst r u ((modPow2 w - 1) / v)
        | false => .none
      | _, _ => .none
  mkBoolAbs known? guard

theorem mulOverflowBoolAbs_isInit (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : (mulOverflowBoolAbs u srcL srcR a1 a2).isInit = true :=
  mkBoolAbs_isInit _ _

theorem mulOverflowBoolAbs_sound {u : UintTy} {srcL srcR : Option Nat}
    {a1 a2 : AbsVal} {locals : List LocalSlot} {x y : Nat}
    (hx : a1.denote (uintWidth u) (some x))
    (hy : a2.denote (uintWidth u) (some y))
    (hL : ∀ r, srcL = some r → localUintNat? locals r u = some x)
    (hR : ∀ r, srcR = some r → localUintNat? locals r u = some y) :
    (mulOverflowBoolAbs u srcL srcR a1 a2).denoteBool locals
      (Nat.ble (modPow2 (uintWidth u)) (x * y)) := by
  have hMPos : 0 < modPow2 (uintWidth u) := modPow2_pos _
  apply mkBoolAbs_sound
  · intro r hr
    have hFall : (match AbsVal.noOverflowMul (uintWidth u) a1 a2 with
        | true => some false
        | false =>
          match a1.lbound?, a2.lbound? with
          | some lo1, some lo2 =>
            match Nat.ble (modPow2 (uintWidth u)) (lo1 * lo2) with
            | true => some true
            | false => none
          | _, _ => none) = some r →
        Nat.ble (modPow2 (uintWidth u)) (x * y) = r := by
      intro hF
      cases hNo : AbsVal.noOverflowMul (uintWidth u) a1 a2 with
      | true =>
        rw [hNo] at hF
        injection hF with hF
        subst hF
        have hLt := absVal_noOverflowMul_sound hNo hx hy
        cases hB : Nat.ble (modPow2 (uintWidth u)) (x * y) with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true hB))
      | false =>
        rw [hNo] at hF
        cases hL1 : a1.lbound? with
        | none => rw [hL1] at hF; nomatch hF
        | some lo1 =>
          cases hL2 : a2.lbound? with
          | none => rw [hL1, hL2] at hF; nomatch hF
          | some lo2 =>
            rw [hL1, hL2] at hF
            simp only at hF
            cases hOv : Nat.ble (modPow2 (uintWidth u)) (lo1 * lo2) with
            | false => rw [hOv] at hF; nomatch hF
            | true =>
              rw [hOv] at hF
              injection hF with hF
              subst hF
              exact Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOv)
                (Nat.mul_le_mul (absVal_lbound?_sound hL1 hx)
                  (absVal_lbound?_sound hL2 hy)))
    cases hE1 : a1.exactVal? (uintWidth u) with
    | some c1 =>
      cases c1 with
      | zero =>
        rw [hE1] at hr
        injection hr with hr
        subst hr
        have h1 := (absVal_exactVal?_sound hE1 hx).1
        injection h1 with h1
        subst h1
        rw [Nat.zero_mul]
        cases hB : Nat.ble (modPow2 (uintWidth u)) 0 with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt hMPos (Nat.le_of_ble_eq_true hB))
      | succ k1 =>
        cases hE2 : a2.exactVal? (uintWidth u) with
        | some c2 =>
          cases c2 with
          | zero =>
            rw [hE1, hE2] at hr
            injection hr with hr
            subst hr
            have h2 := (absVal_exactVal?_sound hE2 hy).1
            injection h2 with h2
            subst h2
            rw [Nat.mul_zero]
            cases hB : Nat.ble (modPow2 (uintWidth u)) 0 with
            | false => rfl
            | true => exact False.elim (Nat.not_le_of_gt hMPos (Nat.le_of_ble_eq_true hB))
          | succ k2 =>
            rw [hE1, hE2] at hr
            exact hFall hr
        | none =>
          rw [hE1, hE2] at hr
          exact hFall hr
    | none =>
      cases hE2 : a2.exactVal? (uintWidth u) with
      | some c2 =>
        cases c2 with
        | zero =>
          rw [hE1, hE2] at hr
          injection hr with hr
          subst hr
          have h2 := (absVal_exactVal?_sound hE2 hy).1
          injection h2 with h2
          subst h2
          rw [Nat.mul_zero]
          cases hB : Nat.ble (modPow2 (uintWidth u)) 0 with
          | false => rfl
          | true => exact False.elim (Nat.not_le_of_gt hMPos (Nat.le_of_ble_eq_true hB))
        | succ k2 =>
          rw [hE1, hE2] at hr
          exact hFall hr
      | none =>
        rw [hE1, hE2] at hr
        exact hFall hr
  · have hRight :
        (match srcR, a1.exactVal? (uintWidth u) with
         | some r, some v =>
           match Nat.blt 0 v with
           | true => RelGuard.ugtConst r u ((modPow2 (uintWidth u) - 1) / v)
           | false => RelGuard.none
         | _, _ => RelGuard.none).denote locals
          (Nat.ble (modPow2 (uintWidth u)) (x * y)) := by
      cases srcR with
      | none => exact True.intro
      | some r =>
        cases hE1 : a1.exactVal? (uintWidth u) with
        | none => exact True.intro
        | some v =>
          simp only
          cases hPos : Nat.blt 0 v with
          | false => exact True.intro
          | true =>
            have h1 := (absVal_exactVal?_sound hE1 hx).1
            injection h1 with h1
            subst h1
            intro y' hy'
            rw [hR r rfl] at hy'
            injection hy' with hy'
            subst hy'
            rw [Nat.mul_comm x y]
            exact mul_overflow_ugt_iff (lt_of_blt_true hPos)
    cases srcL with
    | none => exact hRight
    | some r =>
      cases hE2 : a2.exactVal? (uintWidth u) with
      | none => exact hRight
      | some v =>
        simp only
        cases hPos : Nat.blt 0 v with
        | false => exact True.intro
        | true =>
          have h2 := (absVal_exactVal?_sound hE2 hy).1
          injection h2 with h2
          subst h2
          intro x' hx'
          rw [hL r rfl] at hx'
          injection hx' with hx'
          subst hx'
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

/-- Constant outcome of comparing a value with itself (`x op x`). -/
def decideCmpSame : BinOp → Bool
  | .eq | .le | .ge => true
  | _ => false

/-- Abstract unsigned `BinOp` transfer for operands of equal type `u`.
When both operands share the same source local (`sameLocalOpt`), self-identities
(`x - x = 0`, `x ^ x = 0`, `x / x = 1`, `x % x = 0`, `x == x = true`, etc.) are
folded directly. -/
def binOpSameAbs (op : BinOp) (u : UintTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  let w := uintWidth u
  let same := sameLocalOpt srcL srcR
  match op with
  | .add => some (mkUintVal u (AbsVal.addWrap w a1 a2))
  | .addUnchecked =>
    match AbsVal.noOverflowAdd w a1 a2 with
    | true => some (mkUintVal u (AbsVal.addWrap w a1 a2))
    | false => none
  | .addWithOverflow =>
    some (mkUintBoolPairVal u (AbsVal.addWrap w a1 a2)
      (addOverflowBoolAbs u srcL srcR a1 a2))
  | .sub =>
    match same with
    | true => some (mkUintVal u (AbsVal.const w 0))
    | false => some (mkUintVal u (AbsVal.subWrap w a1 a2))
  | .subUnchecked =>
    match same with
    | true => some (mkUintVal u (AbsVal.const w 0))
    | false =>
      match AbsVal.noUnderflowSub w a1 a2 with
      | true => some (mkUintVal u (AbsVal.subWrap w a1 a2))
      | false => none
  | .subWithOverflow =>
    match same with
    | true => some (mkUintBoolPairVal u (AbsVal.const w 0) (.exact false .none))
    | false =>
      some (mkUintBoolPairVal u (AbsVal.subWrap w a1 a2)
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
    match AbsVal.nonzeroDiv w a2 with
    | true =>
      match same with
      | true => some (mkUintVal u (AbsVal.const w 1))
      | false => some (mkUintVal u (divUintAbs w a1 a2))
    | false => none
  | .rem =>
    match AbsVal.nonzeroDiv w a2 with
    | true =>
      match same with
      | true => some (mkUintVal u (AbsVal.const w 0))
      | false => some (mkUintVal u (remUintAbs w a1 a2))
    | false => none
  | .bitAnd => some (mkUintVal u (AbsVal.bitAnd w a1 a2))
  | .bitOr => some (mkUintVal u (AbsVal.bitOr w a1 a2))
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

/-- Abstract unsigned `BinOp` transfer on evaluated operands `(u1, a1)` and
`(u2, a2)`. Shifts accept any unsigned right-hand type; every other operator
requires equal operand types (`evalScalarBinOp` requires equal byte widths). -/
def binOpUintAbs (op : BinOp) (u1 : UintTy) (a1 : AbsVal) (srcL : Option Nat)
    (u2 : UintTy) (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  let w := uintWidth u1
  let k? := a2.exactVal? (uintWidth u2)
  match op with
  | .shl => some (mkUintVal u1 (shlUintAbs w a1 (k?.map (fun k => Nat.mod k w))))
  | .shlUnchecked =>
    match AbsVal.shiftInBounds w (uintWidth u2) a2 with
    | true => some (mkUintVal u1 (shlUintAbs w a1 k?))
    | false => none
  | .shr => some (mkUintVal u1 (shrUintAbs w a1 (k?.map (fun k => Nat.mod k w))))
  | .shrUnchecked =>
    match AbsVal.shiftInBounds w (uintWidth u2) a2 with
    | true => some (mkUintVal u1 (shrUintAbs w a1 k?))
    | false => none
  | _ =>
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
  cases op <;> simp only [binOpSameAbs, reduceCtorEq] at h
  case add =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_add locals mem,
      mkUintVal_denote (absVal_addWrap_sound hw hx hy hi1 hi2)⟩
  case addUnchecked =>
    cases hB : AbsVal.noOverflowAdd (uintWidth u) a1 a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      cases absVal_noOverflowAdd_sound hB hx hy with
      | intro x' hxy =>
        cases hxy with
        | intro y' hxy =>
          injection hxy.1 with h1
          injection hxy.2.1 with h2
          subst h1
          subst h2
          exact ⟨_, evalScalarBinOp_uint_addUnchecked locals mem hxy.2.2.1,
            mkUintVal_denote (absVal_addWrap_sound hw hx hy hi1 hi2)⟩
  case addWithOverflow =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_addWithOverflow locals mem,
      mkUintBoolPairVal_denote (absVal_addWrap_sound hw hx hy hi1 hi2)
        (addOverflowBoolAbs_isInit u srcL srcR a1 a2)
        (addOverflowBoolAbs_sound hx hy hL hR)⟩
  case sub =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_sub (u := u) (a := x) (b := x) locals mem hxLt hxLt
      have hWrap0 : wrapVal (uintWidth u) (modPow2 (uintWidth u) + x - x) = 0 := by
        rw [Nat.add_sub_cancel]
        exact Nat.mod_self _
      rw [hWrap0] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_sub locals mem hxLt hyLt,
        mkUintVal_denote (absVal_subWrap_sound hw hx hy hi1 hi2)⟩
  case subUnchecked =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_subUnchecked (u := u) (a := x) (b := x)
        locals mem hxLt (Nat.le_refl x)
      have hWrap0 : wrapVal (uintWidth u) (modPow2 (uintWidth u) + x - x) = 0 := by
        rw [Nat.add_sub_cancel]
        exact Nat.mod_self _
      rw [hWrap0] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h
      cases hB : AbsVal.noUnderflowSub (uintWidth u) a1 a2 with
      | false => rw [hB] at h; nomatch h
      | true =>
        rw [hB] at h
        injection h with h
        subst h
        cases absVal_noUnderflowSub_sound hB hx hy with
        | intro x' hxy =>
          cases hxy with
          | intro y' hxy =>
            injection hxy.1 with h1
            injection hxy.2.1 with h2
            subst h1
            subst h2
            exact ⟨_, evalScalarBinOp_uint_subUnchecked locals mem hxLt hxy.2.2.1,
              mkUintVal_denote (absVal_subWrap_sound hw hx hy hi1 hi2)⟩
  case subWithOverflow =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_subWithOverflow (u := u) (a := x) (b := x)
        locals mem hxLt hxLt
      have hWrap0 : wrapVal (uintWidth u) (modPow2 (uintWidth u) + x - x) = 0 := by
        rw [Nat.add_sub_cancel]
        exact Nat.mod_self _
      rw [hWrap0, Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, mkUintBoolPairVal_denote
        (absVal_const_denote_lt hw (modPow2_pos _)) rfl ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_subWithOverflow locals mem hxLt hyLt,
        mkUintBoolPairVal_denote (absVal_subWrap_sound hw hx hy hi1 hi2)
          (subOverflowBoolAbs_isInit u srcL srcR a1 a2)
          (subOverflowBoolAbs_sound hx hy hL hR)⟩
  case mul =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_mul locals mem,
      mkUintVal_denote (mulUintAbs_sound hw hx hy)⟩
  case mulUnchecked =>
    cases hB : AbsVal.noOverflowMul (uintWidth u) a1 a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_mulUnchecked locals mem
        (absVal_noOverflowMul_sound hB hx hy),
        mkUintVal_denote (mulUintAbs_sound hw hx hy)⟩
  case mulWithOverflow =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_mulWithOverflow locals mem,
      mkUintBoolPairVal_denote (mulUintAbs_sound hw hx hy)
        (mulOverflowBoolAbs_isInit u srcL srcR a1 a2)
        (mulOverflowBoolAbs_sound hx hy hL hR)⟩
  case div =>
    cases hB : AbsVal.nonzeroDiv (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      cases absVal_nonzeroDiv_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hEq
        subst hEq
        cases hSame : sameLocalOpt srcL srcR with
        | true =>
          rw [hSame] at h
          injection h with h
          subst h
          have hxy := sameLocalOpt_eq hSame hL hR
          subst hxy
          have hEv := evalScalarBinOp_uint_div (u := u) (a := x) (b := x)
            locals mem hy'.2.1
          rw [Nat.div_self hy'.2.1, wrapVal_of_lt (one_lt_modPow2_uint u)] at hEv
          exact ⟨_, hEv, mkUintVal_denote
            (absVal_const_denote_lt hw (one_lt_modPow2_uint u))⟩
        | false =>
          rw [hSame] at h
          injection h with h
          subst h
          exact ⟨_, evalScalarBinOp_uint_div locals mem hy'.2.1,
            mkUintVal_denote (divUintAbs_sound hw hx hy hy'.2.1)⟩
  case rem =>
    cases hB : AbsVal.nonzeroDiv (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      cases absVal_nonzeroDiv_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hEq
        subst hEq
        cases hSame : sameLocalOpt srcL srcR with
        | true =>
          rw [hSame] at h
          injection h with h
          subst h
          have hxy := sameLocalOpt_eq hSame hL hR
          subst hxy
          have hEv := evalScalarBinOp_uint_rem (u := u) (a := x) (b := x)
            locals mem hy'.2.1
          rw [Nat.mod_self, wrapVal_of_lt (modPow2_pos _)] at hEv
          exact ⟨_, hEv, mkUintVal_denote
            (absVal_const_denote_lt hw (modPow2_pos _))⟩
        | false =>
          rw [hSame] at h
          injection h with h
          subst h
          exact ⟨_, evalScalarBinOp_uint_rem locals mem hy'.2.1,
            mkUintVal_denote (remUintAbs_sound hw hx hy hy'.2.1)⟩
  case bitAnd =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_bitAnd locals mem hxLt,
      mkUintVal_denote (absVal_bitAnd_sound hw hx hy hi1 hi2)⟩
  case bitOr =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_bitOr locals mem hxLt hyLt,
      mkUintVal_denote (absVal_bitOr_sound hw hx hy hi1 hi2)⟩
  case bitXor =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_bitXor (u := u) (a := x) (b := x)
        locals mem hxLt hxLt
      rw [nat_xor_self_zero] at hEv
      exact ⟨_, hEv, mkUintVal_denote (absVal_const_denote_lt hw (modPow2_pos _))⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_bitXor locals mem hxLt hyLt,
        mkUintVal_denote (absVal_bitXor_sound hw hx hy hi1 hi2)⟩
  case eq =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_eq (u := u) (a := x) (b := x) locals mem
      rw [Nat.beq_refl] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact true .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_eq locals mem, cmp_bool_denote hx hy hL hR⟩
  case ne =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_ne (u := u) (a := x) (b := x) locals mem
      rw [Nat.beq_refl] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact false .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_ne locals mem, cmp_bool_denote hx hy hL hR⟩
  case lt =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_lt (u := u) (a := x) (b := x) locals mem
      rw [nat_blt_eq_not_ble, Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact false .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_lt locals mem, cmp_bool_denote hx hy hL hR⟩
  case le =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_le (u := u) (a := x) (b := x) locals mem
      rw [Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact true .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_le locals mem, cmp_bool_denote hx hy hL hR⟩
  case gt =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_gt (u := u) (a := x) (b := x) locals mem
      rw [nat_blt_eq_not_ble, Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact false .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_gt locals mem, cmp_bool_denote hx hy hL hR⟩
  case ge =>
    cases hSame : sameLocalOpt srcL srcR with
    | true =>
      rw [hSame] at h
      injection h with h
      subst h
      have hxy := sameLocalOpt_eq hSame hL hR
      subst hxy
      have hEv := evalScalarBinOp_uint_ge (u := u) (a := x) (b := x) locals mem
      rw [Nat.ble_eq_true_of_le (Nat.le_refl x)] at hEv
      exact ⟨_, hEv, boolAbs_denote_of_bool (ba := .exact true .none)
        ⟨rfl, True.intro⟩⟩
    | false =>
      rw [hSame] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_ge locals mem, cmp_bool_denote hx hy hL hR⟩

theorem binOpUintAbs_not_offset {op : BinOp} {u1 u2 : UintTy} {a1 a2 : AbsVal}
    {srcL srcR : Option Nat} {av : MirAbsVal}
    (h : binOpUintAbs op u1 a1 srcL u2 a2 srcR = some av) : op ≠ .offset := by
  intro hOp
  subst hOp
  simp only [binOpUintAbs] at h
  cases hU : uintTyBeq u1 u2 <;>
    simp only [hU, binOpSameAbs, reduceCtorEq] at h

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
  have hSame : (uintTyBeq u1 u2 = true → binOpSameAbs op u1 a1 srcL a2 srcR =
      some av → ∃ v, evalScalarBinOp op ⟨x, uintBytes u1⟩ ⟨y, uintBytes u2⟩
        locals mem false = .ok v locals mem ∧ av.denote locals v) := by
    intro hU hS
    have hu := uintTy_eq_of_beq hU
    subst hu
    exact binOpSameAbs_sound mem hS hi1 hi2 hx hy hL hR
  cases op
  case shl =>
    simp only [binOpUintAbs] at h
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_shl locals mem,
      mkUintVal_denote (shlUintAbs_sound hw1 hx hi1 hKShift)⟩
  case shr =>
    simp only [binOpUintAbs] at h
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_shr locals mem hxLt,
      mkUintVal_denote (shrUintAbs_sound hw1 hx hi1 hKShift)⟩
  case shlUnchecked =>
    simp only [binOpUintAbs] at h
    cases hB : AbsVal.shiftInBounds (uintWidth u1) (uintWidth u2) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      cases absVal_shiftInBounds_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hyEq
        subst hyEq
        exact ⟨_, evalScalarBinOp_uint_shlUnchecked locals mem hy'.2.1,
          mkUintVal_denote (shlUintAbs_sound hw1 hx hi1 hKExact)⟩
  case shrUnchecked =>
    simp only [binOpUintAbs] at h
    cases hB : AbsVal.shiftInBounds (uintWidth u1) (uintWidth u2) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      cases absVal_shiftInBounds_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hyEq
        subst hyEq
        exact ⟨_, evalScalarBinOp_uint_shrUnchecked locals mem hxLt hy'.2.1,
          mkUintVal_denote (shrUintAbs_sound hw1 hx hi1 hKExact)⟩
  all_goals
    simp only [binOpUintAbs] at h
    cases hU : uintTyBeq u1 u2 with
    | false => simp only [hU, reduceCtorEq] at h
    | true =>
      simp only [hU] at h
      exact hSame hU h

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
  cases hI : (b1.isInit && b2.isInit) <;>
    simp only [hI, boolBinOpEval] at h <;> nomatch h

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
          simp only at h
          injection h with h
          subst h
          have hc2 : c2 = v2 := h2.1
          subst hc2
          exact applyBoolUnary_sound (fun x => f x c2) h1
        | top g2 =>
          cases b1 with
          | exact v1 g1 =>
            simp only at h
            injection h with h
            subst h
            have hc1 : c1 = v1 := h1.1
            subst hc1
            exact applyBoolUnary_sound (fun y => f c1 y) h2
          | top g1 =>
            simp only at h
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
      cases op <;> simp only [boolBinOpEval, reduceCtorEq] at hEv
      case bitAnd =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_bitAnd locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case bitOr =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_bitOr locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case bitXor =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_bitXor locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case eq =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_eq locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case ne =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_ne locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case lt =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_lt locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case le =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_le locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case gt =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_gt locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩
      case ge =>
        injection hEv with hEv; subst hEv
        exact ⟨_, evalScalarBinOp_bool_ge locals mem c1 c2,
          boolAbs_denote_of_bool hDen⟩

/-! ## 7. Rvalues -/

/-- Abstract rvalue evaluation: `use`, `copyForDeref`, unsigned/boolean
`UnOp.not`, unsigned `UnOp.neg`, `CastKind.intToInt` to unsigned targets,
unsigned and boolean binary operations, and `()` / `(u, bool)` tuple
aggregates. -/
def evalRvalueAbs (env : MirAbsEnv) : Rvalue → Option (MirAbsVal × MirAbsEnv)
  | .use op => evalOperandAbs env op
  | .copyForDeref p => evalOperandAbs env (.copy p)
  | .unaryOp .not op =>
    match evalOperandAbs env op with
    | some (.bool ba, env₁) => some (.bool (negBoolAbs ba), env₁)
    | some (.uint u a _, env₁) =>
      let w := uintWidth u
      some (mkUintVal u (AbsVal.bitXor w a (AbsVal.const w (modPow2 w - 1))), env₁)
    | _ => none
  | .unaryOp .neg op =>
    match evalOperandAbs env op with
    | some (.uint u a _, env₁) =>
      let w := uintWidth u
      some (mkUintVal u (AbsVal.subWrap w (AbsVal.const w 0) a), env₁)
    | _ => none
  | .cast .intToInt op targetTy =>
    match targetTy.kind with
    | .uint uDst =>
      match evalOperandAbs env op with
      | some (.uint uSrc a _, env₁) =>
        some (mkUintVal uDst (castUintAbs uSrc uDst a), env₁)
      | some (.bool ba, env₁) => some (mkUintVal uDst (boolToUintAbs uDst ba), env₁)
      | _ => none
    | _ => none
  | .aggregate .tuple [] => some (.unit, env)
  | .aggregate .tuple [op0, op1] =>
    match evalOperandAbs env op0 with
    | some (.uint u a _, env₁) =>
      match evalOperandAbs env₁ op1 with
      | some (.bool ov, env₂) =>
        match ov.isInit with
        | true => some (.uintBoolPair u a ov, env₂)
        | false => none
      | _ => none
    | _ => none
  | .binaryOp op lhs rhs =>
    match evalOperandAbs env lhs with
    | some (.uint u1 a1 srcL, env₁) =>
      match evalOperandAbs env₁ rhs with
      | some (.uint u2 a2 srcR, env₂) =>
        let srcL' :=
          match operandMovedLocal? rhs, srcL with
          | some l, some r =>
            match Nat.beq r l with
            | true => none
            | false => some r
          | _, _ => srcL
        match binOpUintAbs op u1 a1 srcL' u2 a2 srcR with
        | some av => some (av, env₂)
        | none => none
      | _ => none
    | some (.bool ba1, env₁) =>
      match evalOperandAbs env₁ rhs with
      | some (.bool ba2, env₂) =>
        let ba1' :=
          match operandMovedLocal? rhs with
          | some l => ba1.clearGuardIf l
          | none => ba1
        match binOpBoolAbs op ba1' ba2 with
        | some baOut => some (.bool baOut, env₂)
        | none => none
      | _ => none
    | _ => none
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
      simp only at hProj
      subst hProj
      nomatch h
  | inr hm =>
    subst hm
    cases p with
    | mk l proj =>
      simp only at hProj
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
      simp only [validateLoadedValue, hty.1]
      cases av with
      | uint u a src =>
        have hk : ty.kind = .uint u := hty.2
        rw [hk]
      | bool ba =>
        have hk : ty.kind = .bool := hty.2
        rw [hk]
        cases boolAbs_denote_some hDen with
        | intro b hb =>
          rw [hb.1]
          cases b <;> rfl
      | unit =>
        have hk : ty.kind = .tuple [] := hty.2
        rw [hk]
      | uintBoolPair u a ov =>
        have hk : ty.kind = .tuple [.uint u, .bool] := hty.2
        rw [hk]
    | move p =>
      simp only [validateLoadedValue, hty.1]
      cases av with
      | uint u a src =>
        have hk : ty.kind = .uint u := hty.2
        rw [hk]
      | bool ba =>
        have hk : ty.kind = .bool := hty.2
        rw [hk]
        cases boolAbs_denote_some hDen with
        | intro b hb =>
          rw [hb.1]
          cases b <;> rfl
      | unit =>
        have hk : ty.kind = .tuple [] := hty.2
        rw [hk]
      | uintBoolPair u a ov =>
        have hk : ty.kind = .tuple [.uint u, .bool] := hty.2
        rw [hk]

theorem operandIsSigned_of_kind {decls : List LocalDecl} {op : Operand}
    {layouts : LayoutTable} {ty : Ty}
    (hTy : operandTy decls layouts op = some ty)
    (hK : tyIsSigned ty = false) :
    operandIsSigned decls op layouts = false := by
  unfold operandIsSigned
  rw [hTy]
  exact hK

theorem tyIsSigned_of_uint {ty : Ty} {u : UintTy} (h : ty.kind = .uint u) :
    tyIsSigned ty = false := by
  unfold tyIsSigned
  rw [h]

theorem tyIsSigned_of_bool {ty : Ty} (h : ty.kind = .bool) :
    tyIsSigned ty = false := by
  unfold tyIsSigned
  rw [h]

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
  cases op <;> first | exact absurd rfl hNe | simp only [evalRvalue, hL, hR]

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
    have hNoDeref := evalOperandAbs_not_deref hAbs
    cases evalOperandAbs_sound hEnv hAbs with
    | intro v hv =>
      cases hv with
      | intro locals' hv =>
        refine ⟨v, locals', ?_, hv.2.1, hv.2.2.1⟩
        have hVal := validateLoadedValue_ok (layouts := layouts) hv.2.1
          (hv.2.2.2.2.2 layouts)
        have hEv := hv.1 mem.borrows mem.globals layouts mem.callerLocals decls
          mem.callStack (Or.inl rfl)
        simp only [evalRvalue, hEv, hVal]
        split
        · exact False.elim (hNoDeref _ _ (Or.inl rfl) rfl)
        · exact False.elim (hNoDeref _ _ (Or.inr rfl) rfl)
        · rfl
  | copyForDeref p =>
    simp only [evalRvalueAbs] at hAbs
    have hNoDeref := evalOperandAbs_not_deref hAbs
    cases evalOperandAbs_sound hEnv hAbs with
    | intro v hv =>
      cases hv with
      | intro locals' hv =>
        refine ⟨v, locals', ?_, hv.2.1, hv.2.2.1⟩
        have hEv := hv.1 mem.borrows mem.globals layouts mem.callerLocals decls
          mem.callStack (Or.inl rfl)
        simp only [evalRvalue, hEv]
        split
        · rename_i restProj b1 b2 rest heq _
          exact False.elim (hNoDeref p restProj (Or.inl rfl) heq)
        · rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      simp only [evalRvalueAbs] at hAbs
      cases hO : evalOperandAbs env op with
      | none => rw [hO] at hAbs; nomatch hAbs
      | some r =>
        rw [hO] at hAbs
        cases r with
        | mk av1 env₁ =>
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              cases hv.2.2.2.2.2 layouts with
              | intro ty hty =>
                have hEv := hv.1 mem.borrows mem.globals layouts
                  mem.callerLocals decls mem.callStack (Or.inl rfl)
                cases av1 with
                | bool ba =>
                  simp only at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  cases boolAbs_denote_some hv.2.1 with
                  | intro b hb =>
                    refine ⟨.scalar (boolToScalar (!b)), locals', ?_, ?_, hv.2.2.1⟩
                    · simp only [evalRvalue, hEv, hb.1, hty.1]
                      exact evalUnaryNot_bool locals' mem hty.2 b
                    · exact boolAbs_denote_of_bool (negBoolAbs_sound hb.2)
                | uint u a src =>
                  simp only at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
                  have hDen := hv.2.1
                  cases v with
                  | scalar sc =>
                    cases sc with
                    | mk x sz =>
                      have hSz : sz = uintBytes u := hDen.2.1
                      subst hSz
                      have hxLt := (absVal_some_elim hDen.2.2.1).1
                      have hMaskLt : modPow2 (uintWidth u) - 1 <
                          modPow2 (uintWidth u) :=
                        Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one
                      refine ⟨.scalar ⟨modPow2 (uintWidth u) - 1 - x, uintBytes u⟩,
                        locals', ?_, ?_, hv.2.2.1⟩
                      · simp only [evalRvalue, hEv, hty.1]
                        exact evalUnaryNot_uint locals' mem hty.2 hxLt
                      · have hXor := absVal_bitXor_sound (uintWidth_valid u)
                          hDen.2.2.1
                          (absVal_const_denote_lt (uintWidth_valid u) hMaskLt)
                          hDen.1 (absVal_const_isInit (uintWidth_valid u))
                        rw [nat_xor_mask_eq_sub hxLt] at hXor
                        exact mkUintVal_denote hXor
                  | _ => exact False.elim hDen.2
                | unit => nomatch hAbs
                | uintBoolPair _ _ _ => nomatch hAbs
    | neg =>
      simp only [evalRvalueAbs] at hAbs
      cases hO : evalOperandAbs env op with
      | none => rw [hO] at hAbs; nomatch hAbs
      | some r =>
        rw [hO] at hAbs
        cases r with
        | mk av1 env₁ =>
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              have hEv := hv.1 mem.borrows mem.globals layouts
                mem.callerLocals decls mem.callStack (Or.inl rfl)
              cases av1 with
              | uint u a src =>
                simp only at hAbs
                injection hAbs with hAbs
                injection hAbs with hAv hE
                subst hAv
                subst hE
                have hDen := hv.2.1
                cases v with
                | scalar sc =>
                  cases sc with
                  | mk x sz =>
                    have hSz : sz = uintBytes u := hDen.2.1
                    subst hSz
                    have hxLt := (absVal_some_elim hDen.2.2.1).1
                    refine ⟨.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) - x),
                      uintBytes u⟩, locals', ?_, ?_, hv.2.2.1⟩
                    · simp only [evalRvalue, hEv, uintBytes_beq_zero]
                      rw [wrapScalarBits_of_lt_uint hxLt, wrapScalarBits_eq_wrapVal,
                        scalarModulus_uintBytes]
                      rfl
                    · have hSub := absVal_subWrap_sound (uintWidth_valid u)
                        (absVal_const_denote_lt (uintWidth_valid u) (modPow2_pos _))
                        hDen.2.2.1 (absVal_const_isInit (uintWidth_valid u)) hDen.1
                      rw [Nat.add_zero] at hSub
                      exact mkUintVal_denote hSub
                | _ => exact False.elim hDen.2
              | bool _ => nomatch hAbs
              | unit => nomatch hAbs
              | uintBoolPair _ _ _ => nomatch hAbs
    | ptrMetadata => nomatch hAbs
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      simp only [evalRvalueAbs] at hAbs
      split at hAbs
      · rename_i uDst hK
        cases hO : evalOperandAbs env op with
        | none => rw [hO] at hAbs; nomatch hAbs
        | some r =>
          rw [hO] at hAbs
          cases r with
          | mk av1 env₁ =>
            cases evalOperandAbs_sound hEnv hO with
            | intro v hv =>
              cases hv with
              | intro locals' hv =>
                cases hv.2.2.2.2.2 layouts with
                | intro ty hty =>
                  have hEv := hv.1 mem.borrows mem.globals layouts
                    mem.callerLocals decls mem.callStack (Or.inl rfl)
                  cases av1 with
                  | uint uSrc a src =>
                    simp only at hAbs
                    injection hAbs with hAbs
                    injection hAbs with hAv hE
                    subst hAv
                    subst hE
                    have hDen := hv.2.1
                    have hSg := operandIsSigned_of_kind hty.1
                      (tyIsSigned_of_uint hty.2)
                    cases v with
                    | scalar sc =>
                      cases sc with
                      | mk x sz =>
                        have hSz : sz = uintBytes uSrc := hDen.2.1
                        subst hSz
                        refine ⟨.scalar ⟨wrapVal (uintWidth uDst) x, uintBytes uDst⟩,
                          locals', ?_, ?_, hv.2.2.1⟩
                        · simp only [evalRvalue, hEv, uintBytes_beq_zero, hK,
                            intCastTargetBytes_uint, hSg]
                          rw [wrapScalarBits_eq_wrapVal]
                        · exact mkUintVal_denote (castUintAbs_sound hDen.1 hDen.2.2.1)
                    | _ => exact False.elim hDen.2
                  | bool ba =>
                    simp only at hAbs
                    injection hAbs with hAbs
                    injection hAbs with hAv hE
                    subst hAv
                    subst hE
                    have hSg := operandIsSigned_of_kind hty.1
                      (tyIsSigned_of_bool hty.2)
                    cases boolAbs_denote_some hv.2.1 with
                    | intro b hb =>
                      have hbLt : (boolToScalar b).bits < modPow2 (uintWidth uDst) :=
                        Nat.lt_of_le_of_lt (boolToScalar_bits_le_one b)
                          (one_lt_modPow2_uint uDst)
                      refine ⟨.scalar ⟨(boolToScalar b).bits, uintBytes uDst⟩,
                        locals', ?_, ?_, hv.2.2.1⟩
                      · simp only [evalRvalue, hEv, hb.1, hK,
                          intCastTargetBytes_uint, hSg]
                        simp only [boolToScalar_sizeBytes, Nat.beq]
                        rw [wrapScalarBits_of_lt_uint hbLt]
                      · exact mkUintVal_denote (boolToUintAbs_sound hb.2)
                  | unit => nomatch hAbs
                  | uintBoolPair _ _ _ => nomatch hAbs
      · nomatch hAbs
    | _ => nomatch hAbs
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      cases ops with
      | nil =>
        simp only [evalRvalueAbs] at hAbs
        injection hAbs with hAbs
        injection hAbs with hAv hE
        subst hAv
        subst hE
        exact ⟨.aggregate 0 [], locals, rfl, Or.inr rfl, hEnv⟩
      | cons op0 rest =>
        cases rest with
        | nil => nomatch hAbs
        | cons op1 rest2 =>
          cases rest2 with
          | cons _ _ => nomatch hAbs
          | nil =>
            simp only [evalRvalueAbs] at hAbs
            cases hO0 : evalOperandAbs env op0 with
            | none => rw [hO0] at hAbs; nomatch hAbs
            | some r0 =>
              rw [hO0] at hAbs
              cases r0 with
              | mk av0 env₁ =>
                cases av0 with
                | uint u a src =>
                  simp only at hAbs
                  cases hO1 : evalOperandAbs env₁ op1 with
                  | none => rw [hO1] at hAbs; nomatch hAbs
                  | some r1 =>
                    rw [hO1] at hAbs
                    cases r1 with
                    | mk av1 env₂ =>
                      cases av1 with
                      | bool ov =>
                        simp only at hAbs
                        cases hOvI : ov.isInit with
                        | false => rw [hOvI] at hAbs; nomatch hAbs
                        | true =>
                          rw [hOvI] at hAbs
                          injection hAbs with hAbs
                          injection hAbs with hAv hE
                          subst hAv
                          subst hE
                          cases evalOperandAbs_sound hEnv hO0 with
                          | intro v0 hv0 =>
                            cases hv0 with
                            | intro locals₁ hv0 =>
                              cases evalOperandAbs_sound hv0.2.2.1 hO1 with
                              | intro v1 hv1 =>
                                cases hv1 with
                                | intro locals₂ hv1 =>
                                  have hD0 := hv0.2.1
                                  cases v0 with
                                  | scalar sc =>
                                    have hEv0 := hv0.1 mem.borrows mem.globals
                                      layouts mem.callerLocals decls
                                      mem.callStack (Or.inl rfl)
                                    have hEv1 := hv1.1 mem.borrows mem.globals
                                      layouts mem.callerLocals decls
                                      mem.callStack (Or.inl rfl)
                                    refine ⟨.aggregate 0 [.scalar sc, v1],
                                      locals₂, ?_,
                                      ⟨hD0.1, hOvI, hD0.2.1, hD0.2.2.1, hv1.2.1⟩,
                                      hv1.2.2.1⟩
                                    simp only [evalRvalue, evalOperands, hEv0, hEv1]
                                  | _ => exact False.elim hD0.2
                      | uint _ _ _ => nomatch hAbs
                      | unit => nomatch hAbs
                      | uintBoolPair _ _ _ => nomatch hAbs
                | bool _ => nomatch hAbs
                | unit => nomatch hAbs
                | uintBoolPair _ _ _ => nomatch hAbs
    | _ => nomatch hAbs
  | binaryOp op lhs rhs =>
    simp only [evalRvalueAbs] at hAbs
    cases hO1 : evalOperandAbs env lhs with
    | none => rw [hO1] at hAbs; nomatch hAbs
    | some r1 =>
      rw [hO1] at hAbs
      cases r1 with
      | mk av1 env₁ =>
        cases av1 with
        | uint u1 a1 srcL =>
          simp only at hAbs
          cases hO2 : evalOperandAbs env₁ rhs with
          | none => rw [hO2] at hAbs; nomatch hAbs
          | some r2 =>
            rw [hO2] at hAbs
            cases r2 with
            | mk av2 env₂ =>
              cases av2 with
              | uint u2 a2 srcR =>
                simp only at hAbs
                let srcL' :=
                  match operandMovedLocal? rhs, srcL with
                  | some l, some r =>
                    match Nat.beq r l with
                    | true => none
                    | false => some r
                  | _, _ => srcL
                cases hB : binOpUintAbs op u1 a1 srcL' u2 a2 srcR with
                | none => rw [hB] at hAbs; nomatch hAbs
                | some av0 =>
                  rw [hB] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
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
                            have hD1 := hv1.2.1
                            have hD2 := hv2.2.1
                            cases v1 with
                            | scalar sc1 =>
                              cases v2 with
                              | scalar sc2 =>
                                cases sc1 with
                                | mk x sz1 =>
                                  cases sc2 with
                                  | mk y sz2 =>
                                    have hS1 : sz1 = uintBytes u1 := hD1.2.1
                                    have hS2 : sz2 = uintBytes u2 := hD2.2.1
                                    subst hS1
                                    subst hS2
                                    have hSg := operandIsSigned_of_kind hty1.1
                                      (tyIsSigned_of_uint hty1.2)
                                    have hEval := evalRvalue_binaryOp_scalar
                                      (binOpUintAbs_not_offset hB)
                                      (hv1.1 mem.borrows mem.globals layouts
                                        mem.callerLocals decls mem.callStack
                                        (Or.inl rfl))
                                      (hv2.1 mem.borrows mem.globals layouts
                                        mem.callerLocals decls mem.callStack
                                        (Or.inl rfl))
                                    rw [hSg] at hEval
                                    have hLsrc : ∀ r, srcL' = some r →
                                        localUintNat? locals₂ r u1 = some x := by
                                      intro r hr
                                      dsimp only [srcL'] at hr
                                      cases hMv : operandMovedLocal? rhs with
                                      | none =>
                                        rw [hMv] at hr
                                        simp only at hr
                                        rw [hv2.2.2.2.1 hMv]
                                        have h1 := hD1.2.2.2
                                        rw [hr] at h1
                                        exact h1
                                      | some l =>
                                        rw [hMv] at hr
                                        cases hSL : srcL with
                                        | none => rw [hSL] at hr; nomatch hr
                                        | some r0 =>
                                          rw [hSL] at hr
                                          simp only at hr
                                          cases hEqRL : Nat.beq r0 l with
                                          | true => rw [hEqRL] at hr; nomatch hr
                                          | false =>
                                            rw [hEqRL] at hr
                                            injection hr with hr
                                            subst hr
                                            cases hv2.2.2.2.2.1 l hMv with
                                            | intro newCs hSet =>
                                              have hNe : l ≠ r0 :=
                                                fun hE => nat_ne_of_beq_false hEqRL hE.symm
                                              have h1 := hD1.2.2.2
                                              rw [hSL] at h1
                                              unfold localUintNat?
                                              rw [get?_set?_ne hSet hNe]
                                              exact h1
                                    have hRsrc : ∀ r, srcR = some r →
                                        localUintNat? locals₂ r u2 = some y := by
                                      intro r hr
                                      have h2 := hD2.2.2.2
                                      rw [hr] at h2
                                      exact h2
                                    cases binOpUintAbs_sound mem hB hD1.1 hD2.1
                                        hD1.2.2.1 hD2.2.2.1 hLsrc hRsrc with
                                    | intro v hv =>
                                      exact ⟨v, locals₂, Eq.trans hEval hv.1, hv.2,
                                        hv2.2.2.1⟩
                              | _ => exact False.elim hD2.2
                            | _ => exact False.elim hD1.2
              | bool _ => nomatch hAbs
              | unit => nomatch hAbs
              | uintBoolPair _ _ _ => nomatch hAbs
        | bool ba1 =>
          simp only at hAbs
          cases hO2 : evalOperandAbs env₁ rhs with
          | none => rw [hO2] at hAbs; nomatch hAbs
          | some r2 =>
            rw [hO2] at hAbs
            cases r2 with
            | mk av2 env₂ =>
              cases av2 with
              | bool ba2 =>
                simp only at hAbs
                let ba1' :=
                  match operandMovedLocal? rhs with
                  | some l => ba1.clearGuardIf l
                  | none => ba1
                cases hB : binOpBoolAbs op ba1' ba2 with
                | none => rw [hB] at hAbs; nomatch hAbs
                | some baOut =>
                  rw [hB] at hAbs
                  injection hAbs with hAbs
                  injection hAbs with hAv hE
                  subst hAv
                  subst hE
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
                            have hBa1' : ba1'.denote locals₂ (some v1) := by
                              dsimp only [ba1']
                              cases hMv : operandMovedLocal? rhs with
                              | none =>
                                rw [hv2.2.2.2.1 hMv]
                                exact hv1.2.1
                              | some l =>
                                cases hv2.2.2.2.2.1 l hMv with
                                | intro newCs hSet =>
                                  exact boolAbs_clearGuardIf_denote_update hSet
                                    hv1.2.1
                            cases boolAbs_denote_some hBa1' with
                            | intro c1 hc1 =>
                              cases boolAbs_denote_some hv2.2.1 with
                              | intro c2 hc2 =>
                                have hSg := operandIsSigned_of_kind hty1.1
                                  (tyIsSigned_of_bool hty1.2)
                                have hEv1 := hv1.1 mem.borrows mem.globals layouts
                                  mem.callerLocals decls mem.callStack (Or.inl rfl)
                                have hEv2 := hv2.1 mem.borrows mem.globals layouts
                                  mem.callerLocals decls mem.callStack (Or.inl rfl)
                                rw [hc1.1] at hEv1
                                rw [hc2.1] at hEv2
                                have hEval := evalRvalue_binaryOp_scalar
                                  (binOpBoolAbs_not_offset hB) hEv1 hEv2
                                rw [hSg] at hEval
                                cases binOpBoolAbs_sound mem hB hc1.2 hc2.2 with
                                | intro v hv =>
                                  exact ⟨v, locals₂, Eq.trans hEval hv.1, hv.2,
                                    hv2.2.2.1⟩
              | uint _ _ _ => nomatch hAbs
              | unit => nomatch hAbs
              | uintBoolPair _ _ _ => nomatch hAbs
        | unit => nomatch hAbs
        | uintBoolPair _ _ _ => nomatch hAbs
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

/-- One-step soundness of `stepStmtAbs` against `evalStmt` from a frame with
no active function-entry protectors. The successor frame advances `stmtIdx`,
and `callStack`, `activeCallee`, and `activeProtectors` are preserved. -/
theorem stepStmtAbs_sound {decls : List LocalDecl} {layouts : LayoutTable}
    {env env' : MirAbsEnv} {s : MachineState} {stmt : Statement}
    (hEnv : mirAbsEnvDenote decls env s.frame.locals)
    (hProt : s.memory.activeProtectors = [])
    (hStep : stepStmtAbs decls env stmt = some env') :
    ∃ locals' mem',
      evalStmt s stmt decls layouts = MirStepNode.step (advanceStmt s locals' mem') ∧
      mem'.callStack = s.memory.callStack ∧
      mem'.activeCallee = s.memory.activeCallee ∧
      mem'.activeProtectors = s.memory.activeProtectors ∧
      mirAbsEnvDenote decls env' locals' := by
  cases stmt with
  | mk kind span =>
    cases kind with
    | nop =>
      injection hStep with hStep
      subst hStep
      exact ⟨s.frame.locals, s.memory, rfl, rfl, rfl, rfl, hEnv⟩
    | coverage =>
      injection hStep with hStep
      subst hStep
      exact ⟨s.frame.locals, s.memory, rfl, rfl, rfl, rfl, hEnv⟩
    | constEvalCounter =>
      injection hStep with hStep
      subst hStep
      exact ⟨s.frame.locals, s.memory, rfl, rfl, rfl, rfl, hEnv⟩
    | backwardIncompatibleDropHint _ =>
      injection hStep with hStep
      subst hStep
      exact ⟨s.frame.locals, s.memory, rfl, rfl, rfl, rfl, hEnv⟩
    | placeMention p =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          simp only [stepStmtAbs] at hStep
          cases hS : get? env l with
          | none => rw [hS] at hStep; nomatch hStep
          | some sl =>
            rw [hS] at hStep
            cases hLv : sl.isLive with
            | false => simp only [hLv] at hStep; nomatch hStep
            | true =>
              simp only [hLv] at hStep
              injection hStep with hStep
              subst hStep
              cases env_live_lookup hEnv hS hLv with
              | intro d hd =>
                cases hd with
                | intro cs hcs =>
                  refine ⟨s.frame.locals, s.memory, ?_, rfl, rfl, rfl, hEnv⟩
                  cases cs with
                  | dead => exact absurd rfl hcs.2.2.1
                  | uninit =>
                    simp only [evalStmt, hcs.2.1, placeMentionOperandsInit,
                      projectionHasDeref, placeIndexLocalsInit]
                  | init v =>
                    simp only [evalStmt, hcs.2.1, placeMentionOperandsInit,
                      projectionHasDeref, placeIndexLocalsInit]
    | retag rk p =>
      simp only [stepStmtAbs] at hStep
      cases hO : evalOperandAbs env (.copy p) with
      | none => rw [hO] at hStep; nomatch hStep
      | some r =>
        rw [hO] at hStep
        injection hStep with hStep
        subst hStep
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
                refine ⟨s.frame.locals, s.memory, ?_, rfl, rfl, rfl, hEnv⟩
                cases ty with
                | mk k lIdx =>
                  cases av with
                  | uint u a src =>
                    have hk : k = .uint u := hty.2
                    subst hk
                    cases v with
                    | scalar sc => simp only [evalStmt, hEv, hPl]
                    | _ => exact False.elim hv.2.1.2
                  | bool ba =>
                    have hk : k = .bool := hty.2
                    subst hk
                    cases boolAbs_denote_some hv.2.1 with
                    | intro b hb =>
                      rw [hb.1] at hEv
                      simp only [evalStmt, hEv, hPl]
                  | unit =>
                    have hk : k = .tuple [] := hty.2
                    subst hk
                    cases hv.2.1 with
                    | inl hU =>
                      rw [hU] at hEv
                      simp only [evalStmt, hEv, hPl]
                    | inr hA =>
                      rw [hA] at hEv
                      simp only [evalStmt, hEv, hPl]
                  | uintBoolPair u a ov =>
                    have hk : k = .tuple [.uint u, .bool] := hty.2
                    subst hk
                    cases v with
                    | aggregate tag fs => simp only [evalStmt, hEv, hPl]
                    | _ => exact False.elim hv.2.1.2.2
    | storageLive l =>
      simp only [stepStmtAbs] at hStep
      cases hD : get? decls l with
      | none => rw [hD] at hStep; nomatch hStep
      | some d =>
        cases hS : get? env l with
        | none => rw [hD, hS] at hStep; nomatch hStep
        | some sl =>
          rw [hD, hS] at hStep
          cases mirAbsEnv_lookup hEnv hS with
          | intro d' hd =>
            cases hd with
            | intro cs hcs =>
              cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
              | intro locals' hSetC =>
                refine ⟨locals', { s.memory with
                  borrows := disableLocalBorrows s.memory.borrows l
                    (length s.memory.callStack) }, ?_, rfl, rfl, rfl, ?_⟩
                · simp only [evalStmt, hcs.2.1, hSetC, hProt]
                · exact setMirAbsSlot_sound hEnv hD hStep hSetC
                    (uninitSlotFor_denote d.ty s.frame.locals)
    | storageDead l =>
      simp only [stepStmtAbs] at hStep
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
              refine ⟨locals', { s.memory with
                borrows := disableLocalBorrows s.memory.borrows l
                  (length s.memory.callStack) }, ?_, rfl, rfl, rfl, ?_⟩
              · simp only [evalStmt, hcs.2.1, hSetC, hProt]
              · exact setMirAbsSlot_sound hEnv hcs.1 hStep hSetC rfl
    | deinit p =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          simp only [stepStmtAbs] at hStep
          cases hD : get? decls l with
          | none => rw [hD] at hStep; nomatch hStep
          | some d =>
            cases hS : get? env l with
            | none => rw [hD, hS] at hStep; nomatch hStep
            | some sl =>
              rw [hD, hS] at hStep
              cases hLv : sl.isLive with
              | false => simp only [hLv] at hStep; nomatch hStep
              | true =>
                simp only [hLv] at hStep
                cases env_live_lookup hEnv hS hLv with
                | intro d' hd =>
                  cases hd with
                  | intro cs hcs =>
                    cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
                    | intro locals' hSetC =>
                      refine ⟨locals', { s.memory with
                        borrows := invalidateConflictingBorrows s.memory.borrows l
                          .none (length s.memory.callStack) }, ?_, rfl, rfl, rfl, ?_⟩
                      · cases cs with
                        | dead => exact absurd rfl hcs.2.2.1
                        | uninit => simp only [evalStmt, hcs.2.1, hSetC, hProt]
                        | init v => simp only [evalStmt, hcs.2.1, hSetC, hProt]
                      · exact setMirAbsSlot_sound hEnv hD hStep hSetC
                          (uninitSlotFor_denote d.ty s.frame.locals)
    | intrinsic intr =>
      cases intr with
      | assume op =>
        simp only [stepStmtAbs] at hStep
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
                  simp only at hStep
                  injection hStep with hStep
                  subst hStep
                  cases evalOperandAbs_sound hEnv hO with
                  | intro v hv =>
                    cases hv with
                    | intro locals' hv =>
                      cases boolAbs_denote_some hv.2.1 with
                      | intro b hb =>
                        have hbt : b = true := hb.2.1
                        subst hbt
                        have hEv := hv.1 s.memory.borrows s.memory.globals layouts
                          s.memory.callerLocals decls s.memory.callStack
                          (Or.inl rfl)
                        rw [hb.1] at hEv
                        refine ⟨locals', s.memory, ?_, rfl, rfl, rfl,
                          refineEnvByGuard_sound hv.2.2.1 hb.2.2⟩
                        simp only [evalStmt, hEv, boolToScalar]
                        rfl
              | _ => nomatch hStep
            | _ => nomatch hStep
      | _ => nomatch hStep
    | assign dst rv =>
      cases dst with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hStep
        | nil =>
          simp only [stepStmtAbs] at hStep
          cases hD : get? decls l with
          | none => rw [hD] at hStep; nomatch hStep
          | some d =>
            rw [hD] at hStep
            cases hR : evalRvalueAbs env rv with
            | none => simp only [hR] at hStep; nomatch hStep
            | some r =>
              cases r with
              | mk av env₁ =>
                simp only [hR] at hStep
                cases hK : av.kindMatches d.ty.kind with
                | false => simp only [hK] at hStep; nomatch hStep
                | true =>
                  cases hS : get? env₁ l with
                  | none => simp only [hK, hS] at hStep; nomatch hStep
                  | some sl =>
                    cases hLv : sl.isLive with
                    | false => simp only [hK, hS, hLv] at hStep; nomatch hStep
                    | true =>
                      simp only [hK, hS, hLv] at hStep
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
                                refine ⟨locals₂, { s.memory with
                                  borrows := invalidateConflictingBorrows
                                    s.memory.borrows l .none
                                    (length s.memory.callStack) },
                                  ?_, rfl, rfl, rfl, ?_⟩
                                · cases cs with
                                  | dead => exact absurd rfl hcs.2.2.1
                                  | uninit =>
                                    simp only [evalStmt, hv.1, hcs.2.1, hSetC, hProt]
                                  | init v' =>
                                    simp only [evalStmt, hv.1, hcs.2.1, hSetC, hProt]
                                · exact setMirAbsSlot_sound hv.2.2 hD hStep hSetC
                                    (mirAbsVal_toSlot_denote hv.2.1
                                      (mirAbsVal_kindOk_of_kindMatches hK))
    | _ => nomatch hStep

/-! ## 9. Terminators -/

/-- Abstract terminator outcome: a verified root-frame `return` with
initialized `_0` slot, or a list of feasible `(target, refinedEnv)` edges. -/
inductive TermAbsOutcome where
  | ret (retSlot : MirAbsSlot)
  | edges (succs : List (Nat × MirAbsEnv))

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

/-- Refine `env` assuming source local `src?` equals `v`. -/
def refineBySrcEq (src? : Option Nat) (u : UintTy) (v : Nat) (env : MirAbsEnv) :
    MirAbsEnv :=
  match src? with
  | some r => refineEnvByGuard env (.ueqConst r u v) true
  | none => env

/-- Refine `env` assuming source local `src?` does not equal `v`. -/
def refineBySrcNe (src? : Option Nat) (u : UintTy) (v : Nat) (env : MirAbsEnv) :
    MirAbsEnv :=
  match src? with
  | some r => refineEnvByGuard env (.uneConst r u v) true
  | none => env

private theorem reduceAbsVal_isInit_of_denote {w x : Nat} {t : Tnum}
    {wi : WrappedInterval} {sc : StridedCong}
    (h : (reduceAbsVal w ⟨.init, t, wi, sc⟩).denote w (some x)) :
    (reduceAbsVal w ⟨.init, t, wi, sc⟩).isInit = true := by
  unfold reduceAbsVal at h ⊢
  cases hv : validWidth w with
  | false => rw [hv] at h; exact False.elim h.1
  | true =>
    rw [hv] at h
    simp only at h ⊢
    cases h1 : (wi.isBot || sc.isBot) with
    | true => rw [h1] at h; exact False.elim h.1
    | false =>
      rw [h1] at h
      simp only at h ⊢
      cases h2 : (t.wf && wi.wf (modPow2 w) && sc.wf) with
      | false => rw [h2] at h; exact False.elim h.1
      | true =>
        rw [h2] at h
        simp only at h ⊢
        cases h3 : (reduceStageWi1 (modPow2 w) t wi).isBot with
        | true => rw [h3] at h; exact False.elim h.1
        | false =>
          rw [h3] at h
          simp only at h ⊢
          cases h4 : reduceStageT1 w t (reduceStageWi1 (modPow2 w) t wi) with
          | none => rw [h4] at h; exact False.elim h.1
          | some t1 =>
            rw [h4] at h
            simp only at h ⊢
            cases h5 : (reduceStageSc1 w t1 sc).isBot with
            | true => rw [h5] at h; exact False.elim h.1
            | false =>
              rw [h5] at h
              simp only at h ⊢
              cases h6 : reduceStageT2 w t1 (reduceStageSc1 w t1 sc) with
              | none => rw [h6] at h; exact False.elim h.1
              | some t2 =>
                rw [h6] at h
                simp only at h ⊢
                cases h7 : (reduceStageWi2
                    (reduceStageWi1 (modPow2 w) t2
                      (reduceStageWi1 (modPow2 w) t wi))
                    (reduceStageSc1 w t1 sc)).isBot with
                | true => rw [h7] at h; exact False.elim h.1
                | false => rfl

private theorem absVal_refineUleConst_isInit {w x bound : Nat} {a : AbsVal}
    (hai : a.isInit = true)
    (h : (AbsVal.refineUleConst w a bound).denote w (some x)) :
    (AbsVal.refineUleConst w a bound).isInit = true := by
  unfold AbsVal.refineUleConst at h ⊢
  cases hV : (validWidth w && a.isInit) with
  | false => rw [hV] at h; exact False.elim h.1
  | true =>
    rw [hV] at h
    simp only at h ⊢
    cases hB : Nat.blt bound (modPow2 w) with
    | false => exact hai
    | true =>
      rw [hB] at h
      exact reduceAbsVal_isInit_of_denote h

private theorem absVal_refineUgtConst_isInit {w x bound : Nat} {a : AbsVal}
    (h : (AbsVal.refineUgtConst w a bound).denote w (some x)) :
    (AbsVal.refineUgtConst w a bound).isInit = true := by
  unfold AbsVal.refineUgtConst at h ⊢
  cases hV : (validWidth w && a.isInit) with
  | false => rw [hV] at h; exact False.elim h.1
  | true =>
    rw [hV] at h
    simp only at h ⊢
    cases hB : Nat.blt (bound + 1) (modPow2 w) with
    | false => rw [hB] at h; exact False.elim h.1
    | true =>
      rw [hB] at h
      exact reduceAbsVal_isInit_of_denote h

private theorem absVal_refineUneConst_isInit {w x v : Nat} {a : AbsVal}
    (hai : a.isInit = true)
    (h : (AbsVal.refineUneConst w a v).denote w (some x)) :
    (AbsVal.refineUneConst w a v).isInit = true := by
  unfold AbsVal.refineUneConst at h ⊢
  cases h0 : Nat.beq v 0 with
  | true =>
    rw [h0] at h
    exact absVal_refineUgtConst_isInit h
  | false =>
    rw [h0] at h
    simp only at h ⊢
    cases hLo : a.lbound? with
    | none =>
      rw [hLo] at h
      simp only at h ⊢
      cases hTop : Nat.beq v (modPow2 w - 1) with
      | true => rw [hTop] at h; exact absVal_refineUleConst_isInit hai h
      | false => exact hai
    | some lo =>
      rw [hLo] at h
      simp only at h ⊢
      cases hEqLo : Nat.beq v lo with
      | true => rw [hEqLo] at h; exact absVal_refineUgtConst_isInit h
      | false =>
        rw [hEqLo] at h
        simp only at h ⊢
        cases hHi : a.ubound? with
        | none =>
          rw [hHi] at h
          simp only at h ⊢
          cases hTop : Nat.beq v (modPow2 w - 1) with
          | true => rw [hTop] at h; exact absVal_refineUleConst_isInit hai h
          | false => exact hai
        | some hi =>
          rw [hHi] at h
          cases hi with
          | zero =>
            simp only at h ⊢
            cases hTop : Nat.beq v (modPow2 w - 1) with
            | true => rw [hTop] at h; exact absVal_refineUleConst_isInit hai h
            | false => exact hai
          | succ k =>
            simp only at h ⊢
            cases hEqHi : Nat.beq v (k + 1) with
            | true =>
              rw [hEqHi] at h
              exact absVal_refineUleConst_isInit hai h
            | false => exact hai

/-- Unfiltered `switchInt` edges for an unsigned discriminant: skips
out-of-range branch values (`v ≥ 2^w`), prunes remaining branches and
`otherwise` on exact match (`decideEq? = some true`), and refines remaining
branches and `otherwise` by `x ≠ v` (`refineUneConst` / `refineBySrcNe`). -/
def uintSwitchEdgesRaw (u : UintTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) :
    List (Nat × BasicBlockIdx) → BasicBlockIdx → List (Nat × MirAbsEnv)
  | [], otherwise =>
    match a.isBot with
    | true => []
    | false => [(otherwise, env)]
  | (v, tgt) :: rest, otherwise =>
    let w := uintWidth u
    match Nat.blt v (modPow2 w) with
    | false => uintSwitchEdgesRaw u a src? env rest otherwise
    | true =>
      match AbsVal.decideEq? w a (AbsVal.const w v) with
      | some true => [(tgt, refineBySrcEq src? u v env)]
      | some false =>
        let a' := AbsVal.refineUneConst w a v
        let env' := refineBySrcNe src? u v env
        uintSwitchEdgesRaw u a' src? env' rest otherwise
      | none =>
        let a' := AbsVal.refineUneConst w a v
        let env' := refineBySrcNe src? u v env
        (tgt, refineBySrcEq src? u v env) ::
          uintSwitchEdgesRaw u a' src? env' rest otherwise

/-- Feasible `switchInt` edges for an unsigned discriminant (with bottom
environments filtered out). -/
def uintSwitchEdges (u : UintTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) : List (Nat × MirAbsEnv) :=
  filterFeasibleEdges (uintSwitchEdgesRaw u a src? env branches otherwise)

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
      some (.edges (uintSwitchEdges u a src? env₁ targets.branches
        targets.otherwise))
    | _ => none
  | .assert cond expected target _ =>
    match evalOperandAbs env cond with
    | some (.bool (.exact c g), env₁) =>
      match boolBeq c expected with
      | true => some (.edges [(target, refineEnvByGuard env₁ g c)])
      | false => none
    | _ => none
  | _ => none

theorem refineBySrcEq_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {src? : Option Nat} {u : UintTy} {x : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x) :
    mirAbsEnvDenote decls (refineBySrcEq src? u x env) locals := by
  cases src? with
  | none => exact hEnv
  | some r =>
    simp only [refineBySrcEq]
    apply refineEnvByGuard_sound hEnv
    intro y hy
    rw [hSrc r rfl] at hy
    injection hy with hy
    subst hy
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem refineBySrcNe_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {src? : Option Nat} {u : UintTy} {x v : Nat}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x)
    (hNe : x ≠ v) :
    mirAbsEnvDenote decls (refineBySrcNe src? u v env) locals := by
  cases src? with
  | none => exact hEnv
  | some r =>
    simp only [refineBySrcNe]
    apply refineEnvByGuard_sound hEnv
    intro y hy
    rw [hSrc r rfl] at hy
    injection hy with hy
    subst hy
    exact ⟨fun _ => hNe, fun _ => rfl⟩

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
        mirAbsEnvDenote decls envT locals
  | [], otherwise, a, env, hEnv, ha, _ => by
    simp only [uintSwitchEdgesRaw, lookupSwitchTarget]
    cases hBot : a.isBot with
    | true => exact False.elim (absVal_not_isBot hBot ha)
    | false => exact ⟨env, List.Mem.head _, hEnv⟩
  | (v, tgt) :: rest, otherwise, a, env, hEnv, ha, hai => by
    have hxLt := (absVal_some_elim ha).1
    simp only [uintSwitchEdgesRaw, lookupSwitchTarget]
    cases hRange : Nat.blt v (modPow2 (uintWidth u)) with
    | false =>
      have hGe : modPow2 (uintWidth u) ≤ v :=
        Nat.le_of_not_lt (fun hLt => by rw [blt_true_of_lt hLt] at hRange; nomatch hRange)
      have hNe : x ≠ v := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt hGe)
      have hBeqF : Nat.beq x v = false := by
        cases hB : Nat.beq x v with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hB) hNe
      rw [hBeqF]
      exact uintSwitchEdgesRaw_sound hSrc rest otherwise a env hEnv ha hai
    | true =>
      have hvLt : v < modPow2 (uintWidth u) := lt_of_blt_true hRange
      cases hXV : Nat.beq x v with
      | true =>
        have hEq := Nat.eq_of_beq_eq_true hXV
        subst hEq
        have hNotFalse : AbsVal.decideEq? (uintWidth u) a
            (AbsVal.const (uintWidth u) x) ≠ some false := by
          intro hDec
          have h := absVal_decideEq?_sound hDec ha
            (absVal_const_denote_lt (uintWidth_valid u) hxLt)
          rw [Nat.beq_refl] at h
          nomatch h
        simp only
        cases hDec : AbsVal.decideEq? (uintWidth u) a (AbsVal.const (uintWidth u) x) with
        | none =>
          exact ⟨_, List.Mem.head _, refineBySrcEq_sound hEnv hSrc⟩
        | some r =>
          cases r with
          | false => exact absurd hDec hNotFalse
          | true => exact ⟨_, List.Mem.head _, refineBySrcEq_sound hEnv hSrc⟩
      | false =>
        have hNe : x ≠ v := nat_ne_of_beq_false hXV
        have hNotTrue : AbsVal.decideEq? (uintWidth u) a
            (AbsVal.const (uintWidth u) v) ≠ some true := by
          intro hDec
          have h := absVal_decideEq?_sound hDec ha
            (absVal_const_denote_lt (uintWidth_valid u) hvLt)
          rw [hXV] at h
          nomatch h
        have ha' : (AbsVal.refineUneConst (uintWidth u) a v).denote
            (uintWidth u) (some x) :=
          absVal_refineUneConst_sound (uintWidth_valid u) ha hai hNe
        have hai' : (AbsVal.refineUneConst (uintWidth u) a v).isInit = true :=
          absVal_refineUneConst_isInit hai ha'
        have hEnv' : mirAbsEnvDenote decls (refineBySrcNe src? u v env) locals :=
          refineBySrcNe_sound hEnv hSrc hNe
        have ih := uintSwitchEdgesRaw_sound hSrc rest otherwise
          (AbsVal.refineUneConst (uintWidth u) a v)
          (refineBySrcNe src? u v env) hEnv' ha' hai'
        simp only
        cases hDec : AbsVal.decideEq? (uintWidth u) a (AbsVal.const (uintWidth u) v) with
        | none =>
          cases ih with
          | intro envT hT => exact ⟨envT, List.Mem.tail _ hT.1, hT.2⟩
        | some r =>
          cases r with
          | true => exact absurd hDec hNotTrue
          | false => exact ih

theorem uintSwitchEdges_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {u : UintTy} {a : AbsVal} {src? : Option Nat}
    {x : Nat} (hEnv : mirAbsEnvDenote decls env locals)
    (ha : a.denote (uintWidth u) (some x)) (hai : a.isInit = true)
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x)
    (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
        (uintSwitchEdges u a src? env branches otherwise) ∧
      mirAbsEnvDenote decls envT locals := by
  cases uintSwitchEdgesRaw_sound hSrc branches otherwise a env hEnv ha hai with
  | intro envT hT =>
    exact ⟨envT, filterFeasibleEdges_mem hT.1 hT.2, hT.2⟩

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
        retSlot.denote d.ty s.frame.locals (.init retVal)
    | .edges succs =>
      ∃ target envT obs locals' mem', List.Mem (target, envT) succs ∧
        evalTerminator s term cb =
          MirStepNode.emitStep obs
            { frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
              memory := mem' } ∧
        mem'.callStack = s.memory.callStack ∧
        mem'.activeCallee = s.memory.activeCallee ∧
        mem'.activeProtectors = s.memory.activeProtectors ∧
        mirAbsEnvDenote decls envT locals' := by
  cases term with
  | mk kind span =>
    cases kind with
    | goto target =>
      injection hTerm with hTerm
      subst hTerm
      exact ⟨target, env, .silent, s.frame.locals, s.memory, List.Mem.head _,
        rfl, rfl, rfl, rfl, hEnv⟩
    | return_ =>
      simp only [stepTermAbs] at hTerm
      cases hS : get? env 0 with
      | none => rw [hS] at hTerm; nomatch hTerm
      | some sl =>
        rw [hS] at hTerm
        cases hI : sl.isInit with
        | false => simp only [hI] at hTerm; nomatch hTerm
        | true =>
          simp only [hI] at hTerm
          injection hTerm with hTerm
          subst hTerm
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
                  d, hcs.1, ?_, ?_⟩
                · simp only [evalTerminator, hL, hProt, hStack,
                    hasFrameDeallocProtectorConflict, hv.2]
                · rw [← hv.1]
                  exact hcs.2.2
    | drop p target unwind =>
      cases p with
      | mk l proj =>
        cases proj with
        | cons _ _ => nomatch hTerm
        | nil =>
          simp only [stepTermAbs] at hTerm
          cases hS : get? env l with
          | none => rw [hS] at hTerm; nomatch hTerm
          | some sl =>
            rw [hS] at hTerm
            cases hLv : sl.isLive with
            | false => simp only [hLv] at hTerm; nomatch hTerm
            | true =>
              simp only [hLv] at hTerm
              cases hSetA : setMirAbsSlot l sl.toUninit env with
              | none => rw [hSetA] at hTerm; nomatch hTerm
              | some env' =>
                rw [hSetA] at hTerm
                injection hTerm with hTerm
                subst hTerm
                cases env_live_lookup hEnv hS hLv with
                | intro d hd =>
                  cases hd with
                  | intro cs hcs =>
                    cases set?_some_of_get? LocalSlot.uninit hcs.2.1 with
                    | intro locals' hSetC =>
                      refine ⟨target, env', .silent, locals',
                        { s.memory with
                          borrows := invalidateConflictingBorrows
                            s.memory.borrows l .none
                            (length s.memory.callStack) },
                        List.Mem.head _, ?_, rfl, rfl, rfl, ?_⟩
                      · cases cs with
                        | dead => exact absurd rfl hcs.2.2.1
                        | uninit =>
                          simp only [evalTerminator, hcs.2.1, hSetC, hProt]
                          rfl
                        | init v =>
                          simp only [evalTerminator, hcs.2.1, hSetC, hProt]
                          rfl
                      · exact setMirAbsSlot_sound hEnv hcs.1 hSetA hSetC
                          (mirAbsSlot_toUninit_denote hLv hcs.2.2.2)
    | switchInt discr targets =>
      simp only [stepTermAbs] at hTerm
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
                simp only at hTerm
                cases hB : boolSwitchEdges env₁ targets ba with
                | none => rw [hB] at hTerm; nomatch hTerm
                | some es =>
                  rw [hB] at hTerm
                  injection hTerm with hTerm
                  subst hTerm
                  cases boolAbs_denote_some hv.2.1 with
                  | intro b hb =>
                    have hEv : evalTerminator s ⟨.switchInt discr targets, span⟩ cb =
                        MirStepNode.emitStep (.event (boolToScalar b).bits)
                          { frame :=
                              { blockIdx :=
                                  lookupSwitchTarget (boolToScalar b).bits
                                    targets.branches targets.otherwise
                                stmtIdx := 0
                                locals := locals' }
                            memory := s.memory } := by
                      simp only [evalTerminator]
                      rw [hEvalT, hb.1]
                    cases ba with
                    | exact c g =>
                      injection hB with hB
                      subst hB
                      have hc : b = c := hb.2.1
                      subst hc
                      have hRef := refineEnvByGuard_sound hv.2.2.1 hb.2.2
                      exact ⟨_, _, _, locals', s.memory,
                        filterFeasibleEdges_mem (List.Mem.head _) hRef,
                        hEv, rfl, rfl, rfl, hRef⟩
                    | top g =>
                      injection hB with hB
                      subst hB
                      have hRef := refineEnvByGuard_sound hv.2.2.1 hb.2
                      cases b with
                      | false =>
                        exact ⟨_, _, _, locals', s.memory,
                          filterFeasibleEdges_mem (List.Mem.head _) hRef,
                          hEv, rfl, rfl, rfl, hRef⟩
                      | true =>
                        exact ⟨_, _, _, locals', s.memory,
                          filterFeasibleEdges_mem
                            (List.Mem.tail _ (List.Mem.head _)) hRef,
                          hEv, rfl, rfl, rfl, hRef⟩
                    | bot => nomatch hB
                    | uninit => nomatch hB
              | uint u a src? =>
                simp only at hTerm
                injection hTerm with hTerm
                subst hTerm
                have hDen := hv.2.1
                cases v with
                | scalar sc =>
                  have hSrc : ∀ r, src? = some r →
                      localUintNat? locals' r u = some sc.bits := by
                    intro r hr
                    have h := hDen.2.2.2
                    rw [hr] at h
                    exact h
                  cases uintSwitchEdges_sound hv.2.2.1 hDen.2.2.1 hDen.1 hSrc
                      targets.branches targets.otherwise with
                  | intro envT hT =>
                    refine ⟨_, envT, .event sc.bits, locals', s.memory, hT.1,
                      ?_, rfl, rfl, rfl, hT.2⟩
                    simp only [evalTerminator]
                    rw [hEvalT]
                | _ => exact False.elim hDen.2
              | unit => nomatch hTerm
              | uintBoolPair _ _ _ => nomatch hTerm
    | assert cond expected target unwind =>
      simp only [stepTermAbs] at hTerm
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
              simp only at hTerm
              cases hBq : boolBeq c expected with
              | false => rw [hBq] at hTerm; nomatch hTerm
              | true =>
                rw [hBq] at hTerm
                injection hTerm with hTerm
                subst hTerm
                have hCE := bool_eq_of_boolBeq hBq
                subst hCE
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
                      have hbc : b = c := hb.2.1
                      subst hbc
                      refine ⟨target, _, .silent, locals', s.memory,
                        List.Mem.head _, ?_, rfl, rfl, rfl,
                        refineEnvByGuard_sound hv.2.2.1 hb.2.2⟩
                      simp only [evalTerminator]
                      rw [hEvalT, hb.1]
                      cases b <;> rfl
            | _ => nomatch hTerm
          | _ => nomatch hTerm
    | _ => nomatch hTerm

end Anneal.AiPcc
