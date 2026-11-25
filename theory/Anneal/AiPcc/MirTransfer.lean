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

* integer (`UintTy`), `bool`, and `()` constants, and `Copy` / `Move` of
  unprojected locals (`Move` leaves the source `LocalSlot.uninit`, exactly as
  `evalOperand` does, and the abstract frame mirrors it);
* unsigned wrapping, unchecked (overflow-free), and `div` / `rem` (nonzero
  divisor) arithmetic, bitwise operations, shifts, comparisons recording
  `RelGuard`s, `UnOp.not` / `UnOp.neg`, and `CastKind.intToInt` casts to
  unsigned targets;
* `assign` to unprojected locals, `storageLive`, `storageDead`, `deinit`,
  `placeMention`, and no-op statements;
* `goto`, `switchInt` (with per-branch guard refinement), `assert` (certified
  to pass), and root-frame `return`.

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

/-- Abstract slot stored by an assignment of `av`. -/
def MirAbsVal.toSlot : MirAbsVal → MirAbsSlot
  | .uint u a _ => .uint u a
  | .bool b => .bool b
  | .unit => .unit true

/-- `av` has MIR type kind `k`. -/
def MirAbsVal.kindOk (av : MirAbsVal) (k : RigidTy) : Prop :=
  match av with
  | .uint u _ _ => k = .uint u
  | .bool _ => k = .bool
  | .unit => k = .tuple []

/-- Decidable check that `av` has MIR type kind `k`. -/
def MirAbsVal.kindMatches (av : MirAbsVal) (k : RigidTy) : Bool :=
  match av, k with
  | .uint u _ _, .uint u' => uintTyBeq u u'
  | .bool _, .bool => true
  | .unit, .tuple [] => true
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
  | .unit => v = .unit

/-- An evaluated value of kind `ty.kind` denotes the assigned slot. -/
theorem mirAbsVal_toSlot_denote {ty : Ty} {locals : List LocalSlot}
    {av : MirAbsVal} {v : Value} (h : av.denote locals v)
    (hk : av.kindOk ty.kind) : av.toSlot.denote ty locals (.init v) := by
  cases av with
  | uint u a src =>
    cases v with
    | scalar sc => exact ⟨hk, h.2.1, h.2.2.1⟩
    | _ => exact False.elim h.2
  | bool b => exact ⟨hk, h⟩
  | unit => exact ⟨hk, h⟩

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
    have hv : v = .unit := h
    rw [hv]

/-- `op` is a `Move` operand (the only operand form that writes `locals`). -/
def operandIsMove : Operand → Bool
  | .move _ => true
  | _ => false

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
        refine ⟨.unit, ?_, fun _ => rfl, hK⟩
        intro locals borrows globals layouts callerLocals cdecls callStack
        simp only [evalOperand, evalConstValue]
      · nomatch h
    | slice _ _ => nomatch h
    | indirect _ _ => nomatch h
    | unevaluated _ => nomatch h

/-! ## 3. Operands -/

/-- Abstract operand evaluation for constants and for `Copy` / `Move` of
unprojected locals. A `Move` leaves the source slot uninitialized (clearing
every guard mentioning it), mirroring `evalOperand`'s `set? .. .uninit`. -/
def evalOperandAbs (env : MirAbsEnv) : Operand → Option (MirAbsVal × MirAbsEnv)
  | .copy p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some (.uint u a) =>
        match a.isInit with
        | true => some (.uint u a (some p.local_), env)
        | false => none
      | some (.bool ba) =>
        match ba.isInit with
        | true => some (.bool ba, env)
        | false => none
      | some (.unit true) => some (.unit, env)
      | _ => none
    | _ :: _ => none
  | .move p =>
    match p.projection with
    | [] =>
      match get? env p.local_ with
      | some (.uint u a) =>
        match a.isInit,
            setMirAbsSlot p.local_ (.uint u (AbsVal.uninit (uintWidth u))) env with
        | true, some env' => some (.uint u a none, env')
        | _, _ => none
      | some (.bool ba) =>
        match ba.isInit, setMirAbsSlot p.local_ (.bool .uninit) env with
        | true, some env' => some (.bool (ba.clearGuardIf p.local_), env')
        | _, _ => none
      | some (.unit true) =>
        match setMirAbsSlot p.local_ (.unit false) env with
        | some env' => some (.unit, env')
        | none => none
      | _ => none
    | _ :: _ => none
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

/-- Soundness of `evalOperandAbs` against `evalOperand` (for every choice of
the borrow/global/caller context, which unprojected locals never consult). -/
theorem evalOperandAbs_sound {decls : List LocalDecl} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {op : Operand} {av : MirAbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hAbs : evalOperandAbs env op = some (av, env')) :
    ∃ v locals',
      (∀ (borrows : List BorrowEntry) (globals : List CapturedAllocation)
        (layouts : LayoutTable) (callerLocals : List LocalSlot)
        (cdecls : List LocalDecl) (callStack : List SavedCallerFrame),
        evalOperand locals op borrows globals layouts callerLocals cdecls
          callStack = .ok v locals') ∧
      av.denote locals' v ∧
      mirAbsEnvDenote decls env' locals' ∧
      (operandIsMove op = false → locals' = locals) ∧
      (∀ layouts, ∃ ty, operandTy decls layouts op = some ty ∧
        av.kindOk ty.kind) := by
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
        refine ⟨v, locals, hv.1 locals, hv.2.1 locals, hEnv, fun _ => rfl, ?_⟩
        intro layouts
        exact ⟨c.ty, rfl, hv.2.2⟩
  | copy p =>
    cases p with
    | mk l proj =>
      cases proj with
      | cons _ _ => nomatch hAbs
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
              have hTy := operandTy_local (layouts := emptyLayoutTable) hcs.1
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
                    refine ⟨.scalar sc, locals, ?_, ?_, hEnv, fun _ => rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack
                      simp only [evalOperand, hL, readProjectedValue]
                    · exact ⟨hI, hsc.2.1, hsc.2.2,
                        localUintNat?_of_get? hL hsc.2.1⟩
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
                    refine ⟨v, locals, ?_, hDen.2, hEnv, fun _ => rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack
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
                    refine ⟨v, locals, ?_, hDen.2, hEnv, fun _ => rfl, ?_⟩
                    · intro borrows globals layouts callerLocals cdecls callStack
                      simp only [evalOperand, hL, readProjectedValue, hv.2]
                    · intro layouts
                      exact ⟨d.ty, (operandTy_local hcs.1).1, hcs.2.2.1⟩
              | top => nomatch hAbs
              | dead => nomatch hAbs
  | move p =>
    cases p with
    | mk l proj =>
      cases proj with
      | cons _ _ => nomatch hAbs
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
                        have hMv : operandIsMove (.move ⟨l, []⟩) = false →
                            locals' = locals := by intro h; cases h
                        refine ⟨.scalar sc, locals', ?_, ?_, ?_, hMv, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack
                          simp only [evalOperand, hL, readProjectedValue, hSetC]
                        · exact ⟨hI, hsc.2.1, hsc.2.2, True.intro⟩
                        · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                            ⟨hcs.2.2.1, absVal_uninit_sound_none⟩
                        · intro layouts
                          exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
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
                        have hMv : operandIsMove (.move ⟨l, []⟩) = false →
                            locals' = locals := by intro h; cases h
                        refine ⟨v, locals', ?_, ?_, ?_, hMv, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack
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
                        have hMv : operandIsMove (.move ⟨l, []⟩) = false →
                            locals' = locals := by intro h; cases h
                        refine ⟨v, locals', ?_, hDen.2, ?_, hMv, ?_⟩
                        · intro borrows globals layouts callerLocals cdecls callStack
                          simp only [evalOperand, hL, readProjectedValue, hv.2,
                            hSetC]
                        · exact setMirAbsSlot_sound hEnv hcs.1 hSA hSetC
                            ⟨hcs.2.2.1, rfl⟩
                        · intro layouts
                          exact ⟨d.ty, (operandTy_local hcs.1).2, hcs.2.2.1⟩
                | top => nomatch hAbs
                | dead => nomatch hAbs

/-! ## 4. Unsigned Value Transfers -/

/-- Upper bound of an initialized, non-wrapping interval component. -/
def AbsVal.ubound? (a : AbsVal) : Option Nat :=
  match a.init, a.wi with
  | .init, .iv lo hi =>
    match Nat.ble lo hi with
    | true => some hi
    | false => none
  | _, _ => none

theorem absVal_ubound?_sound {w x hi : Nat} {a : AbsVal}
    (h : a.ubound? = some hi) (ha : a.denote w (some x)) : x ≤ hi := by
  have hWi := (absVal_some_elim ha).2.2.1
  unfold AbsVal.ubound? at h
  split at h
  · rename_i lo hi' _ hW
    split at h
    · rename_i hB
      injection h with h
      subst h
      rw [hW] at hWi
      simp only [WrappedInterval.denote, hB] at hWi
      exact hWi.2.2.2.2
    · nomatch h
  · nomatch h

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

/-- Exact constant folding of a binary `Nat` operation, else `topInit`. -/
def foldBinAbs (w : Nat) (a1 a2 : AbsVal) (f : Nat → Nat → Nat) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (f x y)
  | _, _ => AbsVal.topInit w

theorem foldBinAbs_sound {w x y : Nat} {a1 a2 : AbsVal} {f : Nat → Nat → Nat}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) :
    (foldBinAbs w a1 a2 f).denote w (some (wrapVal w (f x y))) := by
  unfold foldBinAbs
  split
  · rename_i cx cy hEx hEy
    have h1 := (absVal_exactVal?_sound hEx hx).1
    have h2 := (absVal_exactVal?_sound hEy hy).1
    injection h1 with h1
    injection h2 with h2
    subst h1
    subst h2
    exact absVal_const_sound hw
  · exact absVal_topInit_sound (nat_mod_lt _ (modPow2_pos w))

/-- Exact constant folding of a unary `Nat` operation, else `topInit`. -/
def foldUnAbs (w : Nat) (a : AbsVal) (f : Nat → Nat) : AbsVal :=
  match a.exactVal? w with
  | some x => AbsVal.const w (f x)
  | none => AbsVal.topInit w

theorem foldUnAbs_sound {w x : Nat} {a : AbsVal} {f : Nat → Nat}
    (hw : validWidth w = true) (hx : a.denote w (some x)) :
    (foldUnAbs w a f).denote w (some (wrapVal w (f x))) := by
  unfold foldUnAbs
  split
  · rename_i cx hEx
    have h1 := (absVal_exactVal?_sound hEx hx).1
    injection h1 with h1
    subst h1
    exact absVal_const_sound hw
  · exact absVal_topInit_sound (nat_mod_lt _ (modPow2_pos w))

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

/-- Unsigned division transfer (`x / y ≤ x`). -/
def divUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (x / y)
  | _, _ => topBelow w a1.ubound?

theorem divUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) :
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
    exact topBelow_sound hw hDivLt (fun hi hU =>
      Nat.le_trans (Nat.div_le_self x y) (absVal_ubound?_sound hU hx))

/-- Unsigned remainder transfer (`x % y < y`). -/
def remUintAbs (w : Nat) (a1 a2 : AbsVal) : AbsVal :=
  match a1.exactVal? w, a2.exactVal? w with
  | some x, some y => AbsVal.const w (x % y)
  | _, _ =>
    match a2.ubound? with
    | some hi => topBelow w (some (hi - 1))
    | none => AbsVal.topInit w

theorem remUintAbs_sound {w x y : Nat} {a1 a2 : AbsVal}
    (hw : validWidth w = true) (hx : a1.denote w (some x))
    (hy : a2.denote w (some y)) (hyPos : 0 < y) :
    (remUintAbs w a1 a2).denote w (some (wrapVal w (x % y))) := by
  have hyLt := (absVal_some_elim hy).1
  have hRemLt : x % y < modPow2 w := Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
    (Nat.le_of_lt hyLt)
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
    cases hU : a2.ubound? with
    | none => exact absVal_topInit_sound hRemLt
    | some hi =>
      exact topBelow_sound hw hRemLt (fun hi' hE => by
        injection hE with hE
        subst hE
        exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hyPos)
          (absVal_ubound?_sound hU hy)))

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

/-- Unsigned integer-to-integer cast transfer. Widening (or same-width) casts
keep the abstract value; narrowing casts fold exact values. -/
def castUintAbs (uSrc uDst : UintTy) (a : AbsVal) : AbsVal :=
  match Nat.ble (uintWidth uSrc) (uintWidth uDst) with
  | true => a
  | false =>
    match a.exactVal? (uintWidth uSrc) with
    | some x => AbsVal.const (uintWidth uDst) x
    | none => AbsVal.topInit (uintWidth uDst)

theorem castUintAbs_sound {uSrc uDst : UintTy} {a : AbsVal} {x : Nat}
    (hx : a.denote (uintWidth uSrc) (some x)) :
    (castUintAbs uSrc uDst a).denote (uintWidth uDst)
      (some (wrapVal (uintWidth uDst) x)) := by
  have hxLt := (absVal_some_elim hx).1
  unfold castUintAbs
  cases hB : Nat.ble (uintWidth uSrc) (uintWidth uDst) with
  | true =>
    have hMono := modPow2_uintWidth_mono hB
    simp only
    rw [wrapVal_of_lt (Nat.lt_of_lt_of_le hxLt hMono)]
    exact absVal_denote_widen hMono hx
  | false =>
    simp only
    split
    · rename_i cx hEx
      have h1 := (absVal_exactVal?_sound hEx hx).1
      injection h1 with h1
      subst h1
      exact absVal_const_sound (uintWidth_valid uDst)
    · exact absVal_topInit_sound (nat_mod_lt _ (modPow2_pos _))

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

/-- Guard for `op(copy l, copy r)`. -/
def cmpGuardRegs (op : BinOp) (l r : Nat) (u : UintTy) : RelGuard :=
  match op with
  | .lt => .ultReg l r u
  | .le => .ugeReg r l u
  | .gt => .ultReg r l u
  | .ge => .ugeReg l r u
  | _ => .none

/-- Guard for `op(const v, copy r)` (equalities only). -/
def cmpGuardConstL (op : BinOp) (v : Nat) (r : Nat) (u : UintTy) : RelGuard :=
  match op with
  | .eq => .ueqConst r u v
  | .ne => .uneConst r u v
  | _ => .none

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
  cases op <;> simp only [cmpGuardConstL] <;>
    first
    | exact True.intro
    | skip
  · intro y' hy'
    rw [hy] at hy'
    injection hy' with hy'
    subst hy'
    exact Iff.trans nat_beq_true_iff ⟨Eq.symm, Eq.symm⟩
  · intro y' hy'
    rw [hy] at hy'
    injection hy' with hy'
    subst hy'
    exact Iff.trans nat_not_beq_true_iff ⟨fun h e => h e.symm, fun h e => h e.symm⟩

/-- Synthesize a `RelGuard` for an unsigned comparison from the operands'
source locals and exactly-known values. -/
def synthCmpGuard (op : BinOp) (u : UintTy) (srcL srcR : Option Nat)
    (a1 a2 : AbsVal) : RelGuard :=
  match srcL, a2.exactVal? (uintWidth u) with
  | some r, some v => cmpGuardConstR op r u v
  | _, _ =>
    match srcL, srcR with
    | some l, some r => cmpGuardRegs op l r u
    | _, _ =>
      match srcR, a1.exactVal? (uintWidth u) with
      | some r, some v => cmpGuardConstL op v r u
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
      | some r => exact cmpGuardRegs_sound (hL l rfl) (hR r rfl)
      | none => exact True.intro
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

/-! ## 6. Unsigned Binary Operations -/

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

/-- Abstract unsigned `BinOp` transfer for operands of equal type `u`. -/
def binOpSameAbs (op : BinOp) (u : UintTy) (a1 : AbsVal) (srcL : Option Nat)
    (a2 : AbsVal) (srcR : Option Nat) : Option MirAbsVal :=
  let w := uintWidth u
  match op with
  | .add => some (mkUintVal u (AbsVal.addWrap w a1 a2))
  | .addUnchecked =>
    match AbsVal.noOverflowAdd w a1 a2 with
    | true => some (mkUintVal u (AbsVal.addWrap w a1 a2))
    | false => none
  | .sub => some (mkUintVal u (AbsVal.subWrap w a1 a2))
  | .subUnchecked =>
    match AbsVal.noUnderflowSub w a1 a2 with
    | true => some (mkUintVal u (AbsVal.subWrap w a1 a2))
    | false => none
  | .mul => some (mkUintVal u (foldBinAbs w a1 a2 (fun x y => x * y)))
  | .mulUnchecked =>
    match AbsVal.noOverflowMul w a1 a2 with
    | true => some (mkUintVal u (foldBinAbs w a1 a2 (fun x y => x * y)))
    | false => none
  | .div =>
    match AbsVal.nonzeroDiv w a2 with
    | true => some (mkUintVal u (divUintAbs w a1 a2))
    | false => none
  | .rem =>
    match AbsVal.nonzeroDiv w a2 with
    | true => some (mkUintVal u (remUintAbs w a1 a2))
    | false => none
  | .bitAnd => some (mkUintVal u (AbsVal.bitAnd w a1 a2))
  | .bitOr => some (mkUintVal u (AbsVal.bitOr w a1 a2))
  | .bitXor => some (mkUintVal u (AbsVal.bitXor w a1 a2))
  | .eq | .ne | .lt | .le | .gt | .ge =>
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
  case sub =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_sub locals mem hxLt hyLt,
      mkUintVal_denote (absVal_subWrap_sound hw hx hy hi1 hi2)⟩
  case subUnchecked =>
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
  case mul =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_mul locals mem,
      mkUintVal_denote (foldBinAbs_sound hw hx hy)⟩
  case mulUnchecked =>
    cases hB : AbsVal.noOverflowMul (uintWidth u) a1 a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      exact ⟨_, evalScalarBinOp_uint_mulUnchecked locals mem
        (absVal_noOverflowMul_sound hB hx hy),
        mkUintVal_denote (foldBinAbs_sound hw hx hy)⟩
  case div =>
    cases hB : AbsVal.nonzeroDiv (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      cases absVal_nonzeroDiv_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hEq
        subst hEq
        exact ⟨_, evalScalarBinOp_uint_div locals mem hy'.2.1,
          mkUintVal_denote (divUintAbs_sound hw hx hy)⟩
  case rem =>
    cases hB : AbsVal.nonzeroDiv (uintWidth u) a2 with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h
      injection h with h
      subst h
      cases absVal_nonzeroDiv_sound hB hy with
      | intro y' hy' =>
        injection hy'.1 with hEq
        subst hEq
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
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_bitXor locals mem hxLt hyLt,
      mkUintVal_denote (absVal_bitXor_sound hw hx hy hi1 hi2)⟩
  case eq =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_eq locals mem, cmp_bool_denote hx hy hL hR⟩
  case ne =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_ne locals mem, cmp_bool_denote hx hy hL hR⟩
  case lt =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_lt locals mem, cmp_bool_denote hx hy hL hR⟩
  case le =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_le locals mem, cmp_bool_denote hx hy hL hR⟩
  case gt =>
    injection h with h
    subst h
    exact ⟨_, evalScalarBinOp_uint_gt locals mem, cmp_bool_denote hx hy hL hR⟩
  case ge =>
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

/-! ## 7. Rvalues -/

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

/-- Abstract rvalue evaluation: `use`, unsigned/boolean `UnOp.not`, unsigned
`UnOp.neg`, `CastKind.intToInt` to unsigned targets, and unsigned binary
operations. -/
def evalRvalueAbs (env : MirAbsEnv) : Rvalue → Option (MirAbsVal × MirAbsEnv)
  | .use op => evalOperandAbs env op
  | .unaryOp .not op =>
    match evalOperandAbs env op with
    | some (.bool ba, env₁) => some (.bool (negBoolAbs ba), env₁)
    | some (.uint u a _, env₁) =>
      some (mkUintVal u (foldUnAbs (uintWidth u) a
        (fun x => modPow2 (uintWidth u) - 1 - x)), env₁)
    | _ => none
  | .unaryOp .neg op =>
    match evalOperandAbs env op with
    | some (.uint u a _, env₁) =>
      some (mkUintVal u (foldUnAbs (uintWidth u) a
        (fun x => modPow2 (uintWidth u) - x)), env₁)
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
  | .binaryOp op lhs rhs =>
    match evalOperandAbs env lhs with
    | some (.uint u1 a1 srcL, env₁) =>
      match evalOperandAbs env₁ rhs with
      | some (.uint u2 a2 srcR, env₂) =>
        let srcL' :=
          match operandIsMove rhs with
          | true => none
          | false => srcL
        match binOpUintAbs op u1 a1 srcL' u2 a2 srcR with
        | some av => some (av, env₂)
        | none => none
      | _ => none
    | _ => none
  | _ => none

theorem evalOperandAbs_proj_nil {env : MirAbsEnv} {op : Operand}
    {r : MirAbsVal × MirAbsEnv} (h : evalOperandAbs env op = some r) :
    ∀ p, (op = .copy p ∨ op = .move p) → p.projection = [] := by
  intro p hp
  cases hp with
  | inl hc =>
    subst hc
    cases p with
    | mk l proj =>
      cases proj with
      | nil => rfl
      | cons _ _ => nomatch h
  | inr hm =>
    subst hm
    cases p with
    | mk l proj =>
      cases proj with
      | nil => rfl
      | cons _ _ => nomatch h

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

theorem wrapVal_not_lt {w x : Nat} :
    wrapVal w (modPow2 w - 1 - x) = modPow2 w - 1 - x :=
  wrapVal_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ x)
    (Nat.sub_lt (modPow2_pos w) (Nat.zero_lt_one)))

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
    have hNil := evalOperandAbs_proj_nil hAbs
    cases evalOperandAbs_sound hEnv hAbs with
    | intro v hv =>
      cases hv with
      | intro locals' hv =>
        refine ⟨v, locals', ?_, hv.2.1, hv.2.2.1⟩
        have hVal := validateLoadedValue_ok (layouts := layouts) hv.2.1
          (hv.2.2.2.2 layouts)
        simp only [evalRvalue, hv.1, hVal]
        split
        · rename_i ptrLoc restProj b1 b2 rest heq _
          nomatch hNil _ (Or.inl rfl)
        · rename_i ptrLoc restProj b1 b2 rest heq _
          nomatch hNil _ (Or.inr rfl)
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
              cases hv.2.2.2.2 layouts with
              | intro ty hty =>
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
                    · simp only [evalRvalue, hv.1, hb.1, hty.1]
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
                      refine ⟨.scalar ⟨modPow2 (uintWidth u) - 1 - x, uintBytes u⟩,
                        locals', ?_, ?_, hv.2.2.1⟩
                      · simp only [evalRvalue, hv.1, hty.1]
                        exact evalUnaryNot_uint locals' mem hty.2 hxLt
                      · have h := foldUnAbs_sound (f := fun x =>
                          modPow2 (uintWidth u) - 1 - x)
                          (uintWidth_valid u) hDen.2.2.1
                        rw [wrapVal_not_lt] at h
                        exact mkUintVal_denote h
                  | _ => exact False.elim hDen.2
                | unit => nomatch hAbs
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
                    · simp only [evalRvalue, hv.1, uintBytes_beq_zero]
                      rw [wrapScalarBits_of_lt_uint hxLt, wrapScalarBits_eq_wrapVal,
                        scalarModulus_uintBytes]
                      rfl
                    · exact mkUintVal_denote (foldUnAbs_sound (f := fun x =>
                        modPow2 (uintWidth u) - x) (uintWidth_valid u) hDen.2.2.1)
                | _ => exact False.elim hDen.2
              | bool _ => nomatch hAbs
              | unit => nomatch hAbs
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
                cases hv.2.2.2.2 layouts with
                | intro ty hty =>
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
                        · simp only [evalRvalue, hv.1, uintBytes_beq_zero, hK,
                            intCastTargetBytes_uint, hSg]
                          rw [wrapScalarBits_eq_wrapVal]
                        · exact mkUintVal_denote (castUintAbs_sound hDen.2.2.1)
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
                      · simp only [evalRvalue, hv.1, hb.1, hK,
                          intCastTargetBytes_uint, hSg]
                        simp only [boolToScalar_sizeBytes, Nat.beq]
                        rw [wrapScalarBits_of_lt_uint hbLt]
                      · exact mkUintVal_denote (boolToUintAbs_sound hb.2)
                  | unit => nomatch hAbs
      · nomatch hAbs
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
                cases hB : binOpUintAbs op u1 a1
                    (match operandIsMove rhs with
                      | true => none
                      | false => srcL) u2 a2 srcR with
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
                          cases hv1.2.2.2.2 layouts with
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
                                        mem.callerLocals decls mem.callStack)
                                      (hv2.1 mem.borrows mem.globals layouts
                                        mem.callerLocals decls mem.callStack)
                                    rw [hSg] at hEval
                                    have hLsrc : ∀ r,
                                        (match operandIsMove rhs with
                                          | true => none
                                          | false => srcL) = some r →
                                        localUintNat? locals₂ r u1 = some x := by
                                      intro r hr
                                      cases hMv : operandIsMove rhs with
                                      | true => rw [hMv] at hr; nomatch hr
                                      | false =>
                                        rw [hMv] at hr
                                        have hr' : srcL = some r := hr
                                        rw [hv2.2.2.2.1 hMv]
                                        have h1 := hD1.2.2.2
                                        rw [hr'] at h1
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
        | bool _ => nomatch hAbs
        | unit => nomatch hAbs
  | _ => nomatch hAbs

/-! ## 8. Statements -/

/-- Abstract transfer for a single MIR statement. Assignments, `deinit`, and
`placeMention` are supported on unprojected places only. -/
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

/-- Refine `env` assuming source local `src?` equals `v`. -/
def refineBySrcEq (src? : Option Nat) (u : UintTy) (v : Nat) (env : MirAbsEnv) :
    MirAbsEnv :=
  match src? with
  | some r => refineEnvByGuard env (.ueqConst r u v) true
  | none => env

/-- Feasible `switchInt` edges for an unsigned discriminant: every branch not
statically excluded (refined by equality on the source local), plus
`otherwise`. -/
def uintSwitchEdges (u : UintTy) (a : AbsVal) (src? : Option Nat)
    (env : MirAbsEnv) :
    List (Nat × BasicBlockIdx) → BasicBlockIdx → List (Nat × MirAbsEnv)
  | [], otherwise => [(otherwise, env)]
  | (v, tgt) :: rest, otherwise =>
    match AbsVal.decideEq? (uintWidth u) a (AbsVal.const (uintWidth u) v) with
    | some false => uintSwitchEdges u a src? env rest otherwise
    | _ =>
      (tgt, refineBySrcEq src? u v env) ::
        uintSwitchEdges u a src? env rest otherwise

/-- Feasible `switchInt` edges for a boolean discriminant. -/
def boolSwitchEdges (env : MirAbsEnv) (targets : SwitchTargets) :
    BoolAbs → Option (List (Nat × MirAbsEnv))
  | .exact c g =>
    some [(lookupSwitchTarget (boolToScalar c).bits targets.branches
      targets.otherwise, refineEnvByGuard env g c)]
  | .top g =>
    some [(lookupSwitchTarget (boolToScalar false).bits targets.branches
        targets.otherwise, refineEnvByGuard env g false),
      (lookupSwitchTarget (boolToScalar true).bits targets.branches
        targets.otherwise, refineEnvByGuard env g true)]
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

theorem uintSwitchEdges_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {u : UintTy} {a : AbsVal} {src? : Option Nat}
    {x : Nat} (hEnv : mirAbsEnvDenote decls env locals)
    (ha : a.denote (uintWidth u) (some x))
    (hSrc : ∀ r, src? = some r → localUintNat? locals r u = some x) :
    ∀ (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx),
      ∃ envT, List.Mem (lookupSwitchTarget x branches otherwise, envT)
          (uintSwitchEdges u a src? env branches otherwise) ∧
        mirAbsEnvDenote decls envT locals
  | [], otherwise => ⟨env, List.Mem.head _, hEnv⟩
  | (v, tgt) :: rest, otherwise => by
    have ih := uintSwitchEdges_sound hEnv ha hSrc rest otherwise
    simp only [uintSwitchEdges, lookupSwitchTarget]
    cases hXV : Nat.beq x v with
    | true =>
      have hEq := Nat.eq_of_beq_eq_true hXV
      subst hEq
      have hNotFalse : AbsVal.decideEq? (uintWidth u) a
          (AbsVal.const (uintWidth u) x) ≠ some false := by
        intro hDec
        have hxLt := (absVal_some_elim ha).1
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
      simp only
      cases ih with
      | intro envT hT =>
        cases hDec : AbsVal.decideEq? (uintWidth u) a (AbsVal.const (uintWidth u) v) with
        | none => exact ⟨envT, List.Mem.tail _ hT.1, hT.2⟩
        | some r =>
          cases r with
          | false => exact ⟨envT, hT.1, hT.2⟩
          | true => exact ⟨envT, List.Mem.tail _ hT.1, hT.2⟩

/-- One-step soundness of `stepTermAbs` against `evalTerminator` from a root
frame (`callStack = []`) with no active protectors. Edges are taken via
`MirStepNode.emitStep obs` (`.silent` for `goto` / `assert`, `.event bits`
for `switchInt`), and `return` yields `MirStepNode.retNormal`. -/
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
      ∃ target envT obs locals', List.Mem (target, envT) succs ∧
        evalTerminator s term cb =
          MirStepNode.emitStep obs
            { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
        mirAbsEnvDenote decls envT locals' := by
  cases term with
  | mk kind span =>
    cases kind with
    | goto target =>
      injection hTerm with hTerm
      subst hTerm
      exact ⟨target, env, .silent, s.frame.locals, List.Mem.head _, rfl, hEnv⟩
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
    | switchInt discr targets =>
      simp only [stepTermAbs] at hTerm
      cases hO : evalOperandAbs env discr with
      | none => rw [hO] at hTerm; nomatch hTerm
      | some r =>
        rw [hO] at hTerm
        cases r with
        | mk av env₁ =>
          cases evalOperandAbs_sound hEnv hO with
          | intro v hv =>
            cases hv with
            | intro locals' hv =>
              have hEvalT : ∀ (lay : LayoutTable) (bd : List LocalDecl),
                  evalOperandWithBodyCast s.frame.locals discr s.memory.borrows
                    s.memory.globals lay s.memory.callerLocals bd
                    s.memory.callStack = .ok v locals' := by
                intro lay bd
                unfold evalOperandWithBodyCast
                split <;> exact hv.1 _ _ _ _ _ _
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
                          { s with
                            frame :=
                              { blockIdx :=
                                  lookupSwitchTarget (boolToScalar b).bits
                                    targets.branches targets.otherwise
                                stmtIdx := 0
                                locals := locals' } } := by
                      simp only [evalTerminator]
                      rw [hEvalT, hb.1]
                    cases ba with
                    | exact c g =>
                      injection hB with hB
                      subst hB
                      have hc : b = c := hb.2.1
                      subst hc
                      exact ⟨_, _, _, locals', List.Mem.head _, hEv,
                        refineEnvByGuard_sound hv.2.2.1 hb.2.2⟩
                    | top g =>
                      injection hB with hB
                      subst hB
                      cases b with
                      | false =>
                        exact ⟨_, _, _, locals', List.Mem.head _, hEv,
                          refineEnvByGuard_sound hv.2.2.1 hb.2⟩
                      | true =>
                        exact ⟨_, _, _, locals', List.Mem.tail _ (List.Mem.head _),
                          hEv, refineEnvByGuard_sound hv.2.2.1 hb.2⟩
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
                  cases uintSwitchEdges_sound hv.2.2.1 hDen.2.2.1 hSrc
                      targets.branches targets.otherwise with
                  | intro envT hT =>
                    refine ⟨_, envT, .event sc.bits, locals', hT.1, ?_, hT.2⟩
                    simp only [evalTerminator]
                    rw [hEvalT]
                | _ => exact False.elim hDen.2
              | unit => nomatch hTerm
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
                cases evalOperandAbs_sound hEnv hO with
                | intro v hv =>
                  cases hv with
                  | intro locals' hv =>
                    have hEvalT : ∀ (lay : LayoutTable) (bd : List LocalDecl),
                        evalOperandWithBodyCast s.frame.locals cond s.memory.borrows
                          s.memory.globals lay s.memory.callerLocals bd
                          s.memory.callStack = .ok v locals' := by
                      intro lay bd
                      unfold evalOperandWithBodyCast
                      split <;> exact hv.1 _ _ _ _ _ _
                    cases boolAbs_denote_some hv.2.1 with
                    | intro b hb =>
                      have hbc : b = c := hb.2.1
                      subst hbc
                      refine ⟨target, _, .silent, locals', List.Mem.head _, ?_,
                        refineEnvByGuard_sound hv.2.2.1 hb.2.2⟩
                      simp only [evalTerminator]
                      rw [hEvalT, hb.1]
                      cases b <;> rfl
            | _ => nomatch hTerm
          | _ => nomatch hTerm
    | _ => nomatch hTerm

end Anneal.AiPcc
