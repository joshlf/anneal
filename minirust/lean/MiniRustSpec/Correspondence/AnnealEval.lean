/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.MiniRustEval

/-!
# Symbolic evaluation of Anneal's MIR semantics on fragment bodies

Facts about `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalOperand`,
`evalRvalue`, `evalScalarBinOp`, `evalStmt`, `evalTerminator`, `stepMirFn`)
on fragment statements and terminators. These lemmas only *compute* Anneal's
trusted definitions; they do not restate or modify them.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- Slot facts for Anneal locals (the Anneal half of `FrameOk`). -/
def SlotsOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List LocalDecl) (locals : List LocalSlot) : Prop :=
  ∀ (i : Nat) d slot, decls[i]? = some d → locals[i]? = some slot → DeclSlotOk d slot layouts

theorem SlotsOk.slotOk_scalar {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {locals : List LocalSlot} (hslots : SlotsOk layouts decls locals)
    {j : Nat} {d : LocalDecl} {slot : LocalSlot} {T : Gen.Type}
    (hd : decls[j]? = some d) (hs : locals[j]? = some slot)
    (hT : scalarTypeOf d.ty = some T) :
    SlotOk T slot := by
  have h := (DeclSlotOk_of_scalarTypeOf (layouts := layouts) hT slot).mp (hslots j d slot hd hs)
  rwa [tyOf_of_scalarTypeOf (layouts := layouts) hT] at h

theorem SlotsOk.slotOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {locals : List LocalSlot} (hslots : SlotsOk layouts decls locals)
    {j : Nat} {d : LocalDecl} {slot : LocalSlot} {it : Gen.IntType}
    (hd : decls[j]? = some d) (hs : locals[j]? = some slot)
    (hit : intTypeOf d.ty = some it) :
    SlotOk (.Int it) slot :=
  hslots.slotOk_scalar hd hs (scalarTypeOf_int hit)

theorem elemTyOf_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) :
    ∃ elemTy, MirSemantics.elemTyOf t = some elemTy ∧ intTypeOf elemTy = some elemIt := by
  unfold arrayTypeOf at h
  cases hk : t.kind with
  | array elemKind c =>
    simp only [hk] at h
    cases hb : intTyBytes elemKind with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨s, n⟩ := p
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨{ kind := elemKind, layoutIdx := 0 }, by simp [MirSemantics.elemTyOf, hk],
        by simp [intTypeOf, hb]⟩
  | _ => simp [hk] at h

theorem readProjectedValue_proj (decls : List LocalDecl) (locals : List LocalSlot)
    (count : Nat) (elems : List Value) (hlen : elems.length = count)
    (proj : ProjectionElem) (hproj : projOk decls count proj = true) :
    (∀ idx, projIdx locals count proj = some idx →
      ∃ v, elems[idx]? = some v ∧
        readProjectedValue locals (.aggregate 0 elems) [proj] = .ok v) ∧
    (projIdx locals count proj = none →
      readProjectedValue locals (.aggregate 0 elems) [proj] = .ub) := by
  match proj, hproj with
  | .index idxLocal, hproj =>
    unfold readProjectedValue
    simp only [projIdx, get?]
    cases hs : locals[idxLocal]? with
    | none => simp
    | some slot =>
      cases slot with
      | uninit => simp
      | dead => simp
      | init val =>
        cases val with
        | scalar sc =>
          by_cases hlt : sc.bits < count
          · have hlt' : sc.bits < elems.length := by omega
            refine ⟨fun idx hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
            simp [hlt] at hidx
            subst hidx
            exact ⟨elems[sc.bits], List.getElem?_eq_getElem hlt',
              by simp [List.getElem?_eq_getElem hlt', readProjectedValue]⟩
          · have hge : elems.length ≤ sc.bits := by omega
            simp [hlt, List.getElem?_eq_none hge]
        | _ => simp
  | .constantIndex offset minLen fromEnd, hproj =>
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨⟨hmin, _⟩, _⟩ := hproj
    have hnot_min : ¬ (count < minLen) := by omega
    have hble : Nat.ble minLen count = true := Nat.ble_eq.mpr hmin
    unfold readProjectedValue
    cases fromEnd <;> simp only [projIdx, hnot_min, ↓reduceIte, length, hlen, hble, get?, Nat.sub_eq]
    · by_cases hlt : offset < count
      · have hlt' : offset < elems.length := by omega
        refine ⟨fun idx' hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
        simp [hlt] at hidx
        subst hidx
        exact ⟨elems[offset], List.getElem?_eq_getElem hlt',
          by simp [List.getElem?_eq_getElem hlt', readProjectedValue]⟩
      · have hge : elems.length ≤ offset := by omega
        simp [hlt, List.getElem?_eq_none hge]
    · by_cases hlt : count - offset < count
      · have hlt' : count - offset < elems.length := by omega
        refine ⟨fun idx' hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
        simp [hlt] at hidx
        subst hidx
        exact ⟨elems[count - offset], List.getElem?_eq_getElem hlt',
          by simp [List.getElem?_eq_getElem hlt', readProjectedValue]⟩
      · have hge : elems.length ≤ count - offset := by omega
        simp [hlt, List.getElem?_eq_none hge]

theorem writeProjectedValue_proj (decls : List LocalDecl) (locals : List LocalSlot)
    (count : Nat) (elems : List Value) (hlen : elems.length = count)
    (proj : ProjectionElem) (hproj : projOk decls count proj = true) (newVal : Value) :
    (∀ idx, projIdx locals count proj = some idx →
      writeProjectedValue locals (.aggregate 0 elems) [proj] newVal =
        .ok (.aggregate 0 (elems.set idx newVal))) ∧
    (projIdx locals count proj = none →
      writeProjectedValue locals (.aggregate 0 elems) [proj] newVal = .ub) := by
  match proj, hproj with
  | .index idxLocal, hproj =>
    unfold writeProjectedValue
    simp only [projIdx, get?, set?]
    cases hs : locals[idxLocal]? with
    | none => simp
    | some slot =>
      cases slot with
      | uninit => simp
      | dead => simp
      | init val =>
        cases val with
        | scalar sc =>
          by_cases hlt : sc.bits < count
          · have hlt' : sc.bits < elems.length := by omega
            refine ⟨fun idx hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
            simp [hlt] at hidx
            subst hidx
            simp [hlt', writeProjectedValue]
          · have hge : elems.length ≤ sc.bits := by omega
            simp [hlt, List.getElem?_eq_none hge]
        | _ => simp
  | .constantIndex offset minLen fromEnd, hproj =>
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨⟨hmin, _⟩, _⟩ := hproj
    have hnot_min : ¬ (count < minLen) := by omega
    have hble : Nat.ble minLen count = true := Nat.ble_eq.mpr hmin
    unfold writeProjectedValue
    cases fromEnd <;> simp only [projIdx, hnot_min, ↓reduceIte, length, hlen, hble, get?, set?, Nat.sub_eq]
    · by_cases hlt : offset < count
      · have hlt' : offset < elems.length := by omega
        refine ⟨fun idx' hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
        simp [hlt] at hidx
        subst hidx
        simp [List.getElem?_eq_getElem hlt', hlt, writeProjectedValue]
      · have hge : elems.length ≤ offset := by omega
        simp [hlt, List.getElem?_eq_none hge]
    · by_cases hlt : count - offset < count
      · have hlt' : count - offset < elems.length := by omega
        refine ⟨fun idx' hidx => ?_, fun hnone => by simp [hlt] at hnone⟩
        simp [hlt] at hidx
        subst hidx
        simp [List.getElem?_eq_getElem hlt', hlt, writeProjectedValue]
      · have hge : elems.length ≤ count - offset := by omega
        simp [hlt, List.getElem?_eq_none hge]

theorem evalOperand_copy_nonDeref (locals : List LocalSlot) (p : Place)
    (hnd : ∀ rest, p.projection ≠ .deref :: rest)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand locals (.copy p) borrows globals layouts callerLocals =
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal p.projection with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub := by
  rcases p with ⟨j, projs⟩
  cases projs with
  | nil => rfl
  | cons hd tl =>
    cases hd <;> try rfl
    exact False.elim (hnd tl rfl)

theorem evalOperand_array_proj {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (j : Nat) (proj : ProjectionElem)
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy)
    (hok : operandOk layouts decls it (.copy ⟨j, [proj]⟩) = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals (.copy ⟨j, [proj]⟩) = some bits →
      evalOperand locals (.copy ⟨j, [proj]⟩) borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals (.copy ⟨j, [proj]⟩) = none →
      evalOperand locals (.copy ⟨j, [proj]⟩) borrows globals layouts callerLocals = .ub) := by
  simp only [operandOk, placeOk_single_nonfield hnf, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hj, hok⟩, _⟩ := hok
  have hjl : j < locals.length := by rw [hn]; exact hj
  cases hd : decls[j]? with
  | none => simp [hd] at hok
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
    cases ha : arrayTypeOf d.ty with
    | none => simp [ha] at hok
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨rfl, hproj⟩ := hok
      have hs : locals[j]? = some locals[j] := by simp [hjl]
      have hslot := hslots j d _ hd hs
      have hns := scalarTypeOf_none_of_arrayTypeOf ha
      simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ha] at hslot
      have hnd : ∀ rest, ([proj] : List ProjectionElem) ≠ .deref :: rest := by
        intro rest hr
        cases hr
        simp [projOk] at hproj
      generalize locals[j] = slot at hs hslot
      match slot, hslot with
      | .dead, _ =>
        rw [evalOperand_copy_nonDeref locals ⟨j, [proj]⟩ hnd]
        cases proj with
        | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
        | _ => simp [opBits, get?, hs]
      | .uninit, _ =>
        rw [evalOperand_copy_nonDeref locals ⟨j, [proj]⟩ hnd]
        cases proj with
        | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
        | _ => simp [opBits, get?, hs]
      | .init (.aggregate 0 elems), ⟨hlen, he⟩ =>
        obtain ⟨hrok, hrnone⟩ := readProjectedValue_proj decls locals count elems hlen proj hproj
        rw [evalOperand_copy_nonDeref locals ⟨j, [proj]⟩ hnd]
        simp only [get?, hs]
        have hop : opBits locals (.copy ⟨j, [proj]⟩) =
            match projIdx locals elems.length proj with
            | some idx =>
              match elems[idx]? with
              | some (.scalar sc) => some sc.bits
              | _ => none
            | none => none := by
          cases proj with
          | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
          | _ => dsimp only [opBits]; rw [hs]; rfl
        rw [hop, hlen]
        cases hidx : projIdx locals count proj with
        | none =>
          refine ⟨fun bits hb => by simp at hb, fun _ => ?_⟩
          rw [hrnone hidx]
        | some idx =>
          obtain ⟨v, hv, hrv⟩ := hrok idx hidx
          have hvok := he v (List.mem_of_getElem? hv)
          cases v with
          | scalar sc =>
            obtain ⟨hsz, _⟩ := hvok
            refine ⟨fun bits hb => ?_, fun hnone => by simp [hv] at hnone⟩
            simp [hv] at hb
            subst hb
            rw [hrv, ← hsz]
          | _ => exact False.elim hvok

/-- Evaluating a fragment operand of fragment type `T` (stored like `it`) in
Anneal's semantics: the scalar of its bit pattern, or UB for an uninitialized
local. -/
theorem evalOperand_fragT {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    (hn : locals.length = decls.length)
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (op : Operand)
    (hok : OperandOkT layouts decls T op)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    obtain ⟨hj, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp only [operandType, hd, Option.bind_eq_bind, Option.bind_some] at hty
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots.slotOk_scalar hd hs hty
    unfold evalOperand
    simp only [opBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .dead, _ => simp [hs]
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), hsc =>
      obtain ⟨hsz, _⟩ := hsc
      rw [hT.tyBytes] at hsz
      refine ⟨fun bits hb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hb
      subst hb
      simp [hs, readProjectedValue, ← hsz]
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩ =>
      cases hT <;> simp at htyT
  | .copy ⟨j, [.field 0 fTy]⟩, hok =>
    obtain ⟨hj, ⟨d, hd, htSome⟩, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    simp only [operandType, placeIntType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      cases hf : intTypeOf fTy with
      | none => simp [ht, hf] at hty
      | some fIt =>
        simp only [ht, hf, Option.bind_some] at hty
        by_cases heq : fIt = it'
        · subst heq
          simp at hty
          subst hty
          cases hT with
          | int _ _ =>
            have hs : locals[j]? = some locals[j] := by simp [hjl]
            have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple ht)
            unfold evalOperand
            simp only [opBits, get?]
            generalize locals[j] = slot at hs hslot
            match slot, hslot with
            | .dead, _ => simp [hs]
            | .uninit, _ => simp [hs]
            | .init (.scalar sc), ⟨_, hvb⟩ =>
              simp [intBoolTupleTy, ValidBits] at hvb
            | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, hsz0, _, _, _⟩ =>
              simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
              subst htyT
              refine ⟨fun bits hb => ?_, fun hnone => by simp [hs, readFieldPath] at hnone⟩
              simp [hs, readFieldPath] at hb
              subst hb
              simp [hs, readProjectedValue, get?, ← hsz0]
        · simp [heq] at hty
  | .copy ⟨j, [.field 1 fTy]⟩, hok =>
    obtain ⟨hj, ⟨d, hd, htSome⟩, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      simp only [ht] at hty
      by_cases hbf : isBoolTy fTy = true
      · simp only [hbf, ↓reduceIte, Option.some.injEq] at hty
        subst hty
        cases hT with
        | bool =>
          have hs : locals[j]? = some locals[j] := by simp [hjl]
          have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple ht)
          unfold evalOperand
          simp only [opBits, get?]
          generalize locals[j] = slot at hs hslot
          match slot, hslot with
          | .dead, _ => simp [hs]
          | .uninit, _ => simp [hs]
          | .init (.scalar sc), ⟨_, hvb⟩ =>
            simp [intBoolTupleTy, ValidBits] at hvb
          | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, _, _, _, hsz1, _⟩ =>
            refine ⟨fun bits hb => ?_, fun hnone => by simp [hs, readFieldPath] at hnone⟩
            simp [hs, readFieldPath] at hb
            subst hb
            cases sc1
            simp_all [readProjectedValue, get?, u8Ty]
      · simp [hbf] at hty
  | .constant c, hok =>
    obtain ⟨hty, htr⟩ := hok
    simp only [operandType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    rcases scalarTypeOf_cases hty with ⟨hb, hTb⟩ | ⟨it', hit', hTi⟩ | ⟨ho, _⟩ | ⟨_, ht, _⟩
    · subst hTb
      cases hT
      simp only [translateOperand, hb, ↓reduceIte] at he
      match hv : c.val, he with
      | .scalar (.int ⟨bits, sz⟩), he =>
        simp only at he
        split at he
        · next hc =>
          obtain ⟨hsz, _⟩ := hc
          subst hsz
          refine ⟨fun bits' hb' => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
          simp [opBits, hv] at hb'
          subst hb'
          simp [evalOperand, hv, evalConstValue, u8Ty]
        · simp at he
    · subst hTi
      cases hT with
      | int _ _ =>
        simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
          ↓reduceIte] at he
        match hv : c.val, he with
        | .scalar (.int ⟨bits, sz⟩), he =>
          simp only at he
          split at he
          · next hc =>
            obtain ⟨hsz, _⟩ := hc
            refine ⟨fun bits' hb => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
            simp [opBits, hv] at hb
            subst hb
            simp [evalOperand, hv, evalConstValue, hsz]
          · simp at he
    · simp [translateOperand_ordering_const ho] at he
    · simp [translateOperand_tuple_const ht] at he

theorem evalOperand_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (op : Operand) (hok : operandOk layouts decls it op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  have hT : FragTy (.Int it) it := .int it (operandOk_good hok)
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hty⟩, _⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    rw [hd] at hty
    simp only [Option.bind_eq_bind, Option.bind_some] at hty
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots.slotOk hd hs hty
    unfold evalOperand
    simp only [opBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .dead, _ => simp [hs]
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), hsc =>
      obtain ⟨hsz, _⟩ := hsc
      rw [hT.tyBytes] at hsz
      refine ⟨fun bits hb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hb
      subst hb
      simp [hs, readProjectedValue, ← hsz]
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩ =>
      simp [tupleIntOfTy] at htyT
  | .copy ⟨j, proj :: rest⟩, hok =>
    cases proj with
    | field idx fieldTy =>
      simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hj, hok⟩, _⟩ := hok
      have hjl : j < locals.length := by rw [hn]; exact hj
      cases hd : decls[j]? with
      | none => simp [hd] at hok
      | some d =>
        simp only [hd] at hok
        cases hij : intBoolTupleOf d.ty with
        | some tupIt =>
          simp only [hij] at hok
          cases idx with
          | zero =>
            cases rest with
            | nil =>
              cases hf : intTypeOf fieldTy with
              | none => simp [hf] at hok
              | some fIt =>
                simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                have hs : locals[j]? = some locals[j] := by simp [hjl]
                have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple hij)
                unfold evalOperand
                simp only [opBits, get?]
                generalize locals[j] = slot at hs hslot
                match slot, hslot with
                | .dead, _ => simp [hs]
                | .uninit, _ => simp [hs]
                | .init (.scalar sc), ⟨_, hvb⟩ =>
                  simp [intBoolTupleTy, ValidBits] at hvb
                | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, hsz0, _, _, _⟩ =>
                  simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
                  subst htyT
                  refine ⟨fun bits hb => ?_, fun hnone => by simp [hs, readFieldPath] at hnone⟩
                  simp [hs, readFieldPath] at hb
                  subst hb
                  simp [hs, readProjectedValue, get?, ← hsz0]
            | cons _ _ => simp at hok
          | succ _ => simp at hok
        | none =>
          simp only [hij] at hok
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hok
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            simp only [ht] at hok
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: rest) with
            | none => simp [hres] at hok
            | some rpair =>
              obtain ⟨relOff, leafSpec⟩ := rpair
              simp only [hres] at hok
              cases leafSpec with
              | tuple _ _ _ => simp at hok
              | scalar leafIt =>
                simp only [decide_eq_true_eq] at hok
                subst hok
                have hs : locals[j]? = some locals[j] := by simp [hjl]
                have hslot := hslots j d _ hd hs
                have hns := scalarTypeOf_none_of_tupleTypeOf ht
                have harr := arrayTypeOf_none_of_tupleTypeOf ht
                simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                  harr, ht] at hslot
                have hnd : ∀ tl, (.field idx fieldTy :: rest) ≠ .deref :: tl := by
                  intro _ hc; cases hc
                generalize locals[j] = slot at hs hslot
                match slot, hslot with
                | .dead, _ =>
                  rw [evalOperand_copy_nonDeref locals ⟨j, .field idx fieldTy :: rest⟩ hnd]
                  simp [opBits, get?, hs]
                | .uninit, _ =>
                  rw [evalOperand_copy_nonDeref locals ⟨j, .field idx fieldTy :: rest⟩ hnd]
                  simp [opBits, get?, hs]
                | .init rootVal, ⟨hwf, hval⟩ =>
                  obtain ⟨leafVal, hread, hleafOk, _, hprojRead⟩ :=
                    resolveFieldPath_read hwf hval hres
                  cases leafVal with
                  | scalar sc =>
                    simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafOk
                    obtain ⟨hsz, _⟩ := hleafOk
                    refine ⟨fun bits hb => ?_, fun hnone => by simp [opBits, hs, hread] at hnone⟩
                    simp [opBits, hs, hread] at hb
                    subst hb
                    simp [evalOperand_copy_nonDeref locals ⟨j, .field idx fieldTy :: rest⟩ hnd,
                      get?, hs, hprojRead locals, ← hsz]
                  | _ => simp [TupleSpec.valOk] at hleafOk
    | index idxLocal =>
      cases rest with
      | nil =>
        exact evalOperand_array_proj decls locals hslots hn it j (.index idxLocal)
          (by intro _ _ h; cases h) hok borrows globals callerLocals
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | nil =>
        exact evalOperand_array_proj decls locals hslots hn it j
          (.constantIndex offset minLen fromEnd)
          (by intro _ _ h; cases h) hok borrows globals callerLocals
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | deref =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, projOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        split at hok <;> simp at hok
      | cons _ _ => simp [operandOk, placeOk] at hok
    | _ => cases rest <;> simp [operandOk, placeOk, projOk, translateOperand, translatePlace] at hok
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact evalOperand_fragT decls locals hslots hn hT (.constant c)
      ⟨operandType_of_operandIntType hok.1, hok.2⟩ borrows globals callerLocals

theorem wrap_eq_toNat (v : Nat) (n : Nat) :
    MirSemantics.wrapScalarBits v (MirSemantics.scalarModulus n) = (((v : Int)) % 2 ^ (8 * n)).toNat := by
  rw [wrapScalarBits_eq, scalarModulus_eq]
  have : ((v : Int) % 2 ^ (8 * n)) = ((v % 2 ^ (8 * n) : Nat) : Int) := by
    rw [Int.natCast_emod]; push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem scalarPow2_eq (k : Nat) : MirSemantics.scalarPow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 2 * MirSemantics.scalarPow2 k = 2 ^ (k + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem two_pow_div_two (n : Nat) (hn : 0 < n) : Nat.div (2 ^ n) 2 = 2 ^ (n - 1) := by
  change 2 ^ n / 2 = 2 ^ (n - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Nat.pow_succ]

theorem two_pow_byte_split (sz : Nat) (hsz : sz ≠ 0) :
    2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) ∧ 2 ≤ 2 ^ (8 * sz - 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 8 * sz = k + 1 := ⟨8 * sz - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 8 * sz - 1)

theorem nat_ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

theorem nat_div_eq_div (a b : Nat) : Nat.div a b = a / b := rfl

theorem nat_mod_eq_mod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem isSignedNegative_eq (v sz : Nat) (hsz : sz ≠ 0) (hv : v < 2 ^ (8 * sz)) :
    MirSemantics.isSignedNegative v sz = decide (2 ^ (8 * sz - 1) ≤ v) := by
  simp only [MirSemantics.isSignedNegative, nat_beq_eq_decide, decide_eq_false hsz,
    scalarModulus_eq, two_pow_div_two (8 * sz) (by omega), wrapScalarBits_eq,
    Nat.mod_eq_of_lt hv, nat_ble_eq_decide]

theorem canRepresent_unsigned (sz : Nat) (hsz : sz ≠ 0) (v : Int) :
    IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ v =
      decide (0 ≤ v ∧ v < ((2 ^ (8 * sz) : Nat) : Int)) := by
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  apply Bool.eq_iff_iff.mpr
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simp [Size.bits]; omega)]
  simp only [windowLo, Size.bits, decide_eq_true_eq]
  rw [hp]
  omega

theorem canRepresent_signed (sz : Nat) (hsz : sz ≠ 0) (v : Int) :
    IntType.can_represent ⟨.Signed, ⟨sz⟩⟩ v =
      decide (-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ v ∧ v < ((2 ^ (8 * sz - 1) : Nat) : Int)) := by
  have hp1 : (2 : Int) ^ (8 * sz - 1) = ((2 ^ (8 * sz - 1) : Nat) : Int) := by push_cast; rfl
  have hp2 : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  apply Bool.eq_iff_iff.mpr
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simp [Size.bits]; omega)]
  have hpred := two_pow_pred_add (8 * sz) (by omega)
  simp only [windowLo, Size.bits, decide_eq_true_eq]
  rw [hp1, hp2] at hpred ⊢
  omega

theorem nat_emod_toNat_of_lt (q M : Nat) (hqM : q < M) :
    ((q : Int) % (M : Int)).toNat = q := by
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem neg_nat_emod_toNat (q M : Nat) (hq0 : 0 < q) (hqM : q < M) :
    ((- (q : Int)) % (M : Int)).toNat = M - q := by
  have : (- (q : Int)) % (M : Int) = (- (q : Int)) + (M : Int) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

theorem tdiv_nat_nat (a b : Nat) :
    Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl

theorem tmod_nat_nat (a b : Nat) :
    Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

theorem tdiv_nat_neg (a b : Nat) (hb : b ≠ 0) :
    Int.tdiv (a : Int) (-(b : Int)) = -((a / b : Nat) : Int) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_nat_neg (a b : Nat) (hb : b ≠ 0) :
    Int.tmod (a : Int) (-(b : Int)) = ((a % b : Nat) : Int) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tdiv_neg_nat (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tdiv (-(a : Int)) (b : Int) = -((a / b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_neg_nat (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tmod (-(a : Int)) (b : Int) = -((a % b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tdiv_neg_neg (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tdiv (-(a : Int)) (-(b : Int)) = ((a / b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_neg_neg (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tmod (-(a : Int)) (-(b : Int)) = -((a % b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem signedOverflowAdd_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowAdd x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hsum_lt : (x + y) % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ (by omega)
  have hsum_mod : (x + y) % 2 ^ (8 * sz) =
      if x + y < 2 ^ (8 * sz) then x + y else x + y - 2 ^ (8 * sz) := by
    split
    · next hlt => exact Nat.mod_eq_of_lt hlt
    · next hge =>
      have heq : x + y = (x + y - 2 ^ (8 * sz)) + 2 ^ (8 * sz) := by omega
      conv => lhs; rw [heq]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedOverflowAdd, scalarModulus_eq, Nat.add_eq, wrapScalarBits_eq,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    isSignedNegative_eq _ sz hsz hsum_lt, canRepresent_signed sz hsz,
    intFromBits]
  rw [hsum_mod, hp]
  clear hp hsum_lt hsum_mod
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxyM : x + y < M
  · simp only [hxyM, ↓reduceIte]
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hsH : H ≤ x + y <;>
      simp [hxH, hyH, hsH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega
  · simp only [hxyM, ↓reduceIte]
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hsH : H ≤ x + y - M <;>
      simp [hxH, hyH, hsH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega

theorem signedOverflowSub_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowSub x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedOverflowSub, scalarModulus_eq, Nat.add_eq, Nat.sub_eq,
    wrapScalarBits_eq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, nat_ble_eq_decide,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    canRepresent_signed sz hsz, intFromBits]
  rw [hp]
  clear hp
  by_cases hyx : y ≤ x
  · have hlt : x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_true hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq _ sz hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega
  · have hlt : 2 ^ (8 * sz) + x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_false hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq _ sz hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ M + x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega

theorem signedOverflowMul_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowMul x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ * intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  unfold MirSemantics.signedOverflowMul
  simp only [nat_beq_eq_decide, decide_eq_false hsz, scalarModulus_eq,
    two_pow_div_two (8 * sz) (by omega), wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_ble_eq_decide, Nat.sub_eq, Nat.mul_eq, canRepresent_signed sz hsz, intFromBits]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  rw [hp]
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxH : x < H <;> by_cases hyH : y < H
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hmul : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
    rw [hmul]
    generalize x * y = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_true (by omega : H ≤ y)]
    have hmul : (x : Int) * ((y : Int) - (M : Int)) = -((x * (M - y) : Nat) : Int) := by
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hy', Int.mul_neg]; push_cast; rfl
    rw [hmul]
    generalize x * (M - y) = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hmul : ((x : Int) - (M : Int)) * (y : Int) = -(((M - x) * y : Nat) : Int) := by
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      rw [hx', Int.neg_mul]; push_cast; rfl
    rw [hmul]
    generalize (M - x) * y = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_true (by omega : H ≤ y)]
    have hmul : ((x : Int) - (M : Int)) * ((y : Int) - (M : Int)) =
        (((M - x) * (M - y) : Nat) : Int) := by
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hx', hy', Int.neg_mul_neg]; push_cast; rfl
    rw [hmul]
    generalize (M - x) * (M - y) = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega

theorem intFromBits_eq_zero_iff (it : Gen.IntType) (hsz : it.size.bytes ≠ 0)
    (v : Nat) (hv : v < 2 ^ (8 * it.size.bytes)) :
    intFromBits v it = 0 ↔ v = 0 := by
  have hzero : intFromBits 0 it = 0 := by
    rcases it with ⟨s, ⟨sz⟩⟩
    cases s with
    | Unsigned => rfl
    | Signed => simp [intFromBits, Nat.two_pow_pos _]
  rw [← hzero]
  exact intFromBits_inj it v 0 hv (Nat.two_pow_pos _)

theorem evalSignedDiv_spec (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval .Div (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = some z →
      MirSemantics.evalSignedDiv x y sz locals mem =
        .ok (.scalar ⟨(z % 2 ^ (8 * sz)).toNat, sz⟩) locals mem) ∧
    (intBinEval .Div (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = none →
      MirSemantics.evalSignedDiv x y sz locals mem = .ub) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hyInt0 : intFromBits y ⟨.Signed, ⟨sz⟩⟩ ≠ 0 := by
    rw [Ne, intFromBits_eq_zero_iff ⟨.Signed, ⟨sz⟩⟩ hsz y hy]; exact hy0
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.evalSignedDiv, intBinEval, hyInt0, ↓reduceIte, scalarModulus_eq,
    Nat.mul_eq, Nat.sub_eq, Nat.mul_comm sz 8, scalarPow2_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_beq_eq_decide, nat_div_eq_div, canRepresent_signed sz hsz]
  rw [hp]
  by_cases hovf : x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1
  · obtain ⟨rfl, rfl⟩ := hovf
    have hnot1 : ¬(2 ^ (8 * sz - 1) < 2 ^ (8 * sz - 1)) := Nat.lt_irrefl _
    have hnot2 : ¬(2 ^ (8 * sz) - 1 < 2 ^ (8 * sz - 1)) := by omega
    simp only [decide_true, Bool.and_self, intFromBits, hnot1, hnot2, ↓reduceIte]
    rw [hp]
    have hx' : ((2 ^ (8 * sz - 1) : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((2 ^ (8 * sz - 1) : Nat) : Int) := by omega
    have hy' : ((2 ^ (8 * sz) - 1 : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((1 : Nat) : Int) := by omega
    rw [hx', hy', tdiv_neg_neg _ 1 (by omega) (by omega), Nat.div_one]
    rw [decide_eq_false (by omega : ¬(-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ ((2 ^ (8 * sz - 1) : Nat) : Int) ∧
        ((2 ^ (8 * sz - 1) : Nat) : Int) < ((2 ^ (8 * sz - 1) : Nat) : Int)))]
    simp
  · have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
      rw [Bool.and_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    simp only [hcond, intFromBits]
    rw [hp]
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hovf ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy hovf ⊢
    by_cases hxH : x < H <;> by_cases hyH : y < H
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_false (by omega : ¬(H ≤ y))]
      rw [tdiv_nat_nat]
      have hqH : x / y < H := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxH
      generalize x / y = q at hqH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hq0 : q = 0
      · subst hq0; simp
      · rw [decide_eq_false hq0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : q < M), nat_emod_toNat_of_lt q M (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_true (by omega : H ≤ y)]
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hy', tdiv_nat_neg x (M - y) (by omega)]
      have hqH : x / (M - y) < H := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxH
      generalize x / (M - y) = q at hqH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hq0 : q = 0
      · subst hq0; simp
      · rw [decide_eq_false hq0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - q < M),
          neg_nat_emod_toNat q M (by omega) (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_false (by omega : ¬(H ≤ y))]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      rw [hx', tdiv_neg_nat (M - x) y (by omega) hy0]
      have hqH : (M - x) / y ≤ H := Nat.le_trans (Nat.div_le_self _ _) (by omega)
      generalize (M - x) / y = q at hqH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hq0 : q = 0
      · subst hq0; simp
      · rw [decide_eq_false hq0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - q < M),
          neg_nat_emod_toNat q M (by omega) (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_true (by omega : H ≤ y)]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hx', hy', tdiv_neg_neg (M - x) (M - y) (by omega) (by omega)]
      have hqH : (M - x) / (M - y) < H := by
        by_cases hxEq : x = H
        · rw [hxEq, show M - H = H by omega]
          exact Nat.div_lt_self (by omega) (by omega)
        · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      generalize (M - x) / (M - y) = q at hqH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hq0 : q = 0
      · subst hq0; simp
      · rw [decide_eq_false hq0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : q < M), nat_emod_toNat_of_lt q M (by omega)]

theorem evalSignedRem_spec (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval .Rem (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = some z →
      MirSemantics.evalSignedRem x y sz locals mem =
        .ok (.scalar ⟨(z % 2 ^ (8 * sz)).toNat, sz⟩) locals mem) ∧
    (intBinEval .Rem (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = none →
      MirSemantics.evalSignedRem x y sz locals mem = .ub) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hyInt0 : intFromBits y ⟨.Signed, ⟨sz⟩⟩ ≠ 0 := by
    rw [Ne, intFromBits_eq_zero_iff ⟨.Signed, ⟨sz⟩⟩ hsz y hy]; exact hy0
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.evalSignedRem, intBinEval, hyInt0, ↓reduceIte, scalarModulus_eq,
    Nat.mul_eq, Nat.sub_eq, Nat.mul_comm sz 8, scalarPow2_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_beq_eq_decide, nat_mod_eq_mod, canRepresent_signed sz hsz]
  rw [hp]
  by_cases hovf : x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1
  · obtain ⟨rfl, rfl⟩ := hovf
    have hnot1 : ¬(2 ^ (8 * sz - 1) < 2 ^ (8 * sz - 1)) := Nat.lt_irrefl _
    have hnot2 : ¬(2 ^ (8 * sz) - 1 < 2 ^ (8 * sz - 1)) := by omega
    simp only [decide_true, Bool.and_self, intFromBits, hnot1, hnot2, ↓reduceIte]
    rw [hp]
    have hx' : ((2 ^ (8 * sz - 1) : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((2 ^ (8 * sz - 1) : Nat) : Int) := by omega
    have hy' : ((2 ^ (8 * sz) - 1 : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((1 : Nat) : Int) := by omega
    rw [hx', hy', tdiv_neg_neg _ 1 (by omega) (by omega), Nat.div_one]
    rw [decide_eq_false (by omega : ¬(-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ ((2 ^ (8 * sz - 1) : Nat) : Int) ∧
        ((2 ^ (8 * sz - 1) : Nat) : Int) < ((2 ^ (8 * sz - 1) : Nat) : Int)))]
    simp
  · have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
      rw [Bool.and_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    simp only [hcond, intFromBits]
    rw [hp]
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hovf ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy hovf ⊢
    by_cases hxH : x < H <;> by_cases hyH : y < H
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_false (by omega : ¬(H ≤ y))]
      rw [tdiv_nat_nat, tmod_nat_nat]
      have hqH : x / y < H := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxH
      have hrH : x % y < H := Nat.lt_trans (Nat.mod_lt x (by omega)) hyH
      generalize x / y = q at hqH ⊢
      generalize x % y = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_true (by omega : H ≤ y)]
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hy', tdiv_nat_neg x (M - y) (by omega), tmod_nat_neg x (M - y) (by omega)]
      have hqH : x / (M - y) < H := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxH
      have hrH : x % (M - y) ≤ H :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
      generalize x / (M - y) = q at hqH ⊢
      generalize x % (M - y) = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_false (by omega : ¬(H ≤ y))]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      rw [hx', tdiv_neg_nat (M - x) y (by omega) hy0, tmod_neg_nat (M - x) y (by omega) hy0]
      have hqH : (M - x) / y ≤ H := Nat.le_trans (Nat.div_le_self _ _) (by omega)
      have hrH : (M - x) % y < H := Nat.lt_trans (Nat.mod_lt _ (by omega)) hyH
      generalize (M - x) / y = q at hqH ⊢
      generalize (M - x) % y = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - r < M),
          neg_nat_emod_toNat r M (by omega) (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_true (by omega : H ≤ y)]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hx', hy', tdiv_neg_neg (M - x) (M - y) (by omega) (by omega),
        tmod_neg_neg (M - x) (M - y) (by omega) (by omega)]
      have hqH : (M - x) / (M - y) < H := by
        by_cases hxEq : x = H
        · rw [hxEq, show M - H = H by omega]
          exact Nat.div_lt_self (by omega) (by omega)
        · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      have hrH : (M - x) % (M - y) ≤ H :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
      generalize (M - x) / (M - y) = q at hqH ⊢
      generalize (M - x) % (M - y) = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - r < M),
          neg_nat_emod_toNat r M (by omega) (by omega)]

theorem wrap_add_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.wrapScalarBits (x + y) (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it + intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.add_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  push_cast; rfl

theorem wrap_sub_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    (let m := MirSemantics.scalarModulus it.size.bytes
      match Nat.ble y x with
      | true => MirSemantics.wrapScalarBits (x - y) m
      | false => MirSemantics.wrapScalarBits (m + MirSemantics.wrapScalarBits x m -
          MirSemantics.wrapScalarBits y m) m) =
      ((intFromBits x it - intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  dsimp only
  have hp : (2 : Int) ^ (8 * it.size.bytes) = ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by
    push_cast; rfl
  have hmod : (intFromBits x it - intFromBits y it) % 2 ^ (8 * it.size.bytes) =
      ((x : Int) - (y : Int)) % 2 ^ (8 * it.size.bytes) := by
    rw [Int.sub_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  rw [hmod, hp]
  clear hp hmod
  simp only [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    nat_ble_eq_decide]
  generalize 2 ^ (8 * it.size.bytes) = M at hx hy ⊢
  by_cases hle : y ≤ x
  · rw [decide_eq_true hle]; dsimp only
    rw [Nat.mod_eq_of_lt (by omega : x - y < M)]
    have hcast : (x : Int) - (y : Int) = ((x - y : Nat) : Int) := by omega
    rw [hcast, nat_emod_toNat_of_lt (x - y) M (by omega)]
  · rw [decide_eq_false hle]; dsimp only
    rw [Nat.mod_eq_of_lt (by omega : M + x - y < M)]
    have hcast : (x : Int) - (y : Int) = -((y - x : Nat) : Int) := by omega
    rw [hcast, neg_nat_emod_toNat (y - x) M (by omega) (by omega)]
    omega

theorem wrap_mul_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.wrapScalarBits (x * y) (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it * intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.mul_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  push_cast; rfl

theorem bits_dvd_two_pow (lhsSz rhsSz : Nat) (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsSz) :
    ((8 * lhsSz : Nat) : Int) ∣ (2 : Int) ^ (8 * rhsSz) := by
  rcases hlhs with rfl | rfl | rfl | rfl | rfl <;>
    rcases hrhs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem bits_le_half_modulus (lhsSz rhsSz : Nat) (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsSz) :
    8 * lhsSz ≤ 2 ^ (8 * rhsSz - 1) := by
  rcases hlhs with rfl | rfl | rfl | rfl | rfl <;>
    rcases hrhs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem shift_offset_eq (it rhsIt : Gen.IntType) (hlhs : GoodSize it.size.bytes)
    (hrhs : GoodSize rhsIt.size.bytes) (y : Nat) :
    (intFromBits y rhsIt % (Size.bits it.size : Int)).toNat = y % (it.size.bytes * 8) := by
  rcases it with ⟨_, ⟨lhsSz⟩⟩
  rcases rhsIt with ⟨s, ⟨rhsSz⟩⟩
  dsimp only [Size.bits] at hlhs hrhs ⊢
  rw [Nat.mul_comm lhsSz 8]
  have hcast : ((y % (8 * lhsSz) : Nat) : Int) = (y : Int) % ((8 * lhsSz : Nat) : Int) := by
    rw [Int.natCast_emod]
  cases s with
  | Unsigned =>
    simp only [intFromBits]
    rw [← hcast, Int.toNat_natCast]
  | Signed =>
    simp only [intFromBits]
    split
    · rw [← hcast, Int.toNat_natCast]
    · have hdvd := bits_dvd_two_pow lhsSz rhsSz hlhs hrhs
      rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
        Int.emod_emod, ← hcast, Int.toNat_natCast]

theorem unchecked_shift_oob_iff (it rhsIt : Gen.IntType) (hlhs : GoodSize it.size.bytes)
    (hrhs : GoodSize rhsIt.size.bytes) (y : Nat) (hy : y < 2 ^ (8 * rhsIt.size.bytes)) :
    (intFromBits y rhsIt < 0 ∨ intFromBits y rhsIt ≥ (Size.bits it.size : Int)) ↔
      it.size.bytes * 8 ≤ y := by
  rcases it with ⟨_, ⟨lhsSz⟩⟩
  rcases rhsIt with ⟨s, ⟨rhsSz⟩⟩
  dsimp only [Size.bits] at hlhs hrhs hy ⊢
  rw [Nat.mul_comm lhsSz 8]
  have hle := bits_le_half_modulus lhsSz rhsSz hlhs hrhs
  have hp : (2 : Int) ^ (8 * rhsSz) = ((2 ^ (8 * rhsSz) : Nat) : Int) := by push_cast; rfl
  cases s with
  | Unsigned =>
    simp only [intFromBits]
    omega
  | Signed =>
    simp only [intFromBits, hp]
    split <;> omega

theorem unchecked_shift_toNat (lhsSz : Nat) (rhsIt : Gen.IntType)
    (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsIt.size.bytes)
    (y : Nat) (hlt : y < lhsSz * 8) :
    (intFromBits y rhsIt).toNat = y := by
  rcases rhsIt with ⟨signed, ⟨rhsSz⟩⟩
  dsimp only at hrhs ⊢
  have hle := bits_le_half_modulus lhsSz rhsSz hlhs hrhs
  cases signed with
  | Unsigned => simp [intFromBits]
  | Signed =>
    have hyHalf : y < 2 ^ (8 * rhsSz - 1) := by omega
    simp [intFromBits, hyHalf]

theorem shiftLeftBits_eq (v k m : Nat) :
    MirSemantics.shiftLeftBits v k m = MirSemantics.wrapScalarBits (v * 2 ^ k) m := by
  simp [MirSemantics.shiftLeftBits, Nat.mul_eq, scalarPow2_eq]

theorem shiftLeftBits_intFromBits (it : Gen.IntType) (x k : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.shiftLeftBits x k (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it * (2 : Int) ^ k) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [shiftLeftBits_eq, wrap_eq_toNat]
  congr 1
  have hcast : ((x * 2 ^ k : Nat) : Int) = (x : Int) * (2 : Int) ^ k := by push_cast; rfl
  have hxMod : (x : Int) % (2 : Int) ^ (8 * it.size.bytes) = (x : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  rw [hcast, Int.mul_emod (intFromBits x it), intFromBits_emod x it hx,
    Int.mul_emod (x : Int), hxMod]

theorem shiftRightUnsignedBits_eq (v k : Nat) :
    MirSemantics.shiftRightUnsignedBits v k = v / 2 ^ k := by
  simp [MirSemantics.shiftRightUnsignedBits, nat_div_eq_div, scalarPow2_eq]

theorem shiftRightUnsigned_intFromBits (sz x k : Nat) (hx : x < 2 ^ (8 * sz)) :
    MirSemantics.wrapScalarBits (MirSemantics.shiftRightUnsignedBits x k)
      (MirSemantics.scalarModulus sz) =
      ((intFromBits x ⟨.Unsigned, ⟨sz⟩⟩ / (2 : Int) ^ k) % 2 ^ (8 * sz)).toNat := by
  have hlt : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hdiv : (x : Int) / (2 : Int) ^ k = ((x / 2 ^ k : Nat) : Int) := by
    have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    rw [hpk]; rfl
  simp only [shiftRightUnsignedBits_eq, wrapScalarBits_eq, scalarModulus_eq,
    Nat.mod_eq_of_lt hlt, intFromBits]
  rw [hdiv, hp, nat_emod_toNat_of_lt _ _ hlt]

theorem arithmeticShrBits_intFromBits (sz x k : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hk : k < 8 * sz) :
    MirSemantics.arithmeticShrBits x sz k =
      ((intFromBits x ⟨.Signed, ⟨sz⟩⟩ / (2 : Int) ^ k) % 2 ^ (8 * sz)).toNat := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  have hsplit : 2 ^ (8 * sz) = 2 ^ (8 * sz - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hQpos : 0 < 2 ^ (8 * sz - k) := Nat.two_pow_pos _
  have hSpos : 0 < 2 ^ k := Nat.two_pow_pos _
  have hqlt : x / 2 ^ k < 2 ^ (8 * sz - k) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsplit]; exact hx)
  have hltM : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [MirSemantics.arithmeticShrBits, scalarModulus_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, shiftRightUnsignedBits_eq, isSignedNegative_eq x sz hsz hx,
    Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_comm sz 8, scalarPow2_eq, intFromBits]
  rw [hp, hpk]
  by_cases hxH : 2 ^ (8 * sz - 1) ≤ x
  · rw [decide_eq_true hxH]; dsimp only
    simp only [show ¬(x < 2 ^ (8 * sz - 1)) by omega, ↓reduceIte]
    have hdiv : ((x : Int) - ((2 ^ (8 * sz) : Nat) : Int)) / ((2 ^ k : Nat) : Int) =
        ((x / 2 ^ k : Nat) : Int) - ((2 ^ (8 * sz - k) : Nat) : Int) := by
      have hrew : (x : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
          (x : Int) + (-((2 ^ (8 * sz - k) : Nat) : Int)) * ((2 ^ k : Nat) : Int) := by
        have hmul : ((2 ^ (8 * sz - k) * 2 ^ k : Nat) : Int) =
            ((2 ^ (8 * sz - k) : Nat) : Int) * ((2 ^ k : Nat) : Int) := by push_cast; rfl
        rw [hsplit, hmul, Int.neg_mul]; omega
      rw [hrew, Int.add_mul_ediv_right _ _ (by omega)]
      have hed : (x : Int) / ((2 ^ k : Nat) : Int) = ((x / 2 ^ k : Nat) : Int) := rfl
      rw [hed]; omega
    rw [hdiv]
    generalize x / 2 ^ k = q at hqlt ⊢
    generalize 2 ^ (8 * sz - k) = Q at hsplit hqlt hQpos ⊢
    generalize 2 ^ (8 * sz) = M at hsplit ⊢
    have hQM : Q ≤ M := by
      have : Q * 1 ≤ Q * 2 ^ k := Nat.mul_le_mul_left Q hSpos
      omega
    rw [Nat.mod_eq_of_lt (by omega : q + (M - Q) < M)]
    have hemod : ((q : Int) - (Q : Int)) % (M : Int) = (q : Int) - (Q : Int) + (M : Int) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hemod]
    omega
  · rw [decide_eq_false hxH]; dsimp only
    simp only [show x < 2 ^ (8 * sz - 1) by omega, ↓reduceIte, Nat.mod_eq_of_lt hltM]
    have hed : (x : Int) / ((2 ^ k : Nat) : Int) = ((x / 2 ^ k : Nat) : Int) := rfl
    rw [hed, nat_emod_toNat_of_lt _ _ hltM]

theorem emod_pow_succ_two (w : Int) (k : Nat) :
    (w % (2 : Int) ^ (k + 1)) % 2 = w % 2 :=
  Int.emod_emod_of_dvd w ⟨(2 : Int) ^ k, by rw [Int.pow_succ, Int.mul_comm]⟩

theorem ediv_two_emod_pow (w : Int) (k : Nat) :
    (w / 2) % (2 : Int) ^ k = (w % (2 : Int) ^ (k + 1)) / 2 := by
  have hM : 0 < (2 : Int) ^ k := two_pow_pos k
  have h2M : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by rw [Int.pow_succ, Int.mul_comm]
  rw [h2M]
  generalize (2 : Int) ^ k = M at hM ⊢
  have hr0 : 0 ≤ w % (2 * M) := Int.emod_nonneg w (by omega)
  have hrlt : w % (2 * M) < 2 * M := Int.emod_lt_of_pos w (by omega)
  have hw : w = w % (2 * M) + (M * (w / (2 * M))) * 2 := by
    have hdiv := Int.emod_def w (2 * M)
    have hmul : 2 * M * (w / (2 * M)) = (M * (w / (2 * M))) * 2 := by
      rw [Int.mul_assoc, Int.mul_comm 2 _]
    omega
  conv => lhs; rw [hw]
  rw [Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0),
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

theorem two_mul_add_bit_emod_toNat (Q : Int) (bit k : Nat) (hbit : bit < 2) :
    ((2 * Q + (bit : Int)) % (2 : Int) ^ (k + 1)).toNat =
      bit + 2 * (Q % (2 : Int) ^ k).toNat := by
  have hM : 0 < (2 : Int) ^ k := two_pow_pos k
  have h2M : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by rw [Int.pow_succ, Int.mul_comm]
  rw [h2M]
  generalize (2 : Int) ^ k = M at hM ⊢
  have hr0 : 0 ≤ Q % M := Int.emod_nonneg Q (by omega)
  have hrlt : Q % M < M := Int.emod_lt_of_pos Q hM
  have hrew : 2 * Q + (bit : Int) = (2 * (Q % M) + (bit : Int)) + (2 * M) * (Q / M) := by
    have hdiv := Int.emod_def Q M
    have hmul : 2 * (M * (Q / M)) = (2 * M) * (Q / M) := (Int.mul_assoc 2 M (Q / M)).symm
    omega
  rw [hrew, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem intBitMeasure_pos {a : Int} (h0 : a ≠ 0) (h1 : a ≠ -1) : 0 < intBitMeasure a := by
  simp only [intBitMeasure]; split <;> omega

theorem intBitMeasure_ediv_lt {a : Int} (h0 : a ≠ 0) (h1 : a ≠ -1) :
    intBitMeasure (a / 2) < intBitMeasure a := by
  simp only [intBitMeasure]; split <;> (try split) <;> omega

theorem intBitRec_irrel (z o : Int → Int) (f : Int → Int → Int) (n m : Nat) (a b : Int)
    (hn : intBitMeasure a ≤ n) (hm : intBitMeasure a ≤ m) :
    intBitRec z o f n a b = intBitRec z o f m a b := by
  induction n generalizing m a b with
  | zero =>
    by_cases ha0 : a = 0
    · subst ha0; cases m <;> simp [intBitRec]
    · by_cases ha1 : a = -1
      · subst ha1; cases m <;> simp [intBitRec]
      · exact absurd (intBitMeasure_pos ha0 ha1) (by omega)
  | succ n ih =>
    by_cases ha0 : a = 0
    · subst ha0; cases m <;> simp [intBitRec]
    · by_cases ha1 : a = -1
      · subst ha1; cases m <;> simp [intBitRec]
      · have hpos := intBitMeasure_pos ha0 ha1
        have hlt := intBitMeasure_ediv_lt ha0 ha1
        cases m with
        | zero => exact absurd hpos (by omega)
        | succ m =>
          simp only [intBitRec, ha0, ha1, ↓reduceIte]
          rw [ih m (a / 2) (b / 2) (by omega) (by omega)]

theorem intBitRec_unfold (z o : Int → Int) (f : Int → Int → Int) (a b : Int) :
    intBitRec z o f (intBitMeasure a) a b =
      if a = 0 then z b
      else if a = -1 then o b
      else 2 * intBitRec z o f (intBitMeasure (a / 2)) (a / 2) (b / 2) + f (a % 2) (b % 2) := by
  rw [intBitRec_irrel z o f (intBitMeasure a) (intBitMeasure a + 1) a b (Nat.le_refl _) (Nat.le_succ _)]
  simp only [intBitRec]
  by_cases ha0 : a = 0
  · simp [ha0]
  · by_cases ha1 : a = -1
    · simp [ha1]
    · simp only [ha0, ha1, ↓reduceIte]
      have hlt := intBitMeasure_ediv_lt ha0 ha1
      rw [intBitRec_irrel z o f (intBitMeasure a) (intBitMeasure (a / 2)) (a / 2) (b / 2)
        (by omega) (Nat.le_refl _)]

theorem intBitAnd_unfold (a b : Int) :
    intBitAnd a b =
      if a = 0 then 0
      else if a = -1 then b
      else 2 * intBitAnd (a / 2) (b / 2) + (if a % 2 = 1 ∧ b % 2 = 1 then 1 else 0) :=
  intBitRec_unfold _ _ _ a b

theorem intBitOr_unfold (a b : Int) :
    intBitOr a b =
      if a = 0 then b
      else if a = -1 then -1
      else 2 * intBitOr (a / 2) (b / 2) + (if a % 2 = 1 ∨ b % 2 = 1 then 1 else 0) :=
  intBitRec_unfold _ _ _ a b

theorem intBitXor_unfold (a b : Int) :
    intBitXor a b =
      if a = 0 then b
      else if a = -1 then -b - 1
      else 2 * intBitXor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1) :=
  intBitRec_unfold _ _ _ a b

theorem intBitAnd_step (a b : Int) :
    intBitAnd a b = 2 * intBitAnd (a / 2) (b / 2) + (if a % 2 = 1 ∧ b % 2 = 1 then 1 else 0) := by
  rw [intBitAnd_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitAnd_unfold 0 (b / 2)]
    simp
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitAnd_unfold (-1) (b / 2)]
      simp only [show (-1 : Int) ≠ 0 by decide, ↓reduceIte, true_and]
      split <;> omega
    · simp [ha0, ha1]

theorem intBitOr_step (a b : Int) :
    intBitOr a b = 2 * intBitOr (a / 2) (b / 2) + (if a % 2 = 1 ∨ b % 2 = 1 then 1 else 0) := by
  rw [intBitOr_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitOr_unfold 0 (b / 2)]
    simp only [↓reduceIte, show (0 : Int) = 1 ↔ False by decide, false_or]
    split <;> omega
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitOr_unfold (-1) (b / 2)]
      simp [show (-1 : Int) ≠ 0 by decide]
    · simp [ha0, ha1]

theorem intBitXor_step (a b : Int) :
    intBitXor a b = 2 * intBitXor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1) := by
  rw [intBitXor_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitXor_unfold 0 (b / 2)]
    simp only [↓reduceIte]
    split <;> omega
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitXor_unfold (-1) (b / 2)]
      simp only [show (-1 : Int) ≠ 0 by decide, ↓reduceIte]
      split <;> omega
    · simp [ha0, ha1]

theorem bitwiseAndBits_eq_intBitAnd (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseAndBits k x y = (intBitAnd a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseAndBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseAndBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitAnd_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = 1 ∧ ((y % 2 : Nat) : Int) = 1 then (1 : Int) else 0) =
          (((match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with
              | true => 1 | false => 0) : Nat) : Int) ∧
        (match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem bitwiseOrBits_eq_intBitOr (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseOrBits k x y = (intBitOr a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseOrBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseOrBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitOr_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = 1 ∨ ((y % 2 : Nat) : Int) = 1 then (1 : Int) else 0) =
          (((match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with
              | true => 1 | false => 0) : Nat) : Int) ∧
        (match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem bitwiseXorBits_eq_intBitXor (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseXorBits k x y = (intBitXor a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseXorBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseXorBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitXor_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = ((y % 2 : Nat) : Int) then (0 : Int) else 1) =
          (((match Nat.beq (x % 2) (y % 2) with
              | true => 0 | false => 1) : Nat) : Int) ∧
        (match Nat.beq (x % 2) (y % 2) with | true => 0 | false => 1) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem intFromBits_emod_nat (it : Gen.IntType) (v : Nat) (hv : v < 2 ^ (8 * it.size.bytes)) :
    intFromBits v it % (2 : Int) ^ (8 * it.size.bytes) = (v : Int) % (2 : Int) ^ (8 * it.size.bytes) := by
  rw [intFromBits_emod v it hv, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hv)]

theorem bitwiseAndBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseAndBits (it.size.bytes * 8) x y =
      (intBitAnd (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseAndBits_eq_intBitAnd (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem bitwiseOrBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseOrBits (it.size.bytes * 8) x y =
      (intBitOr (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseOrBits_eq_intBitOr (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem bitwiseXorBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseXorBits (it.size.bytes * 8) x y =
      (intBitXor (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseXorBits_eq_intBitXor (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem evalScalarBinOp_frag (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (it rhsIt : Gen.IntType) (hgood : GoodSize it.size.bytes) (hrhsGood : GoodSize rhsIt.size.bytes)
    (hhom : isShiftIntBinOp iop = false → rhsIt = it)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * rhsIt.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it = some z →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
        .ok (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem) ∧
    (intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it = none →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) = .ub) := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hrhsSz : rhsIt.size.bytes ≠ 0 := Nat.ne_of_gt hrhsGood.pos
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hgood hsz hx ⊢
  have hbeq : Nat.beq sz 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hrhsBeq : Nat.beq rhsIt.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hrhsSz]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  match op, hop with
  | .add, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq,
      wrap_add_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .sub, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hsub := wrap_sub_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy
    dsimp only at hsub
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq]
    cases hble : Nat.ble y x <;> simp only [hble] at hsub ⊢ <;> rw [hsub]
  | .mul, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      wrap_mul_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitAnd, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseAndBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitOr, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseOrBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitXor, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseXorBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .addUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      by_cases hlt : x + y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x + y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hcast : (x : Int) + (y : Int) = ((x + y : Nat) : Int) := by push_cast; rfl
        rw [hcast, hp, nat_emod_toNat_of_lt (x + y) _ hlt]
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x + y),
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq, intBinEval,
        signedOverflowAdd_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        simp [wrap_add_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy]
  | .subUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      by_cases hle : y ≤ x
      · have hlt : x - y < 2 ^ (8 * sz) := by omega
        rw [decide_eq_true hle, decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x - y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hcast : (x : Int) - (y : Int) = ((x - y : Nat) : Int) := by omega
        rw [hcast, hp, nat_emod_toNat_of_lt (x - y) _ hlt]
      · rw [decide_eq_false hle,
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq, intBinEval,
        signedOverflowSub_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hsub := wrap_sub_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy
        dsimp only at hsub
        have hxMod : MirSemantics.wrapScalarBits x (MirSemantics.scalarModulus sz) = x := by
          rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
        have hyMod : MirSemantics.wrapScalarBits y (MirSemantics.scalarModulus sz) = y := by
          rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
        simp only [hxMod, hyMod] at hsub ⊢
        cases hble : Nat.ble y x <;> simp only [hble, Bool.not_true] at hsub ⊢ <;> rw [hsub]
  | .mulUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      have hcast : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
      by_cases hlt : x * y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x * y)), hcast,
          decide_eq_true (by omega : 0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt (x * y) _ hlt]
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x * y), hcast,
          decide_eq_false (by omega : ¬(0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq, intBinEval,
        signedOverflowMul_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ * intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        simp [wrap_mul_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy]
  | .div, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    by_cases hy0 : y = 0
    · subst hy0
      have hyInt0 := (intFromBits_eq_zero_iff ⟨signed, ⟨sz⟩⟩ hsz 0 (Nat.two_pow_pos _)).mpr rfl
      simp [evalScalarBinOp, hbeq, Nat.beq_refl, intBinEval, hyInt0]
    · have hyBeq : Nat.beq y 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hy0]
      cases signed with
      | Unsigned =>
        have hyInt0 : (y : Int) ≠ 0 := by omega
        have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq, nat_div_eq_div, wrapScalarBits_eq,
          scalarModulus_eq, Nat.mod_eq_of_lt hqlt, intBinEval, intFromBits, hyInt0, ↓reduceIte,
          canRepresent_unsigned sz hsz]
        rw [tdiv_nat_nat]
        generalize x / y = q at hqlt ⊢
        rw [decide_eq_true (by omega : 0 ≤ (q : Int) ∧ (q : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt q _ hqlt]
      | Signed =>
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq]
        exact evalSignedDiv_spec x y sz hsz hx hy hy0 locals mem
  | .rem, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    by_cases hy0 : y = 0
    · subst hy0
      have hyInt0 := (intFromBits_eq_zero_iff ⟨signed, ⟨sz⟩⟩ hsz 0 (Nat.two_pow_pos _)).mpr rfl
      simp [evalScalarBinOp, hbeq, Nat.beq_refl, intBinEval, hyInt0]
    · have hyBeq : Nat.beq y 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hy0]
      cases signed with
      | Unsigned =>
        have hyInt0 : (y : Int) ≠ 0 := by omega
        have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx
        have hrlt : x % y < 2 ^ (8 * sz) := Nat.lt_trans (Nat.mod_lt x (by omega)) hy
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq, nat_mod_eq_mod, wrapScalarBits_eq,
          scalarModulus_eq, Nat.mod_eq_of_lt hrlt, intBinEval, intFromBits, hyInt0, ↓reduceIte,
          canRepresent_unsigned sz hsz]
        rw [tdiv_nat_nat, tmod_nat_nat]
        generalize x / y = q at hqlt ⊢
        generalize x % y = r at hrlt ⊢
        rw [decide_eq_true (by omega : 0 ≤ (q : Int) ∧ (q : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt r _ hrlt]
      | Signed =>
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq]
        exact evalSignedRem_spec x y sz hsz hx hy hy0 locals mem
  | .shl, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hoff := shift_offset_eq ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y
    dsimp only at hoff
    simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
      shiftLeftBits_intFromBits ⟨signed, ⟨sz⟩⟩ x _ hx]
  | .shr, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hoff := shift_offset_eq ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y
    dsimp only at hoff
    have hklt : y % (sz * 8) < 8 * sz := by rw [Nat.mul_comm]; exact Nat.mod_lt _ (by omega)
    cases signed with
    | Unsigned =>
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
        shiftRightUnsigned_intFromBits sz x _ hx]
    | Signed =>
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
        arithmeticShrBits_intFromBits sz x _ hsz hx hklt]
  | .shlUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hoob := unchecked_shift_oob_iff ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y hy
    dsimp only at hoob
    by_cases hle : sz * 8 ≤ y
    · have hoob' : intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int) := hoob.mpr hle
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_true hle,
        intBinEval, hoob']
    · have hnoob : ¬(intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int)) := by
        rw [hoob]; exact hle
      have htoNat := unchecked_shift_toNat sz rhsIt hgood hrhsGood y (by omega)
      simp only [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_false hle,
        intBinEval, hnoob, ↓reduceIte, htoNat]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      simp [shiftLeftBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx]
  | .shrUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hoob := unchecked_shift_oob_iff ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y hy
    dsimp only at hoob
    by_cases hle : sz * 8 ≤ y
    · have hoob' : intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int) := hoob.mpr hle
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_true hle,
        intBinEval, hoob']
    · have hnoob : ¬(intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int)) := by
        rw [hoob]; exact hle
      have htoNat := unchecked_shift_toNat sz rhsIt hgood hrhsGood y (by omega)
      have hklt : y < 8 * sz := by omega
      simp only [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_false hle,
        intBinEval, hnoob, ↓reduceIte, htoNat]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      cases signed with
      | Unsigned => simp [shiftRightUnsigned_intFromBits sz x y hx]
      | Signed => simp [arithmeticShrBits_intFromBits sz x y hsz hx hklt]

/-- The bit pattern of a fragment operand of type `T` is valid at `T`. -/
theorem opBits_valid {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) {T : Gen.Type} {it : Gen.IntType} (_hT : FragTy T it)
    (op : Operand) (hok : OperandOkT layouts decls T op) (bits : Nat)
    (hb : opBits locals op = some bits) :
    ValidBits T bits := by
  match op, hok, hb with
  | .copy ⟨j, []⟩, hok, hb =>
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp only [operandType, hd, Option.bind_eq_bind, Option.bind_some] at hty
    simp only [opBits] at hb
    match hs : locals[j]?, hb with
    | some (.init (.scalar sc)), hb =>
      simp at hb; subst hb
      exact (hslots.slotOk_scalar hd hs hty).2
  | .copy ⟨j, [.field 0 fTy]⟩, hok, hb =>
    obtain ⟨_, ⟨d, hd, htSome⟩, hty⟩ := hok
    simp only [operandType, placeIntType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      cases hf : intTypeOf fTy with
      | none => simp [ht, hf] at hty
      | some fIt =>
        simp only [ht, hf, Option.bind_some] at hty
        by_cases heq : fIt = it'
        · subst heq
          simp at hty
          subst hty
          simp only [opBits] at hb
          cases hs : locals[j]? with
          | none => simp [hs] at hb
          | some slot =>
            have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple ht)
            match slot, hslot, hb with
            | .dead, _, hb => simp [hs] at hb
            | .uninit, _, hb => simp [hs] at hb
            | .init (.scalar sc), ⟨_, hvb⟩, _ =>
              simp [intBoolTupleTy, ValidBits] at hvb
            | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, _, hb0, _, _⟩, hb =>
              simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
              subst htyT
              simp [hs, readFieldPath] at hb
              subst hb
              exact hb0
        · simp [heq] at hty
  | .copy ⟨j, [.field 1 fTy]⟩, hok, hb =>
    obtain ⟨_, ⟨d, hd, htSome⟩, hty⟩ := hok
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      simp only [ht] at hty
      by_cases hbf : isBoolTy fTy = true
      · simp only [hbf, ↓reduceIte, Option.some.injEq] at hty
        subst hty
        simp only [opBits] at hb
        cases hs : locals[j]? with
        | none => simp [hs] at hb
        | some slot =>
          have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple ht)
          match slot, hslot, hb with
          | .dead, _, hb => simp [hs] at hb
          | .uninit, _, hb => simp [hs] at hb
          | .init (.scalar sc), ⟨_, hvb⟩, _ =>
            simp [intBoolTupleTy, ValidBits] at hvb
          | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, _, _, _, _, hb1⟩, hb =>
            simp [hs, readFieldPath] at hb
            subst hb
            exact hb1
      · simp [hbf] at hty
  | .constant c, hok, hb =>
    obtain ⟨hty, htr⟩ := hok
    simp only [operandType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [opBits] at hb
    rcases scalarTypeOf_cases hty with ⟨hbool, hTb⟩ | ⟨it', hit', hTi⟩ | ⟨ho, _⟩ | ⟨_, ht, _⟩
    · subst hTb
      simp only [translateOperand, hbool, ↓reduceIte] at he
      match hv : c.val, he, hb with
      | .scalar (.int ⟨bits', sz⟩), he, hb =>
        simp only at he hb
        simp at hb; subst hb
        split at he
        · next hc => exact hc.2
        · simp at he
    · subst hTi
      simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
        ↓reduceIte] at he
      match hv : c.val, he, hb with
      | .scalar (.int ⟨bits', sz⟩), he, hb =>
        simp only at he hb
        simp at hb; subst hb
        split at he
        · next hc => obtain ⟨hsz, hlt⟩ := hc; subst hsz; exact hlt
        · simp at he
    · simp [translateOperand_ordering_const ho] at he
    · simp [translateOperand_tuple_const ht] at he

theorem opBits_lt {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals)
    (it : Gen.IntType) (op : Operand) (hok : operandOk layouts decls it op = true) (bits : Nat)
    (hb : opBits locals op = some bits) : bits < 2 ^ (8 * it.size.bytes) := by
  have hT : FragTy (.Int it) it := .int it (operandOk_good hok)
  match op, hok, hb with
  | .copy ⟨j, []⟩, hok, hb =>
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hty⟩, _⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    rw [hd] at hty
    simp only [Option.bind_eq_bind, Option.bind_some] at hty
    simp only [opBits] at hb
    match hs : locals[j]?, hb with
    | some (.init (.scalar sc)), hb =>
      simp at hb; subst hb
      exact (hslots.slotOk hd hs hty).2
  | .copy ⟨j, proj :: rest⟩, hok, hb =>
    cases proj with
    | field idx fieldTy =>
      simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hok⟩, _⟩ := hok
      cases hd : decls[j]? with
      | none => simp [hd] at hok
      | some d =>
        simp only [hd] at hok
        cases hij : intBoolTupleOf d.ty with
        | some tupIt =>
          simp only [hij] at hok
          cases idx with
          | zero =>
            cases rest with
            | nil =>
              cases hf : intTypeOf fieldTy with
              | none => simp [hf] at hok
              | some fIt =>
                simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                simp only [opBits] at hb
                cases hs : locals[j]? with
                | none => simp [hs] at hb
                | some slot =>
                  have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple hij)
                  match slot, hslot, hb with
                  | .dead, _, hb => simp [hs] at hb
                  | .uninit, _, hb => simp [hs] at hb
                  | .init (.scalar sc), ⟨_, hvb⟩, _ =>
                    simp [intBoolTupleTy, ValidBits] at hvb
                  | .init (.aggregate 0 [.scalar sc0, .scalar sc1]),
                      ⟨it'', htyT, _, hb0, _, _⟩, hb =>
                    simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
                    subst htyT
                    simp [hs, readFieldPath] at hb
                    subst hb
                    exact hb0
            | cons _ _ => simp at hok
          | succ _ => simp at hok
        | none =>
          simp only [hij] at hok
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hok
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            simp only [ht] at hok
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: rest) with
            | none => simp [hres] at hok
            | some rpair =>
              obtain ⟨_, leafSpec⟩ := rpair
              simp only [hres] at hok
              cases leafSpec with
              | tuple _ _ _ => simp at hok
              | scalar leafIt =>
                simp only [decide_eq_true_eq] at hok
                subst hok
                simp only [opBits] at hb
                match hs : locals[j]?, hb with
                | some (.init rootVal), hb =>
                  simp only at hb
                  have hslot := hslots j d _ hd hs
                  have hns := scalarTypeOf_none_of_tupleTypeOf ht
                  have harr := arrayTypeOf_none_of_tupleTypeOf ht
                  simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                    harr, ht] at hslot
                  obtain ⟨hwf, hval⟩ := hslot
                  obtain ⟨leafVal, hread, hleafOk, _, _⟩ := resolveFieldPath_read hwf hval hres
                  rw [hread] at hb
                  cases leafVal with
                  | scalar sc =>
                    simp at hb; subst hb
                    simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafOk
                    exact hleafOk.2
                  | _ => simp [TupleSpec.valOk] at hleafOk
    | index idxLocal =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨rfl, _⟩ := hok
            simp only [opBits] at hb
            match hs : locals[j]?, hb with
            | some (.init (.aggregate 0 elems)), hb =>
              simp only at hb
              have hslot := hslots j d _ hd hs
              have hns := scalarTypeOf_none_of_arrayTypeOf ha
              simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                ha] at hslot
              obtain ⟨_, he⟩ := hslot
              cases hidx : projIdx locals elems.length (.index idxLocal) with
              | none => simp [hidx] at hb
              | some idx =>
                simp only [hidx] at hb
                match hv : elems[idx]?, hb with
                | some (.scalar sc), hb =>
                  simp at hb; subst hb
                  exact (he _ (List.mem_of_getElem? hv)).2
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨rfl, _⟩ := hok
            simp only [opBits] at hb
            match hs : locals[j]?, hb with
            | some (.init (.aggregate 0 elems)), hb =>
              simp only at hb
              have hslot := hslots j d _ hd hs
              have hns := scalarTypeOf_none_of_arrayTypeOf ha
              simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                ha] at hslot
              obtain ⟨_, he⟩ := hslot
              cases hidx : projIdx locals elems.length (.constantIndex offset minLen fromEnd) with
              | none => simp [hidx] at hb
              | some idx =>
                simp only [hidx] at hb
                match hv : elems[idx]?, hb with
                | some (.scalar sc), hb =>
                  simp at hb; subst hb
                  exact (he _ (List.mem_of_getElem? hv)).2
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | deref =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, projOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        split at hok <;> simp at hok
      | cons _ _ => simp [operandOk, placeOk] at hok
    | _ => cases rest <;> simp [operandOk, placeOk, projOk, translateOperand, translatePlace] at hok
  | .constant c, hok, hb =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact opBits_valid decls locals hslots hT (.constant c)
      ⟨operandType_of_operandIntType hok.1, hok.2⟩ bits hb

theorem wrap_neg_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    MirSemantics.wrapScalarBits (m - MirSemantics.wrapScalarBits x m) m =
      ((- (x : Int)) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have hlt : 2 ^ (8 * sz) - x < 2 ^ (8 * sz) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : (- (x : Int)) % 2 ^ (8 * sz) = (- (x : Int)) + 2 ^ (8 * sz) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]
    omega

theorem wrap_not_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    (m - 1) - MirSemantics.wrapScalarBits x m =
      ((- (x : Int) - 1) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  have : (- (x : Int) - 1) % 2 ^ (8 * sz) = (- (x : Int) - 1) + 2 ^ (8 * sz) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

theorem operandTy_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk layouts decls srcIt op = true) :
    ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ intTypeOf ty = some srcIt := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hty⟩, _⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp [hd] at hty
    exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
      MirSemantics.resolveProjectedTy], hty⟩
  | .copy ⟨j, proj :: rest⟩, hok =>
    cases proj with
    | field idx fieldTy =>
      simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hok⟩, _⟩ := hok
      cases hd : decls[j]? with
      | none => simp [hd] at hok
      | some d =>
        simp only [hd] at hok
        cases hij : intBoolTupleOf d.ty with
        | some tupIt =>
          simp only [hij] at hok
          cases idx with
          | zero =>
            cases rest with
            | nil =>
              cases hf : intTypeOf fieldTy with
              | none => simp [hf] at hok
              | some fIt =>
                simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                exact ⟨fieldTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
                  MirSemantics.resolveProjectedTy], hf⟩
            | cons _ _ => simp at hok
          | succ _ => simp at hok
        | none =>
          simp only [hij] at hok
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hok
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            simp only [ht] at hok
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: rest) with
            | none => simp [hres] at hok
            | some rpair =>
              obtain ⟨_, leafSpec⟩ := rpair
              simp only [hres] at hok
              cases leafSpec with
              | tuple _ _ _ => simp at hok
              | scalar leafIt =>
                simp only [decide_eq_true_eq] at hok
                subst hok
                obtain ⟨leafTy, _, hsemProjTy, hleafSpec⟩ :=
                  resolveFieldPath_ty (specOfRigidTy_of_tupleTypeOf ht) hres
                exact ⟨leafTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
                  hsemProjTy], intTypeOf_of_specOfRigidTy_scalar hleafSpec⟩
    | index idxLocal =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨rfl, _⟩ := hok
            obtain ⟨elemTy, helem, hit⟩ := elemTyOf_of_arrayTypeOf ha
            exact ⟨elemTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
              MirSemantics.resolveProjectedTy, helem], hit⟩
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨rfl, _⟩ := hok
            obtain ⟨elemTy, helem, hit⟩ := elemTyOf_of_arrayTypeOf ha
            exact ⟨elemTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
              MirSemantics.resolveProjectedTy, helem], hit⟩
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at hok
    | deref =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, projOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨_, hok⟩, _⟩ := hok
        split at hok <;> simp at hok
      | cons _ _ => simp [operandOk, placeOk] at hok
    | _ => cases rest <;> simp [operandOk, placeOk, projOk, translateOperand, translatePlace] at hok
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, _⟩ := hok
    simp only [operandIntType] at hty
    exact ⟨c.ty, rfl, hty⟩

theorem intTypeOf_kind {ty : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf ty = some it) :
    ((∃ u, ty.kind = .uint u) ∧ it.signed = .Unsigned) ∨
    ((∃ i, ty.kind = .int i) ∧ it.signed = .Signed) := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all

theorem evalUnaryNot_frag (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0) (op : Operand)
    (hok : operandOk layouts decls it op = true)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    MirSemantics.evalUnaryNot ⟨x, it.size.bytes⟩ (MirSemantics.operandTy decls layouts op) locals mem =
      .ok (.scalar ⟨((- (x : Int) - 1) % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts it op hok
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    cases h : Nat.beq it.size.bytes 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hsz
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, _⟩ | ⟨⟨i, hi⟩, _⟩
  · simp [MirSemantics.evalUnaryNot, hty, hu, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]
  · simp [MirSemantics.evalUnaryNot, hty, hi, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]

theorem intCastTargetBytes_of_intTypeOf {ty : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf ty = some it) :
    MirSemantics.intCastTargetBytes ty.kind = some it.size.bytes := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all [MirSemantics.intCastTargetBytes]

theorem operandIsSigned_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk layouts decls srcIt op = true) :
    MirSemantics.operandIsSigned decls op layouts =
      match srcIt.signed with | .Unsigned => false | .Signed => true := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts srcIt op hok
  simp only [MirSemantics.operandIsSigned, hty, MirSemantics.tyIsSigned]
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, hs⟩ | ⟨⟨i, hi⟩, hs⟩
  · simp [hu, hs]
  · simp [hi, hs]

/-- The signedness Anneal uses for a fragment operand of type `T`. -/
def signedOf : Gen.Type → Bool
  | .Int it => match it.signed with | .Unsigned => false | .Signed => true
  | _ => false

theorem operandTy_of_OperandOkT (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {T : Gen.Type} (op : Operand) (hok : OperandOkT layouts decls T op) :
    ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ scalarTypeOf ty = some T := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp only [operandType, hd, Option.bind_eq_bind, Option.bind_some] at hty
    exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
      MirSemantics.resolveProjectedTy], hty⟩
  | .copy ⟨j, [.field 0 fTy]⟩, hok =>
    obtain ⟨_, ⟨d, hd, htSome⟩, hty⟩ := hok
    simp only [operandType, placeIntType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      cases hf : intTypeOf fTy with
      | none => simp [ht, hf] at hty
      | some fIt =>
        simp only [ht, hf, Option.bind_some] at hty
        by_cases heq : fIt = it'
        · subst heq
          simp at hty
          subst hty
          exact ⟨fTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
            MirSemantics.resolveProjectedTy], scalarTypeOf_int hf⟩
        · simp [heq] at hty
  | .copy ⟨j, [.field 1 fTy]⟩, hok =>
    obtain ⟨_, ⟨d, hd, htSome⟩, hty⟩ := hok
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      simp only [ht] at hty
      by_cases hb : isBoolTy fTy = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hty
        subst hty
        exact ⟨fTy, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
          MirSemantics.resolveProjectedTy], scalarTypeOf_bool hb⟩
      · simp [hb] at hty
  | .constant c, hok => exact ⟨c.ty, rfl, hok.1⟩

theorem operandIsSigned_of_OperandOkT (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {T : Gen.Type} (op : Operand) (hok : OperandOkT layouts decls T op) :
    MirSemantics.operandIsSigned decls op layouts = signedOf T := by
  obtain ⟨ty, hty, hT⟩ := operandTy_of_OperandOkT decls layouts op hok
  simp only [MirSemantics.operandIsSigned, hty, MirSemantics.tyIsSigned]
  rcases scalarTypeOf_cases hT with ⟨hb, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨ho, rfl⟩ | ⟨_, ht, rfl⟩
  · unfold isBoolTy at hb
    split at hb <;> simp_all [signedOf]
  · rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, hs⟩ | ⟨⟨i, hi⟩, hs⟩
    · simp [hu, hs, signedOf]
    · simp [hi, hs, signedOf]
  · unfold isOrderingTy at ho
    split at ho <;> simp_all [signedOf, orderingTy]
  · unfold intBoolTupleOf at ht
    revert ht
    cases ty.kind <;> simp [signedOf, intBoolTupleTy]

theorem castBits_eq_toNat (srcIt it : Gen.IntType) (hsrcGood : GoodSize srcIt.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * srcIt.size.bytes)) :
    let m := MirSemantics.scalarModulus it.size.bytes
    (match srcIt.signed with
      | .Unsigned => MirSemantics.wrapScalarBits x m
      | .Signed =>
        match Nat.ble it.size.bytes srcIt.size.bytes with
        | true => MirSemantics.wrapScalarBits x m
        | false => MirSemantics.signExtendBits x srcIt.size.bytes it.size.bytes) =
      (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat := by
  dsimp only
  rcases srcIt with ⟨s, ⟨srcBytes⟩⟩
  rcases it with ⟨_, ⟨dstBytes⟩⟩
  dsimp only at hsrcGood hx ⊢
  have hsrcPos : 0 < srcBytes := hsrcGood.pos
  cases s with
  | Unsigned =>
    rw [wrap_eq_toNat]
    rfl
  | Signed =>
    simp only [intFromBits]
    cases hble : Nat.ble dstBytes srcBytes with
    | true =>
      dsimp only
      have hle : dstBytes ≤ srcBytes := Nat.ble_eq.mp hble
      rw [wrap_eq_toNat]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · simp [hneg]
      · simp only [hneg, ↓reduceIte]
        congr 1
        have hdvd : ((2 : Int) ^ (8 * dstBytes)) ∣ (2 : Int) ^ (8 * srcBytes) := by
          have hdvdNat : (2 : Nat) ^ (8 * dstBytes) ∣ 2 ^ (8 * srcBytes) :=
            Nat.pow_dvd_pow 2 (by omega)
          exact_mod_cast hdvdNat
        rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
          Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    | false =>
      dsimp only
      have hlt : srcBytes < dstBytes :=
        Nat.lt_of_not_ge (fun hle => by rw [Nat.ble_eq.mpr hle] at hble; cases hble)
      have hsrcBeq : Nat.beq srcBytes 0 = false := by
        cases h : Nat.beq srcBytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
      have hpowLe : 2 ^ (8 * srcBytes) ≤ 2 ^ (8 * dstBytes) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hdstPos : 0 < 2 ^ (8 * dstBytes) := Nat.two_pow_pos _
      have hpSrc : ((2 : Nat) ^ (8 * srcBytes) : Int) = 2 ^ (8 * srcBytes) := by push_cast; rfl
      have hpDst : ((2 : Nat) ^ (8 * dstBytes) : Int) = 2 ^ (8 * dstBytes) := by push_cast; rfl
      have hhalf : Nat.div (2 ^ (8 * srcBytes)) 2 = 2 ^ (8 * srcBytes - 1) :=
        two_pow_div_two (8 * srcBytes) (by omega)
      simp only [MirSemantics.signExtendBits, hble, MirSemantics.isSignedNegative, hsrcBeq,
        scalarModulus_eq, wrapScalarBits_eq, Nat.mod_eq_of_lt hx, hhalf,
        Nat.add_eq, Nat.sub_eq]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = false := by
          cases h : Nat.ble (2 ^ (8 * srcBytes - 1)) x
          · rfl
          · exact absurd (Nat.ble_eq.mp h) (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have hxDst : (x : Int) < 2 ^ (8 * dstBytes) := by omega
        rw [Int.emod_eq_of_lt (by omega) hxDst, Int.toNat_natCast]
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = true :=
          Nat.ble_eq.mpr (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have : ((x : Int) - 2 ^ (8 * srcBytes)) % 2 ^ (8 * dstBytes) =
            ((x : Int) - 2 ^ (8 * srcBytes)) + 2 ^ (8 * dstBytes) := by
          rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [this]
        omega

/-- Every non-scalar, non-pointer local referenced by `ops` is initialized in `locals`. -/
def OpsNonScalarInit (decls : List LocalDecl) (locals : List LocalSlot)
    (ops : List Operand) : Prop :=
  ∀ op ∈ ops, ∀ j ∈ opLocals op, ∀ d slot,
    decls[j]? = some d → locals[j]? = some slot → scalarTypeOf d.ty = none →
    isPtrTy d.ty = false → ∃ v, slot = .init v

theorem evalRvalue_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOk layouts decls it rv = true)
    (hns : OpsNonScalarInit decls locals (rvOperands rv))
    (mem : MirSemantics.Memory) :
    (∀ r, rvBits decls locals it layouts rv = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, it.size.bytes⟩) locals mem) ∧
    (rvBits decls locals it layouts rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOk] at hok
    obtain ⟨hsome, hnone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  | .unaryOp uop op, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, hiuop⟩ := Option.isSome_iff_exists.mp huop
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals mem.callerLocals
    have hbeq : Nat.beq it.size.bytes 0 = false := by
      cases h : Nat.beq it.size.bytes 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hsz
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiuop, hxo] at hr, fun _ => ?_⟩
      cases uop <;> simp [translateUnOp] at hiuop <;> simp [evalRvalue, hanone hxo]
    | some x =>
      refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiuop, hxo] at h⟩
      simp [rvBits, hiuop, hxo] at hr
      subst hr
      have hx := opBits_lt decls locals hslots it op hok x hxo
      cases uop <;> simp [translateUnOp] at hiuop <;> subst hiuop
      · simp only [evalRvalue, ha x hxo, evalUnaryNot_frag decls layouts it hsz op hok x hx, intUnArith]
      · simp [evalRvalue, ha x hxo, hbeq, Nat.sub_eq, wrap_neg_eq_toNat x _ hx, intUnArith]
  | .binaryOp op a b, hok =>
    obtain ⟨iop, rhsIt, hiop, hoka, hrhsTy, hokb, hhom⟩ := rvalueOk_binaryOp hok
    obtain ⟨_, _, hrhsTyOf⟩ := operandTy_of_operandOk decls layouts rhsIt b hokb
    have hrhsGood : GoodSize rhsIt.size.bytes := intTypeOf_good hrhsTyOf
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_frag decls locals hslots hn rhsIt b hokb mem.borrows mem.globals mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_lt decls locals hslots it a hoka x hxa
        have hy := opBits_lt decls locals hslots rhsIt b hokb y hyb
        have hsigned := operandIsSigned_of_operandOk decls layouts it a hoka
        obtain ⟨hbinOk, hbinNone⟩ :=
          evalScalarBinOp_frag op iop hiop it rhsIt hgood hrhsGood hhom x y hx hy locals mem
        cases hz : intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr, fun _ => ?_⟩
          simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hbinNone hz]
        | some z =>
          refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at h⟩
          simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr
          subst hr
          simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hbinOk z hz]
  | .cast .intToInt op targetTy, hok =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType layouts decls op with
    | none =>
      simp only [hsrcIt] at hsrc
      have hokT := operandOkB_T hsrc
      obtain ⟨ha, hanone⟩ :=
        evalOperand_fragT decls locals hslots hn .bool op hokT mem.borrows mem.globals mem.callerLocals
      have htgtBytes := intCastTargetBytes_of_intTypeOf htgt
      have hsigned : MirSemantics.operandIsSigned decls op layouts = false :=
        operandIsSigned_of_OperandOkT decls layouts op hokT
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxo]
      | some x =>
        refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hsrcIt, hxo] at h⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hx2 : x < 2 := by simpa [ValidBits] using opBits_valid decls locals hslots .bool op hokT x hxo
        have hx : x < 2 ^ (8 * u8Ty.size.bytes) := by simp [u8Ty]; omega
        have hcast := castBits_eq_toNat u8Ty it (Or.inl rfl) x hx
        dsimp only [u8Ty] at hcast
        have hbeq1 : Nat.beq u8Ty.size.bytes 0 = false := rfl
        simp only [evalRvalue, ha x hxo, hbeq1, htgtBytes, hsigned]
        rw [hcast]
        rfl
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      obtain ⟨ha, hanone⟩ :=
        evalOperand_frag decls locals hslots hn srcIt op hsrc mem.borrows mem.globals mem.callerLocals
      obtain ⟨ty, _, hsrcTy⟩ := operandTy_of_operandOk decls layouts srcIt op hsrc
      have hsrcGood : GoodSize srcIt.size.bytes := intTypeOf_good hsrcTy
      have hsrcBeq : Nat.beq srcIt.size.bytes 0 = false := by
        cases h : Nat.beq srcIt.size.bytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.ne_of_gt hsrcGood.pos)
      have htgtBytes := intCastTargetBytes_of_intTypeOf htgt
      have hsigned := operandIsSigned_of_operandOk decls layouts srcIt op hsrc
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxo]
      | some x =>
        refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hsrcIt, hxo] at h⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hx := opBits_lt decls locals hslots srcIt op hsrc x hxo
        have hcast := castBits_eq_toNat srcIt it hsrcGood x hx
        dsimp only at hcast
        simp only [evalRvalue, ha x hxo, hsrcBeq, htgtBytes, hsigned]
        cases hs : srcIt.signed <;> simp only [hs] at hcast ⊢
        · rw [hcast]
        · cases hble : Nat.ble it.size.bytes srcIt.size.bytes <;> simp only [hble] at hcast ⊢ <;> rw [hcast]
  | .len ⟨j, []⟩, hok =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, hj⟩, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    cases hd : decls[j]? with
    | none => simp [hd] at hty
    | some d =>
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at hty
      cases ha : arrayTypeOf d.ty with
      | none => simp [ha] at hty
      | some p =>
        obtain ⟨elemIt, count⟩ := p
        have hs : locals[j]? = some locals[j] := by simp [hjl]
        have hscNone := scalarTypeOf_none_of_arrayTypeOf ha
        obtain ⟨v, hv⟩ := hns (.copy ⟨j, []⟩) (by simp [rvOperands]) j
          (by simp [opLocals, placeLocals]) d locals[j] hd hs hscNone
          (isPtrTy_false_of_arrayTypeOf ha)
        have hslot := hslots j d (.init v) hd (hv ▸ hs)
        simp only [DeclSlotOk, hscNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          ha] at hslot
        rw [hv] at hs
        match v, hslot with
        | .aggregate 0 elems, ⟨hlen, _⟩ =>
          refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hd, ha] at hnone⟩
          simp [rvBits, hd, ha] at hr
          subst hr
          simp [evalRvalue, evalOperand, get?, hs, readProjectedValue, length, hlen, usizeIt]

theorem evalOperands_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (elemIt : Gen.IntType) (ops : List Operand)
    (hok : ops.all (operandOk layouts decls elemIt) = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ elems, (ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = some elems →
      evalOperands locals ops borrows globals layouts callerLocals =
        .ok elems locals) ∧
    ((ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = none →
      evalOperands locals ops borrows globals layouts callerLocals = .ub) := by
  induction ops with
  | nil =>
    refine ⟨fun elems h => ?_, fun h => by simp at h⟩
    simp at h
    subst h
    simp [evalOperands]
  | cons op rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hop, hrest⟩ := hok
    obtain ⟨hopOk, hopNone⟩ :=
      evalOperand_frag decls locals hslots hn elemIt op hop borrows globals callerLocals
    obtain ⟨hrestOk, hrestNone⟩ := ih hrest
    cases hb : opBits locals op with
    | none =>
      refine ⟨fun elems h => by simp [List.mapM_cons, hb] at h, fun _ => ?_⟩
      simp [evalOperands, hopNone hb]
    | some x =>
      cases hxs : rest.mapM (fun op => do
          let b ← opBits locals op
          pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
      | none =>
        refine ⟨fun elems h => by rw [List.mapM_cons, hb, hxs] at h; simp at h, fun _ => ?_⟩
        simp [evalOperands, hopOk x hb, hrestNone hxs]
      | some xs =>
        refine ⟨fun ys hys => ?_, fun h => by rw [List.mapM_cons, hb, hxs] at h; simp at h⟩
        rw [List.mapM_cons, hb, hxs] at hys
        simp at hys
        subst hys
        simp [evalOperands, hopOk x hb, hrestOk xs hxs]

theorem replicateValue_eq_replicate (count : Nat) (v : Value) :
    MirSemantics.replicateValue count v = List.replicate count v := by
  induction count with
  | zero => rfl
  | succ n ih => simp [MirSemantics.replicateValue, List.replicate_succ, ih]

theorem evalRvalue_array_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (elemIt : Gen.IntType) (count : Nat) (rv : Rvalue)
    (hok : arrayRvalueOk layouts decls elemIt count rv = true)
    (mem : MirSemantics.Memory) :
    (∀ elems, arrayRvElems locals elemIt rv = some elems →
      evalRvalue locals rv mem decls layouts =
        .ok (.aggregate 0 elems) locals mem) ∧
    (arrayRvElems locals elemIt rv = none →
      evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use (.copy ⟨j, []⟩), hok =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    cases hd : decls[j]? with
    | none => simp [hd] at hty
    | some d =>
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at hty
      have hs : locals[j]? = some locals[j] := by simp [hjl]
      have hslot := hslots j d _ hd hs
      have hns := scalarTypeOf_none_of_arrayTypeOf hty
      simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hty] at hslot
      generalize locals[j] = slot at hs hslot
      match slot, hslot with
      | .dead, _ => simp [arrayRvElems, evalRvalue, evalOperand, get?, hs]
      | .uninit, _ => simp [arrayRvElems, evalRvalue, evalOperand, get?, hs]
      | .init (.aggregate 0 elems), ⟨_, _⟩ =>
        refine ⟨fun ys hys => ?_, fun hnone => by simp [arrayRvElems, hs] at hnone⟩
        simp [arrayRvElems, hs] at hys
        subst hys
        simp [evalRvalue, evalOperand, get?, hs, readProjectedValue]
  | .repeat op c, hok =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, _⟩, hop⟩ := hok
    obtain ⟨hopOk, hopNone⟩ :=
      evalOperand_frag decls locals hslots hn elemIt op hop mem.borrows mem.globals mem.callerLocals
    cases hb : opBits locals op with
    | none =>
      refine ⟨fun xs hxs => by simp [arrayRvElems, hb] at hxs, fun _ => ?_⟩
      simp [evalRvalue, hopNone hb]
    | some x =>
      refine ⟨fun xs hxs => ?_, fun hnone => by simp [arrayRvElems, hb] at hnone⟩
      simp [arrayRvElems, hb] at hxs
      subst hxs
      simp [evalRvalue, hopOk x hb, replicateValue_eq_replicate]
  | .aggregate (.array elemTy) ops, hok =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, _⟩, hops⟩ := hok
    obtain ⟨hopsOk, hopsNone⟩ :=
      evalOperands_frag decls locals hslots hn elemIt ops hops mem.borrows mem.globals mem.callerLocals
    cases hxs : ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
    | none =>
      refine ⟨fun xs h => by rw [arrayRvElems, hxs] at h; contradiction, fun _ => ?_⟩
      simp [evalRvalue, hopsNone hxs]
    | some xs =>
      refine ⟨fun ys hys => ?_, fun hnone => by rw [arrayRvElems, hxs] at hnone; contradiction⟩
      rw [arrayRvElems, hxs] at hys
      cases hys
      simp [evalRvalue, hopsOk xs hxs]

theorem tuplePlaceSpec_nonDeref {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {p : Place} {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tuplePlaceSpec layouts decls p = some (fields, size, align)) :
    ∀ rest, p.projection ≠ .deref :: rest := by
  intro rest hproj
  rcases p with ⟨j, projs⟩
  dsimp only at hproj
  subst hproj
  simp [tuplePlaceSpec] at h

theorem evalOperand_spec_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    (hn : locals.length = decls.length)
    (spec : TupleSpec) (op : Operand) (hok : specOperandOk layouts decls spec op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ v, specOpVal locals spec op = some v →
      evalOperand locals op borrows globals layouts callerLocals = .ok v locals) ∧
    (specOpVal locals spec op = none →
      evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  cases spec with
  | scalar it =>
    simp only [specOperandOk] at hok
    obtain ⟨haok, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok borrows globals callerLocals
    cases hb : opBits locals op with
    | none =>
      refine ⟨fun v hv => by simp [specOpVal, hb] at hv, fun _ => hanone hb⟩
    | some b =>
      refine ⟨fun v hv => ?_, fun hnone => by simp [specOpVal, hb] at hnone⟩
      simp [specOpVal, hb] at hv
      subst hv
      exact haok b hb
  | tuple fields size align =>
    cases op with
    | move _ | constant _ => simp [specOperandOk] at hok
    | copy p =>
      simp only [specOperandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨htp, _⟩ := hok
      have hnd := tuplePlaceSpec_nonDeref htp
      obtain ⟨d, rootFields, rootSize, rootAlign, relOff, hj, hd, ht, hres, _⟩ :=
        tuplePlaceSpec_resolve htp
      have hjl : p.local_ < locals.length := by rw [hn]; exact hj
      have hs : locals[p.local_]? = some locals[p.local_] := by simp [hjl]
      have hslot := hslots p.local_ d _ hd hs
      have hns := scalarTypeOf_none_of_tupleTypeOf ht
      have harr := arrayTypeOf_none_of_tupleTypeOf ht
      simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        harr, ht] at hslot
      generalize locals[p.local_] = slot at hs hslot
      match slot, hslot with
      | .dead, _ =>
        rw [evalOperand_copy_nonDeref locals p hnd borrows globals layouts callerLocals]
        cases p; simp [specOpVal, get?, hs]
      | .uninit, _ =>
        rw [evalOperand_copy_nonDeref locals p hnd borrows globals layouts callerLocals]
        cases p; simp [specOpVal, get?, hs]
      | .init rootVal, ⟨hwf, hval⟩ =>
        obtain ⟨leafVal, hread, _, _, hprojRead⟩ := resolveFieldPath_read hwf hval hres
        rw [evalOperand_copy_nonDeref locals p hnd borrows globals layouts callerLocals]
        refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · cases p; simp [specOpVal, hs, hread] at hv
          subst hv
          simp [get?, hs, hprojRead locals]
        · cases p; simp [specOpVal, hs, hread] at hnone

theorem evalOperands_tuple_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    (hn : locals.length = decls.length)
    (fields : List (Nat × TupleSpec)) (ops : List Operand)
    (hok : tupleFieldsOperandOk layouts decls fields ops = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ vals, tupleFieldsOpsVal locals fields ops = some vals →
      evalOperands locals ops borrows globals layouts callerLocals = .ok vals locals) ∧
    (tupleFieldsOpsVal locals fields ops = none →
      evalOperands locals ops borrows globals layouts callerLocals = .ub) := by
  induction fields generalizing ops with
  | nil =>
    cases ops <;> simp [tupleFieldsOperandOk] at hok
    refine ⟨fun vals h => ?_, fun h => by simp [tupleFieldsOpsVal] at h⟩
    simp [tupleFieldsOpsVal] at h
    subst h
    simp [evalOperands]
  | cons f restF ih =>
    obtain ⟨off, fSpec⟩ := f
    cases ops with
    | nil => simp [tupleFieldsOperandOk] at hok
    | cons op restOps =>
      simp only [tupleFieldsOperandOk, Bool.and_eq_true] at hok
      obtain ⟨hop, hrest⟩ := hok
      obtain ⟨hopOk, hopNone⟩ :=
        evalOperand_spec_frag decls locals hslots hn fSpec op hop borrows globals callerLocals
      obtain ⟨hrestOk, hrestNone⟩ := ih restOps hrest
      cases hv1 : specOpVal locals fSpec op with
      | none =>
        refine ⟨fun vals h => by simp [tupleFieldsOpsVal, hv1] at h, fun _ => ?_⟩
        simp [evalOperands, hopNone hv1]
      | some v1 =>
        cases hvs : tupleFieldsOpsVal locals restF restOps with
        | none =>
          refine ⟨fun vals h => by simp [tupleFieldsOpsVal, hv1, hvs] at h, fun _ => ?_⟩
          simp [evalOperands, hopOk v1 hv1, hrestNone hvs]
        | some vs =>
          refine ⟨fun ys hys => ?_, fun h => by simp [tupleFieldsOpsVal, hv1, hvs] at h⟩
          simp [tupleFieldsOpsVal, hv1, hvs] at hys
          subst hys
          simp [evalOperands, hopOk v1 hv1, hrestOk vs hvs]

theorem evalRvalue_tuple_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    (hn : locals.length = decls.length)
    (dstTy : MirAst.Ty) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (rv : Rvalue) (hok : tupleRvalueOk layouts decls dstTy fields size align rv = true)
    (mem : MirSemantics.Memory) :
    (∀ newVal, tupleRvVal locals fields rv = some newVal →
      evalRvalue locals rv mem decls layouts = .ok newVal locals mem) ∧
    (tupleRvVal locals fields rv = none →
      evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use (.copy p), hok =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hnd := tuplePlaceSpec_nonDeref hok.1
    obtain ⟨d, rootFields, rootSize, rootAlign, relOff, hj, hd, ht, hres, _⟩ :=
      tuplePlaceSpec_resolve hok.1
    have hjl : p.local_ < locals.length := by rw [hn]; exact hj
    have hs : locals[p.local_]? = some locals[p.local_] := by simp [hjl]
    have hslot := hslots p.local_ d _ hd hs
    have hns := scalarTypeOf_none_of_tupleTypeOf ht
    have harr := arrayTypeOf_none_of_tupleTypeOf ht
    simp only [DeclSlotOk, hns, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      harr, ht] at hslot
    generalize locals[p.local_] = slot at hs hslot
    match slot, hslot with
    | .dead, _ =>
      cases p; simp [tupleRvVal, evalRvalue, evalOperand_copy_nonDeref locals _ hnd, get?, hs]
    | .uninit, _ =>
      cases p; simp [tupleRvVal, evalRvalue, evalOperand_copy_nonDeref locals _ hnd, get?, hs]
    | .init rootVal, ⟨hwf, hval⟩ =>
      obtain ⟨leafVal, hread, _, _, hprojRead⟩ := resolveFieldPath_read hwf hval hres
      refine ⟨fun newVal hnv => ?_, fun hnone => ?_⟩
      · cases p; simp [tupleRvVal, hs, hread] at hnv
        subst hnv
        simp [evalRvalue, evalOperand_copy_nonDeref locals _ hnd, get?, hs, hprojRead locals]
      · cases p; simp [tupleRvVal, hs, hread] at hnone
  | .aggregate .tuple ops, hok =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hopsOk, hopsNone⟩ :=
      evalOperands_tuple_frag decls locals hslots hn fields ops hok.2
        mem.borrows mem.globals mem.callerLocals
    cases hvs : tupleFieldsOpsVal locals fields ops with
    | none =>
      refine ⟨fun newVal h => by simp [tupleRvVal, hvs] at h, fun _ => ?_⟩
      simp [evalRvalue, hopsNone hvs]
    | some vs =>
      refine ⟨fun newVal h => ?_, fun hnone => by simp [tupleRvVal, hvs] at hnone⟩
      simp [tupleRvVal, hvs] at h
      subst h
      simp [evalRvalue, hopsOk vs hvs]
  | .aggregate (.adt defId 0 none) ops, hok =>
    simp only [tupleRvalueOk, Bool.and_eq_true] at hok
    obtain ⟨_, hokOps⟩ := hok
    obtain ⟨hopsOk, hopsNone⟩ :=
      evalOperands_tuple_frag decls locals hslots hn fields ops hokOps
        mem.borrows mem.globals mem.callerLocals
    cases hvs : tupleFieldsOpsVal locals fields ops with
    | none =>
      refine ⟨fun newVal h => by simp [tupleRvVal, hvs] at h, fun _ => ?_⟩
      simp [evalRvalue, hopsNone hvs]
    | some vs =>
      refine ⟨fun newVal h => ?_, fun hnone => by simp [tupleRvVal, hvs] at hnone⟩
      simp [tupleRvVal, hvs] at h
      subst h
      simp [evalRvalue, hopsOk vs hvs]

/-! ## Comparisons, `!` on `bool`, and `bool` rvalues -/

theorem signedLt_eq (x y sz : Nat) (hsz : sz ≠ 0) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedLt x y sz =
      decide (intFromBits x ⟨.Signed, ⟨sz⟩⟩ < intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedLt, scalarModulus_eq, wrapScalarBits_eq, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_ble_eq_decide, intFromBits]
  rw [hp]
  generalize 2 ^ (8 * sz - 1) = H at hM hH ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;>
    simp [hxH, hyH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;> omega

theorem signedLe_eq (x y sz : Nat) (hsz : sz ≠ 0) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedLe x y sz =
      decide (intFromBits x ⟨.Signed, ⟨sz⟩⟩ ≤ intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  simp only [MirSemantics.signedLe, signedLt_eq y x sz hsz hy hx]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem relBool_intCmp_lt (a b : Int) : relBool .Lt (intCmp a b) = decide (a < b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool]
theorem relBool_intCmp_gt (a b : Int) : relBool .Gt (intCmp a b) = decide (b < a) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_le (a b : Int) : relBool .Le (intCmp a b) = decide (a ≤ b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_ge (a b : Int) : relBool .Ge (intCmp a b) = decide (b ≤ a) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_eq (a b : Int) : relBool .Eq (intCmp a b) = decide (a = b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_ne (a b : Int) : relBool .Ne (intCmp a b) = decide (a ≠ b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega

theorem intFromBits_unsigned (sz x : Nat) : intFromBits x ⟨.Unsigned, ⟨sz⟩⟩ = (x : Int) := rfl

theorem decide_intFromBits_eq (it : Gen.IntType) (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes))
    (hy : y < 2 ^ (8 * it.size.bytes)) :
    decide (intFromBits x it = intFromBits y it) = Nat.beq x y := by
  rw [nat_beq_eq_decide]
  exact decide_eq_decide.mpr (intFromBits_inj it x y hx hy)

/-- Anneal's comparison of two integers of one fragment type agrees with
MiniRust's `BinOp::Rel` on the decoded values (`cmpOf`), for both signed and
unsigned types. -/
theorem evalScalarBinOp_rel_int (op : MirAst.BinOp) (rel : Gen.RelOp)
    (hrel : translateRelOp op = some rel) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
      .ok (.scalar (boolToScalar (relBool rel (cmpOf (.Int it) x y)))) locals mem := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have heq := decide_intFromBits_eq it x y hx hy
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hsz hbeq hx hy heq ⊢
  cases op <;> simp [translateRelOp] at hrel <;> subst hrel <;>
    cases signed <;>
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, cmpOf, relBool_intCmp_lt, relBool_intCmp_gt,
      relBool_intCmp_le, relBool_intCmp_ge, relBool_intCmp_eq, relBool_intCmp_ne, heq,
      intFromBits_unsigned, signedLt_eq _ _ sz hsz hx hy, signedLt_eq _ _ sz hsz hy hx,
      signedLe_eq _ _ sz hsz hx hy, signedLe_eq _ _ sz hsz hy hx, nat_ble_eq_decide,
      nat_beq_eq_decide, decide_not] <;>
    (congr 3; apply Bool.eq_iff_iff.mpr; simp only [Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]; omega)

/-- Anneal's comparison of two `bool`s (one byte each, `0` or `1`, compared
unsigned) agrees with MiniRust's `false < true`. -/
theorem evalScalarBinOp_rel_bool (op : MirAst.BinOp) (rel : Gen.RelOp)
    (hrel : translateRelOp op = some rel) (x y : Nat) (hx : x < 2) (hy : y < 2)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp op ⟨x, u8Ty.size.bytes⟩ ⟨y, u8Ty.size.bytes⟩ locals mem false =
      .ok (.scalar (boolToScalar (relBool rel (cmpOf .Bool x y)))) locals mem := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;>
    cases op <;> simp [translateRelOp] at hrel <;> subst hrel <;> rfl

/-- Anneal's `!` on a `bool` operand (`0` or `1`) is `1 - x`. -/
theorem evalUnaryNot_bool (decls : List LocalDecl) (layouts : Layout.LayoutTable) (op : Operand)
    (hok : OperandOkT layouts decls .Bool op) (x : Nat) (hx : x < 2) (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    MirSemantics.evalUnaryNot ⟨x, u8Ty.size.bytes⟩ (MirSemantics.operandTy decls layouts op) locals mem =
      .ok (.scalar ⟨1 - x, u8Ty.size.bytes⟩) locals mem := by
  obtain ⟨ty, hty, hT⟩ := operandTy_of_OperandOkT decls layouts op hok
  have hkind : ty.kind = .bool := by
    rcases scalarTypeOf_cases hT with ⟨hb, _⟩ | ⟨it, _, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩
    · unfold isBoolTy at hb; split at hb <;> simp_all
    · cases h
    · simp [orderingTy] at h
    · simp [intBoolTupleTy] at h
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    simp [MirSemantics.evalUnaryNot, hty, hkind, u8Ty]

/-- Anneal's bitwise `BitAnd`, `BitOr`, and `BitXor` on two `bool`s (`0` or
`1`) agrees with MiniRust's `build::bool_and`, `build::bool_or`, and
`build::bool_xor` (`boolBitEval`). -/
theorem evalScalarBinOp_boolBit (op : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : translateBoolBitOp op = some iop) (x y : Nat) (hx : x < 2) (hy : y < 2)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp op ⟨x, u8Ty.size.bytes⟩ ⟨y, u8Ty.size.bytes⟩ locals mem false =
      .ok (.scalar ⟨boolBitEval iop x y, u8Ty.size.bytes⟩) locals mem := by
  cases op <;> simp [translateBoolBitOp] at hop <;> subst hop <;>
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl

theorem evalRelOperand_frag {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    (hn : locals.length = decls.length) {T : Gen.Type} {it : Gen.IntType} (op : Operand)
    (hok : RelOperandOk layouts decls T it op)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none →
      evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  cases hok with
  | int it op hok =>
    exact evalOperand_frag decls locals hslots hn it op hok borrows globals callerLocals
  | bool op hok =>
    exact evalOperand_fragT decls locals hslots hn .bool op (operandOkB_T hok)
      borrows globals callerLocals

theorem opBits_valid_of_RelOperandOk {layouts : Layout.LayoutTable} (decls : List LocalDecl)
    (locals : List LocalSlot) (hslots : SlotsOk layouts decls locals)
    {T : Gen.Type} {it : Gen.IntType} (op : Operand)
    (hok : RelOperandOk layouts decls T it op) (bits : Nat)
    (hb : opBits locals op = some bits) :
    ValidBits T bits := by
  cases hok with
  | int it op hok =>
    simpa [ValidBits] using opBits_lt decls locals hslots it op hok bits hb
  | bool op hok =>
    exact opBits_valid decls locals hslots .bool op (operandOkB_T hok) bits hb

theorem operandIsSigned_of_RelOperandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {T : Gen.Type} {it : Gen.IntType} (op : Operand)
    (hok : RelOperandOk layouts decls T it op) :
    MirSemantics.operandIsSigned decls op layouts = signedOf T := by
  cases hok with
  | int it op hok =>
    simpa [signedOf] using operandIsSigned_of_operandOk decls layouts it op hok
  | bool op hok =>
    exact operandIsSigned_of_OperandOkT decls layouts op (operandOkB_T hok)

/-- Evaluating a fragment rvalue of type `bool` in Anneal's semantics. -/
theorem evalRvalue_fragB {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (rv : Rvalue) (hok : rvalueOkB layouts decls rv = true)
    (mem : MirSemantics.Memory) :
    (∀ r, rvBitsB decls locals rv layouts = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, u8Ty.size.bytes⟩) locals mem) ∧
    (rvBitsB decls locals rv layouts = none → evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOkB] at hok
    obtain ⟨hsome, hnone⟩ := evalOperand_fragT decls locals hslots hn .bool op (operandOkB_T hok)
      mem.borrows mem.globals mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  | .unaryOp .not op, hok =>
    simp only [rvalueOkB] at hok
    have hokT := operandOkB_T hok
    obtain ⟨hsome, hnone⟩ := evalOperand_fragT decls locals hslots hn .bool op hokT
      mem.borrows mem.globals mem.callerLocals
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hxo] at hr, fun _ => ?_⟩
      simp [evalRvalue, hnone hxo]
    | some x =>
      have hx : x < 2 := by simpa [ValidBits] using opBits_valid decls locals hslots .bool op hokT x hxo
      refine ⟨fun r hr => ?_, fun h => by simp [rvBitsB, hxo] at h⟩
      simp [rvBitsB, hxo] at hr
      subst hr
      simp only [evalRvalue, hsome x hxo, evalUnaryNot_bool decls layouts op hokT x hx]
  | .unaryOp .neg _, hok => simp [rvalueOkB] at hok
  | .unaryOp .ptrMetadata _, hok => simp [rvalueOkB] at hok
  | .binaryOp op a b, hok =>
    simp only [rvalueOkB] at hok
    cases hrel : translateRelOp op with
    | some rel =>
      simp only [hrel, Option.isSome_some, ↓reduceIte] at hok
      obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hok
      obtain ⟨ha, hanone⟩ := evalRelOperand_frag decls locals hslots hn a hokA
        mem.borrows mem.globals mem.callerLocals
      obtain ⟨hb, hbnone⟩ := evalRelOperand_frag decls locals hslots hn b hokB
        mem.borrows mem.globals mem.callerLocals
      have hsigned := operandIsSigned_of_RelOperandOk decls layouts a hokA
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxa]
      | some x =>
        cases hyb : opBits locals b with
        | none =>
          refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr, fun _ => ?_⟩
          simp [evalRvalue, ha x hxa, hbnone hyb]
        | some y =>
          have hx := opBits_valid_of_RelOperandOk decls locals hslots a hokA x hxa
          have hy := opBits_valid_of_RelOperandOk decls locals hslots b hokB y hyb
          refine ⟨fun r hr => ?_, fun h => by simp [rvBitsB, hrel, htyA, hxa, hyb] at h⟩
          simp [rvBitsB, hrel, htyA, hxa, hyb] at hr
          subst hr
          have hres : evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem (signedOf T) =
              .ok (.scalar (boolToScalar (relBool rel (cmpOf T x y)))) locals mem := by
            cases hT with
            | int it hgood => exact evalScalarBinOp_rel_int op rel hrel it hgood x y hx hy locals mem
            | bool =>
              exact evalScalarBinOp_rel_bool op rel hrel x y (by simpa [ValidBits] using hx)
                (by simpa [ValidBits] using hy) locals mem
          simp only [evalRvalue, ha x hxa, hb y hyb, hsigned, hres]
          cases relBool rel (cmpOf T x y) <;> rfl
    | none =>
      simp only [hrel, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
      obtain ⟨⟨hbitSome, hokA'⟩, hokB'⟩ := hok
      obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hbitSome
      have hokA := operandOkB_T hokA'
      have hokB := operandOkB_T hokB'
      obtain ⟨ha, hanone⟩ := evalOperand_fragT decls locals hslots hn .bool a hokA
        mem.borrows mem.globals mem.callerLocals
      obtain ⟨hb, hbnone⟩ := evalOperand_fragT decls locals hslots hn .bool b hokB
        mem.borrows mem.globals mem.callerLocals
      have hsigned : MirSemantics.operandIsSigned decls a layouts = false :=
        operandIsSigned_of_OperandOkT decls layouts a hokA
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxa]
      | some x =>
        cases hyb : opBits locals b with
        | none =>
          refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa, hyb] at hr, fun _ => ?_⟩
          simp [evalRvalue, ha x hxa, hbnone hyb]
        | some y =>
          have hx : x < 2 := by simpa [ValidBits] using opBits_valid decls locals hslots .bool a hokA x hxa
          have hy : y < 2 := by simpa [ValidBits] using opBits_valid decls locals hslots .bool b hokB y hyb
          refine ⟨fun r hr => ?_, fun h => by simp [rvBitsB, hrel, hiop, hxa, hyb] at h⟩
          simp [rvBitsB, hrel, hiop, hxa, hyb] at hr
          subst hr
          simp only [evalRvalue, ha x hxa, hb y hyb, hsigned,
            evalScalarBinOp_boolBit op iop hiop x y hx hy locals mem]
  | .cast _ _ _, hok => simp [rvalueOkB] at hok
  | .copyForDeref _, hok => simp [rvalueOkB] at hok
  | .repeat _ _, hok => simp [rvalueOkB] at hok
  | .ref _ _, hok => simp [rvalueOkB] at hok
  | .rawPtr _ _, hok => simp [rvalueOkB] at hok
  | .len _, hok => simp [rvalueOkB] at hok
  | .discriminant _, hok => simp [rvalueOkB] at hok
  | .aggregate _ _, hok => simp [rvalueOkB] at hok
  | .threadLocalRef _, hok => simp [rvalueOkB] at hok
  | .nullaryOp _ _, hok => simp [rvalueOkB] at hok
  | .shallowInitBox _ _, hok => simp [rvalueOkB] at hok
  | .wrapUnsafeBinder _ _, hok => simp [rvalueOkB] at hok

/-! ## Three-way comparisons (`Ordering` rvalues) -/

/-- Anneal's three-way comparison of two integers of one fragment type yields
the tag (`ordBits`) of the `Ordering` variant that MiniRust's `RelOp::Cmp`
followed by `minimize`'s transmute produces from the decoded values (`cmpOf`),
for both signed and unsigned types. -/
theorem evalScalarBinOp_cmp_int (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp .cmp ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
      .ok (.scalar ⟨ordBits (cmpOf (.Int it) x y), u8Ty.size.bytes⟩) locals mem := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have heq := decide_intFromBits_eq it x y hx hy
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hsz hbeq hx hy heq ⊢
  cases signed with
  | Unsigned =>
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, cmpOf, intFromBits_unsigned, intCmp,
      nat_beq_eq_decide, nat_ble_eq_decide]
    by_cases h1 : x < y
    · have h2 : x ≠ y := by omega
      have h3 : x ≤ y := by omega
      simp [h1, h2, h3, ordBits, u8Ty]
    · by_cases h2 : x = y
      · subst h2; simp [ordBits, u8Ty]
      · have h3 : ¬ x ≤ y := by omega
        have h4 : ¬ (x : Int) < y := by omega
        have h5 : ¬ (x : Int) = y := by omega
        simp [h2, h3, h4, h5, ordBits, u8Ty]
  | Signed =>
    obtain ⟨hM, _⟩ := two_pow_byte_split sz hsz
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, cmpOf, intCmp, scalarModulus_eq,
      wrapScalarBits_eq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, signedLt_eq x y sz hsz hx hy]
    rw [← heq]
    generalize intFromBits x ⟨.Signed, ⟨sz⟩⟩ = a
    generalize intFromBits y ⟨.Signed, ⟨sz⟩⟩ = b
    by_cases h1 : a < b
    · have h2 : a ≠ b := by omega
      simp [h1, h2, ordBits, u8Ty]
    · by_cases h2 : a = b
      · subst h2; simp [ordBits, u8Ty]
      · simp [h1, h2, ordBits, u8Ty]

/-- Anneal's three-way comparison of two `bool`s (one byte each, `0` or `1`,
compared unsigned) agrees with MiniRust's `false < true`. -/
theorem evalScalarBinOp_cmp_bool (x y : Nat) (hx : x < 2) (hy : y < 2)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp .cmp ⟨x, u8Ty.size.bytes⟩ ⟨y, u8Ty.size.bytes⟩ locals mem false =
      .ok (.scalar ⟨ordBits (cmpOf .Bool x y), u8Ty.size.bytes⟩) locals mem := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl

/-- Evaluating a fragment rvalue of type `Ordering` in Anneal's semantics. -/
theorem evalRvalue_fragO {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (rv : Rvalue) (hok : rvalueOkO layouts decls rv = true)
    (mem : MirSemantics.Memory) :
    (∀ r, rvBitsO decls locals rv layouts = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, u8Ty.size.bytes⟩) locals mem) ∧
    (rvBitsO decls locals rv layouts = none → evalRvalue locals rv mem decls layouts = .ub) := by
  rcases rvalueOkO_spec hok with ⟨op, rfl, hokOp⟩ | ⟨a, b, rfl, hops⟩
  · obtain ⟨hsome, hnone⟩ := evalOperand_fragT decls locals hslots hn .ordering op
      (operandOkO_T hokOp) mem.borrows mem.globals mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  · obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hops
    obtain ⟨ha, hanone⟩ := evalRelOperand_frag decls locals hslots hn a hokA
      mem.borrows mem.globals mem.callerLocals
    obtain ⟨hb, hbnone⟩ := evalRelOperand_frag decls locals hslots hn b hokB
      mem.borrows mem.globals mem.callerLocals
    have hsigned := operandIsSigned_of_RelOperandOk decls layouts a hokA
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_valid_of_RelOperandOk decls locals hslots a hokA x hxa
        have hy := opBits_valid_of_RelOperandOk decls locals hslots b hokB y hyb
        refine ⟨fun r hr => ?_, fun h => by simp [rvBitsO, htyA, hxa, hyb] at h⟩
        simp [rvBitsO, htyA, hxa, hyb] at hr
        subst hr
        have hres : evalScalarBinOp .cmp ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
            (signedOf T) = .ok (.scalar ⟨ordBits (cmpOf T x y), u8Ty.size.bytes⟩) locals mem := by
          cases hT with
          | int it hgood => exact evalScalarBinOp_cmp_int it hgood x y hx hy locals mem
          | bool =>
            exact evalScalarBinOp_cmp_bool x y (by simpa [ValidBits] using hx)
              (by simpa [ValidBits] using hy) locals mem
        simp only [evalRvalue, ha x hxa, hb y hyb, hsigned, hres]

/-! ## `(Int, bool)` 2-tuple rvalues and checked integer arithmetic -/

/-- Evaluating a fragment 2-tuple operand `_j` of type `(it, bool)` in Anneal's
semantics: the 2-element aggregate of its field scalars, or UB for an
uninitialized local. -/
theorem evalOperand_fragTuple {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (op : Operand) (hok : operandOkTuple decls it op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (callerLocals : List LocalSlot) :
    (∀ bits b, opTupleBits locals op = some (bits, b) →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.aggregate 0 [.scalar ⟨bits, it.size.bytes⟩, .scalar ⟨b, 1⟩]) locals) ∧
    (opTupleBits locals op = none →
      evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOkTuple, operandTupleIntType, Option.bind_eq_bind, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    obtain ⟨hj, ht⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp only [hd, Option.bind_some, decide_eq_true_eq] at ht
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots.slotOk_scalar hd hs (scalarTypeOf_tuple ht)
    unfold evalOperand
    simp only [opTupleBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .dead, _ => simp [hs]
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), ⟨_, hvb⟩ =>
      simp [intBoolTupleTy, ValidBits] at hvb
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, hsz0, _, hsz1, _⟩ =>
      simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
      subst htyT
      refine ⟨fun bits b hbb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hbb
      rcases hbb with ⟨rfl, rfl⟩
      simp [hs, readProjectedValue, ← hsz0, ← hsz1]

/-- Anneal's `AddWithOverflow`, `SubWithOverflow`, and `MulWithOverflow` on two
integers of one fragment type agree with MiniRust's `BinOp::IntWithOverflow` on
both the wrapped result (`res % 2^(8*sz)`) and the overflow flag
(`!can_represent(res)`). -/
theorem evalScalarBinOp_checked (op : MirAst.BinOp) (cop : Gen.IntBinOpWithOverflow)
    (hcop : translateCheckedBinOp op = some cop) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    let res := intCheckedArith cop (intFromBits x it) (intFromBits y it)
    let wrappedBits := (res % 2 ^ (8 * it.size.bytes)).toNat
    let ovfBit := if IntType.can_represent it res then 0 else 1
    evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
      .ok (.aggregate 0 [.scalar ⟨wrappedBits, it.size.bytes⟩, .scalar ⟨ovfBit, 1⟩])
        locals mem := by
  dsimp only
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hgood hsz hx hy ⊢
  have hbeq : Nat.beq sz 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  match op, cop, hcop with
  | .addWithOverflow, .Add, _ =>
    unfold intCheckedArith
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq]
      rw [wrap_add_intFromBits ⟨.Unsigned, ⟨sz⟩⟩ x y hx hy]
      simp only [scalarModulus_eq, nat_ble_eq_decide, canRepresent_unsigned sz hsz, intFromBits]
      by_cases hlt : x + y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x + y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int))]
        rfl
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x + y),
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int)))]
        rfl
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq,
        wrap_add_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy,
        signedOverflowAdd_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩) <;> rfl
  | .subWithOverflow, .Sub, _ =>
    unfold intCheckedArith
    have hsub := wrap_sub_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy
    dsimp only at hsub
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq,
        canRepresent_unsigned sz hsz, intFromBits]
      by_cases hle : y ≤ x
      · have hble : Nat.ble y x = true := by rw [nat_ble_eq_decide, decide_eq_true hle]
        simp only [hble] at hsub ⊢
        rw [hsub, intFromBits, intFromBits,
          decide_eq_true (by omega : 0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int))]
        rfl
      · have hble : Nat.ble y x = false := by rw [nat_ble_eq_decide, decide_eq_false hle]
        simp only [hble] at hsub ⊢
        rw [hsub, intFromBits, intFromBits,
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int)))]
        rfl
    | Signed =>
      have hxMod : MirSemantics.wrapScalarBits x (MirSemantics.scalarModulus sz) = x := by
        rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
      have hyMod : MirSemantics.wrapScalarBits y (MirSemantics.scalarModulus sz) = y := by
        rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq,
        hxMod, hyMod, signedOverflowSub_eq x y sz hsz hx hy]
      simp only [hxMod, hyMod] at hsub
      cases hble : Nat.ble y x <;> simp only [hble] at hsub ⊢ <;> rw [hsub] <;>
        cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩) <;> rfl
  | .mulWithOverflow, .Mul, _ =>
    unfold intCheckedArith
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq]
      rw [wrap_mul_intFromBits ⟨.Unsigned, ⟨sz⟩⟩ x y hx hy]
      simp only [scalarModulus_eq, nat_ble_eq_decide, canRepresent_unsigned sz hsz, intFromBits]
      have hcast : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
      by_cases hlt : x * y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x * y)), hcast,
          decide_eq_true (by omega : 0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        rfl
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x * y), hcast,
          decide_eq_false (by omega : ¬(0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int)))]
        rfl
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
        wrap_mul_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy,
        signedOverflowMul_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ * intFromBits y ⟨.Signed, ⟨sz⟩⟩) <;> rfl

/-- Evaluating a fragment rvalue of 2-tuple type `(it, bool)` in Anneal's
semantics. -/
theorem evalRvalue_fragTuple {layouts : Layout.LayoutTable} (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOkTuple layouts decls it rv = true) (mem : MirSemantics.Memory) :
    (∀ bits b, rvTupleBits locals it rv = some (bits, b) →
      evalRvalue locals rv mem decls layouts =
        .ok (.aggregate 0 [.scalar ⟨bits, it.size.bytes⟩, .scalar ⟨b, 1⟩]) locals mem) ∧
    (rvTupleBits locals it rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOkTuple] at hok
    obtain ⟨hsome, hnone⟩ :=
      evalOperand_fragTuple decls locals hslots hn it op hok mem.borrows mem.globals mem.callerLocals
    refine ⟨fun bits b hbb => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome bits b hbb]
    · simp [evalRvalue, hnone h]
  | .binaryOp op a b, hok =>
    simp only [rvalueOkTuple, Bool.and_eq_true] at hok
    obtain ⟨⟨hcopSome, hoka⟩, hokb⟩ := hok
    obtain ⟨cop, hcop⟩ := Option.isSome_iff_exists.mp hcopSome
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_frag decls locals hslots hn it b hokb mem.borrows mem.globals mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa] at hbb, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa, hyb] at hbb, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_lt decls locals hslots it a hoka x hxa
        have hy := opBits_lt decls locals hslots it b hokb y hyb
        have hsigned := operandIsSigned_of_operandOk decls layouts it a hoka
        have hchk := evalScalarBinOp_checked op cop hcop it hgood x y hx hy locals mem
        refine ⟨fun bits b' hbb => ?_, fun h => by simp [rvTupleBits, hcop, hxa, hyb] at h⟩
        simp [rvTupleBits, hcop, hxa, hyb] at hbb
        rcases hbb with ⟨rfl, rfl⟩
        simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hchk]
  | .aggregate .tuple [a, b], hok =>
    simp only [rvalueOkTuple, Bool.and_eq_true] at hok
    obtain ⟨hoka, hokb⟩ := hok
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_fragT decls locals hslots hn .bool b (operandOkB_T hokb)
        mem.borrows mem.globals mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa] at hbb, fun _ => ?_⟩
      simp [evalRvalue, evalOperands, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa, hyb] at hbb, fun _ => ?_⟩
        simp [evalRvalue, evalOperands, ha x hxa, hbnone hyb]
      | some y =>
        refine ⟨fun bits b' hbb => ?_, fun h => by simp [rvTupleBits, hxa, hyb] at h⟩
        simp [rvTupleBits, hxa, hyb] at hbb
        rcases hbb with ⟨rfl, rfl⟩
        simp [evalRvalue, evalOperands, ha x hxa, hb y hyb, u8Ty]

/-! ## Statements -/

theorem memory_mk_nil_prot (mem : MirSemantics.Memory) (hprot : mem.activeProtectors = []) :
    { mem with activeProtectors := [] } = mem := by
  cases mem; subst hprot; rfl

theorem invalidateConflictingBorrows_of_ne (borrows : List BorrowEntry) (loc : Local)
    (writerTag : Option Nat) (h : ∀ e ∈ borrows, e.targetLocal ≠ loc) :
    invalidateConflictingBorrows borrows loc writerTag = borrows := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hne : Nat.beq entry.targetLocal loc = false := by
      rw [nat_beq_eq_decide, decide_eq_false (h entry (.head _))]
    simp [invalidateConflictingBorrows, updateBorrowPerm, hne,
      ih (fun e he => h e (.tail _ he))]

theorem invalidateConflictingBorrowsAtProj_of_ne (borrows : List BorrowEntry) (loc : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (writeRangeOff : Nat := 0) (writeRangeLen : Nat := 0)
    (h : ∀ e ∈ borrows, e.targetLocal ≠ loc) :
    invalidateConflictingBorrowsAtProj borrows loc writerTag writeProj writeRangeOff writeRangeLen =
      borrows := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hne : Nat.beq entry.targetLocal loc = false := by
      rw [nat_beq_eq_decide, decide_eq_false (h entry (.head _))]
    simp [invalidateConflictingBorrowsAtProj, updateBorrowPermAtProj, hne,
      ih (fun e he => h e (.tail _ he))]

/-- Anneal's assignment to a live local `_i` from an rvalue that evaluates to
a scalar (or to UB). -/
theorem evalStmt_assign_of (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (_hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ sc, evalRvalue s.frame.locals rv s.memory decls layouts = .ok (.scalar sc) s.frame.locals s.memory →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar sc))) s.memory))) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hlive : s.frame.locals[i] ≠ .dead := fun h => hlive0 (by rw [hs, h])
  have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
  refine ⟨fun sc hsc => ?_, fun h => ?_⟩
  · simp only [evalStmt, hsc, get?, hs, set?, hi, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    | init v => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp [evalStmt, h]

theorem evalStmt_assign (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (hgood : GoodSize (itOf d layouts).size.bytes)
    (hok : rvalueOk layouts decls (itOf d layouts) rv = true)
    (hns : OpsNonScalarInit decls s.frame.locals (rvOperands rv))
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBits decls s.frame.locals (itOf d layouts) layouts rv = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d layouts).size.bytes⟩)))
          s.memory))) ∧
    (rvBits decls s.frame.locals (itOf d layouts) layouts rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  obtain ⟨hok', hnone⟩ :=
    evalRvalue_frag decls s.frame.locals hslots hn (itOf d layouts) hgood rv hok hns s.memory
  obtain ⟨hA, hAub⟩ := evalStmt_assign_of s decls layouts i rv span hslots hn d hd hlive0 hbor hprot
  exact ⟨fun r hr => hA _ (hok' r hr), fun h => hAub (hnone h)⟩

theorem evalStmt_assignB (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (hbool : isBoolTy d.ty = true) (hok : rvalueOkB layouts decls rv = true)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBitsB decls s.frame.locals rv layouts = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d layouts).size.bytes⟩)))
          s.memory))) ∧
    (rvBitsB decls s.frame.locals rv layouts = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hit : itOf d layouts = u8Ty := (tyOf_bool (layouts := layouts) hbool).2
  obtain ⟨hok', hnone⟩ := evalRvalue_fragB decls s.frame.locals hslots hn rv hok s.memory
  obtain ⟨hA, hAub⟩ := evalStmt_assign_of s decls layouts i rv span hslots hn d hd hlive0 hbor hprot
  refine ⟨fun r hr => ?_, fun h => hAub (hnone h)⟩
  rw [hit]
  exact hA _ (hok' r hr)

theorem evalStmt_assignO (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (hord : isOrderingTy d.ty = true) (hok : rvalueOkO layouts decls rv = true)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBitsO decls s.frame.locals rv layouts = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d layouts).size.bytes⟩)))
          s.memory))) ∧
    (rvBitsO decls s.frame.locals rv layouts = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hit : itOf d layouts = u8Ty := (tyOf_ordering (layouts := layouts) hord).2
  obtain ⟨hok', hnone⟩ := evalRvalue_fragO decls s.frame.locals hslots hn rv hok s.memory
  obtain ⟨hA, hAub⟩ := evalStmt_assign_of s decls layouts i rv span hslots hn d hd hlive0 hbor hprot
  refine ⟨fun r hr => ?_, fun h => hAub (hnone h)⟩
  rw [hit]
  exact hA _ (hok' r hr)

theorem evalStmt_assignTuple (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (hgood : GoodSize (itOf d layouts).size.bytes)
    (hok : rvalueOkTuple layouts decls (itOf d layouts) rv = true)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ bits b, rvTupleBits s.frame.locals (itOf d layouts) rv = some (bits, b) →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i (.init (.aggregate 0 [.scalar ⟨bits, (itOf d layouts).size.bytes⟩, .scalar ⟨b, 1⟩])))
          s.memory))) ∧
    (rvTupleBits s.frame.locals (itOf d layouts) rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hlive : s.frame.locals[i] ≠ .dead := fun h => hlive0 (by rw [hs, h])
  have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
  obtain ⟨hok', hnone⟩ :=
    evalRvalue_fragTuple decls s.frame.locals hslots hn (itOf d layouts) hgood rv hok s.memory
  refine ⟨fun bits b hbb => ?_, fun h => ?_⟩
  · simp only [evalStmt, hok' bits b hbb, get?, hs, set?, hi, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    | init v => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp [evalStmt, hnone h]

theorem evalStmt_assign_array (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hlive0 : s.frame.locals[i]? ≠ some .dead)
    (elemIt : Gen.IntType) (count : Nat) (_ha : arrayTypeOf d.ty = some (elemIt, count))
    (hok : arrayRvalueOk layouts decls elemIt count rv = true)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ elems, arrayRvElems s.frame.locals elemIt rv = some elems →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i (.init (.aggregate 0 elems)))
          s.memory))) ∧
    (arrayRvElems s.frame.locals elemIt rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hlive : s.frame.locals[i] ≠ .dead := fun h => hlive0 (by rw [hs, h])
  have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
  obtain ⟨hok', hnone⟩ :=
    evalRvalue_array_frag decls s.frame.locals hslots hn elemIt count rv hok s.memory
  refine ⟨fun elems hel => ?_, fun h => ?_⟩
  · simp only [evalStmt, hok' elems hel, get?, hs, set?, hi, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    | init v => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp [evalStmt, hnone h]

theorem evalStmt_assign_index (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (proj : ProjectionElem) (rv : Rvalue) (span : String)
    (hslots : SlotsOk layouts decls s.frame.locals) (hn : s.frame.locals.length = decls.length)
    (d : LocalDecl) (hd : decls[i]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (_ha : arrayTypeOf d.ty = some (elemIt, count))
    (hgood : GoodSize elemIt.size.bytes)
    (hproj : projOk decls count proj = true)
    (hok : rvalueOk layouts decls elemIt rv = true)
    (hns : OpsNonScalarInit decls s.frame.locals (rvOperands rv))
    (elems : List Value) (hsl : s.frame.locals[i]? = some (.init (.aggregate 0 elems)))
    (hlen : elems.length = count)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ idx r, projIdx s.frame.locals count proj = some idx →
      rvBits decls s.frame.locals elemIt layouts rv = some r →
      evalStmt s ⟨.assign ⟨i, [proj]⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))))
          s.memory))) ∧
    ((projIdx s.frame.locals count proj = none ∨ rvBits decls s.frame.locals elemIt layouts rv = none) →
      evalStmt s ⟨.assign ⟨i, [proj]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hsl' : s.frame.locals[i] = .init (.aggregate 0 elems) := by
    rw [List.getElem?_eq_getElem hi] at hsl
    exact Option.some.inj hsl
  obtain ⟨hrvOk, hrvNone⟩ :=
    evalRvalue_frag decls s.frame.locals hslots hn elemIt hgood rv hok hns s.memory
  refine ⟨fun idx r hidx hr => ?_, fun hfail => ?_⟩
  · obtain ⟨hwOk, _⟩ :=
      writeProjectedValue_proj decls s.frame.locals count elems hlen proj hproj
        (.scalar ⟨r, elemIt.size.bytes⟩)
    have hw := hwOk idx hidx
    have hinv := invalidateConflictingBorrowsAtProj_of_ne s.memory.borrows i .none [proj] 0 0 hbor
    match proj, hproj, hw, hinv with
    | .index _, _, hw, hinv =>
      simp [evalStmt, hrvOk r hr, get?, hi, hsl', hw, set?, hprot, hinv, MirStepNode.step,
        memory_mk_nil_prot s.memory hprot]
    | .constantIndex _ _ _, _, hw, hinv =>
      simp [evalStmt, hrvOk r hr, get?, hi, hsl', hw, set?, hprot, hinv, MirStepNode.step,
        memory_mk_nil_prot s.memory hprot]
  · cases hrv : rvBits decls s.frame.locals elemIt layouts rv with
    | none => simp [evalStmt, hrvNone hrv]
    | some r =>
      have hpnone : projIdx s.frame.locals count proj = none := by
        rcases hfail with hp | hr
        · exact hp
        · simp [hrv] at hr
      obtain ⟨_, hwNone⟩ :=
        writeProjectedValue_proj decls s.frame.locals count elems hlen proj hproj
          (.scalar ⟨r, elemIt.size.bytes⟩)
      have hw := hwNone hpnone
      match proj, hproj with
      | .index _, _ => simp [evalStmt, hrvOk r hrv, get?, hi, hsl', hw]
      | .constantIndex _ _ _, _ => simp [evalStmt, hrvOk r hrv, get?, hi, hsl', hw]

theorem evalStmt_assign_tuple (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dst : MirAst.Place) (dstTy : MirAst.Ty)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (htp : tuplePlaceSpec layouts decls dst = some (fields, size, align))
    (rv : Rvalue) (span : String)
    (hslots : SlotsOk layouts decls s.frame.locals) (hn : s.frame.locals.length = decls.length)
    (hok : tupleRvalueOk layouts decls dstTy fields size align rv = true)
    (rootVal : Value) (hsl : s.frame.locals[dst.local_]? = some (.init rootVal))
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ dst.local_)
    (hprot : s.memory.activeProtectors = []) :
    (∀ newVal newRootVal,
      tupleRvVal s.frame.locals fields rv = some newVal →
      writeFieldPath rootVal dst.projection newVal = some newRootVal →
      (∀ locals', MirSemantics.writeProjectedValue locals' rootVal dst.projection newVal = .ok newRootVal) →
      evalStmt s ⟨.assign dst rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set dst.local_ (.init newRootVal))
          s.memory))) ∧
    (tupleRvVal s.frame.locals fields rv = none →
      evalStmt s ⟨.assign dst rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  obtain ⟨d, _, _, _, _, hj, _, _, _, _⟩ := tuplePlaceSpec_resolve htp
  have hi : dst.local_ < s.frame.locals.length := by rw [hn]; exact hj
  have hsl' : s.frame.locals[dst.local_] = .init rootVal := by
    rw [List.getElem?_eq_getElem hi] at hsl
    exact Option.some.inj hsl
  obtain ⟨hrvOk, hrvNone⟩ :=
    evalRvalue_tuple_frag decls s.frame.locals hslots hn dstTy fields size align rv hok s.memory
  refine ⟨fun newVal newRootVal hrv hwpath hwsem => ?_, fun hnone => ?_⟩
  · rcases dst with ⟨i, projs⟩
    dsimp only at hi hsl' htp hwpath hwsem hbor ⊢
    cases projs with
    | nil =>
      simp [writeFieldPath] at hwpath
      subst hwpath
      have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
      simp [evalStmt, hrvOk newVal hrv, get?, hi, hsl', set?, hprot, hinv, MirStepNode.step,
        memory_mk_nil_prot s.memory hprot]
    | cons p rest =>
      cases p with
      | field idx fieldTy =>
        have hw := hwsem s.frame.locals
        have hinv := invalidateConflictingBorrowsAtProj_of_ne s.memory.borrows i .none
          (.field idx fieldTy :: rest) 0 0 hbor
        simp [evalStmt, hrvOk newVal hrv, get?, hi, hsl', hw, set?, hprot, hinv, MirStepNode.step,
          memory_mk_nil_prot s.memory hprot]
      | _ => simp [tuplePlaceSpec] at htp
  · simp [evalStmt, hrvNone hnone]

theorem evalStmt_assign_field_scalar (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i idx : Nat) (fieldTy : MirAst.Ty) (rest : List ProjectionElem)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (rv : Rvalue) (span : String)
    (hslots : SlotsOk layouts decls s.frame.locals) (hn : s.frame.locals.length = decls.length)
    (hi : i < decls.length)
    (hok : rvalueOk layouts decls it rv = true)
    (hns : OpsNonScalarInit decls s.frame.locals (rvOperands rv))
    (rootVal : Value) (hsl : s.frame.locals[i]? = some (.init rootVal))
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ r newRootVal,
      rvBits decls s.frame.locals it layouts rv = some r →
      (∀ locals', MirSemantics.writeProjectedValue locals' rootVal (.field idx fieldTy :: rest)
        (.scalar ⟨r, it.size.bytes⟩) = .ok newRootVal) →
      evalStmt s ⟨.assign ⟨i, .field idx fieldTy :: rest⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i (.init newRootVal))
          s.memory))) ∧
    (rvBits decls s.frame.locals it layouts rv = none →
      evalStmt s ⟨.assign ⟨i, .field idx fieldTy :: rest⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hil : i < s.frame.locals.length := by rw [hn]; exact hi
  have hsl' : s.frame.locals[i] = .init rootVal := by
    rw [List.getElem?_eq_getElem hil] at hsl
    exact Option.some.inj hsl
  obtain ⟨hrvOk, hrvNone⟩ :=
    evalRvalue_frag decls s.frame.locals hslots hn it hgood rv hok hns s.memory
  refine ⟨fun r newRootVal hr hwsem => ?_, fun hnone => ?_⟩
  · have hw := hwsem s.frame.locals
    have hinv := invalidateConflictingBorrowsAtProj_of_ne s.memory.borrows i .none
      (.field idx fieldTy :: rest) 0 0 hbor
    simp [evalStmt, hrvOk r hr, get?, hil, hsl', hw, set?, hprot, hinv, MirStepNode.step,
      memory_mk_nil_prot s.memory hprot]
  · simp [evalStmt, hrvNone hnone]

theorem evalStmt_placeMention (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (projs : List ProjectionElem) (span : String)
    (_hslots : SlotsOk layouts decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (hi : i < decls.length)
    (hlive0 : s.frame.locals[i]? ≠ some .dead) :
    evalStmt s ⟨.placeMention ⟨i, projs⟩, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) := by
  have hil : i < s.frame.locals.length := by rw [hn]; exact hi
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hil]
  have hlive : s.frame.locals[i] ≠ .dead := fun h => hlive0 (by rw [hs, h])
  simp only [evalStmt, get?, hs]
  cases hsl : s.frame.locals[i] with
  | dead => exact absurd hsl hlive
  | uninit => simp [MirStepNode.step]
  | init v => simp [MirStepNode.step]

theorem evalStmt_placeMention_place (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Place) (span : String)
    (_hslots : SlotsOk layouts decls s.frame.locals) (hn : s.frame.locals.length = decls.length)
    (hi : p.local_ < decls.length)
    (hlive0 : s.frame.locals[p.local_]? ≠ some .dead) :
    evalStmt s ⟨.placeMention p, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) :=
  evalStmt_placeMention s decls layouts p.local_ p.projection span _hslots hn hi hlive0

/-- Anneal's `StorageLive(_i)`: the slot becomes `.uninit`. -/
theorem evalStmt_storageLive (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (span : String) (hi : i < s.frame.locals.length) :
    evalStmt s ⟨.storageLive i, span⟩ decls layouts =
      .tau (.running (advanceStmt s (s.frame.locals.set i .uninit))) := by
  simp [evalStmt, get?, set?, hi, MirStepNode.step]

/-- Anneal's `StorageDead(_i)`: the slot becomes `.dead`. -/
theorem evalStmt_storageDead (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (span : String) (hi : i < s.frame.locals.length) :
    evalStmt s ⟨.storageDead i, span⟩ decls layouts =
      .tau (.running (advanceStmt s (s.frame.locals.set i .dead))) := by
  simp [evalStmt, get?, set?, hi, MirStepNode.step]

/-- Anneal's `Deinit(_i)` of a root local: the slot of a live local becomes
`.uninit`; a dead local is UB. -/
theorem evalStmt_deinit (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (span : String) (hi : i < s.frame.locals.length) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.deinit ⟨i, []⟩, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i .uninit)))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.deinit ⟨i, []⟩, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  refine ⟨fun hlive => ?_, fun hdead => ?_⟩
  · simp only [evalStmt, get?, hs]
    cases hsl : s.frame.locals[i] with
    | dead => rw [hsl] at hs; exact absurd hs hlive
    | uninit => simp [set?, hi, MirStepNode.step]
    | init v => simp [set?, hi, MirStepNode.step]
  · simp [evalStmt, get?, hdead]

/-- Anneal's `PlaceMention` of a place based on a dead local is UB. -/
theorem evalStmt_placeMention_dead (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Place) (span : String)
    (hdead : s.frame.locals[p.local_]? = some .dead) :
    evalStmt s ⟨.placeMention p, span⟩ decls layouts = MirStepNode.fail .ub := by
  simp [evalStmt, get?, hdead]

/-! ## Moves

Anneal's `evalOperand` de-initializes a local that it reads through a root
`move _j` ("reading a root local via `Operand.move` transitions its slot to
`.uninit`"); every other operand reads like its `copy` form (`copyOp`). The
lemmas below reduce the evaluation of fragment operands, rvalues, and
assignments with `move` operands to the evaluation of their `copy` forms,
whose results the lemmas above compute, followed by the de-initialization
(`opPost`, `rvPost`). -/

/-- An operand evaluation result with its slots replaced by `L'`. -/
def opWithLocals : PlaceReadResult → List LocalSlot → PlaceReadResult
  | .ok v _, L' => .ok v L'
  | r, _ => r

/-- An operand-list evaluation result with its slots replaced by `L'`. -/
def opsWithLocals : OperandsEvalResult → List LocalSlot → OperandsEvalResult
  | .ok vs _, L' => .ok vs L'
  | r, _ => r

/-- An rvalue evaluation result with its slots replaced by `L'`. -/
def rvWithLocals : RvalueEvalResult → List LocalSlot → RvalueEvalResult
  | .ok v _ m, L' => .ok v L' m
  | r, _ => r

/-- Anneal's slots after reading `op`: a root `move _j` of a live local
leaves `_j` uninitialized (reading a dead local is UB, so how this function
treats one does not matter; it keeps the slot dead). -/
def opPost (locals : List LocalSlot) (op : Operand) : List LocalSlot :=
  match opMoved op with
  | some j =>
    match locals[j]? with
    | some .dead => locals
    | _ => locals.set j .uninit
  | none => locals

/-- Anneal's slots after reading the operands `ops` in order. -/
def opsPost (locals : List LocalSlot) (ops : List Operand) : List LocalSlot :=
  ops.foldl opPost locals

/-- Anneal's slots after reading the operands of `rv` in order. -/
def rvPost (locals : List LocalSlot) (rv : Rvalue) : List LocalSlot :=
  opsPost locals (rvOperands rv)

theorem opPost_length (locals : List LocalSlot) (op : Operand) :
    (opPost locals op).length = locals.length := by
  unfold opPost
  split
  · split <;> simp
  · rfl

theorem opsPost_length (locals : List LocalSlot) (ops : List Operand) :
    (opsPost locals ops).length = locals.length := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op ops ih => simp only [opsPost, List.foldl_cons] at ih ⊢; rw [ih, opPost_length]

theorem rvPost_length (locals : List LocalSlot) (rv : Rvalue) :
    (rvPost locals rv).length = locals.length :=
  opsPost_length locals _

/-- `opPost` changes at most the slot of the local that `op` moves out of,
to `.uninit`, and never a dead slot. -/
theorem opPost_get (locals : List LocalSlot) (op : Operand) (k : Nat) :
    (opPost locals op)[k]? = locals[k]? ∨
      (opMoved op = some k ∧ (opPost locals op)[k]? = some .uninit ∧
        ∃ s, locals[k]? = some s ∧ s ≠ .dead) := by
  unfold opPost
  cases hm : opMoved op with
  | none => exact .inl rfl
  | some j =>
    simp only
    cases hj : locals[j]? with
    | none =>
      left
      have : locals.length ≤ j := List.getElem?_eq_none_iff.mp hj
      rw [List.getElem?_set]
      split <;> simp_all
    | some s =>
      cases s with
      | dead => exact .inl rfl
      | uninit =>
        by_cases hkj : j = k
        · subst hkj
          right
          have := (List.getElem?_eq_some_iff.mp hj).1
          exact ⟨rfl, List.getElem?_set_self this, .uninit, hj, by simp⟩
        · left; simp [List.getElem?_set_ne hkj]
      | init v =>
        by_cases hkj : j = k
        · subst hkj
          right
          have := (List.getElem?_eq_some_iff.mp hj).1
          exact ⟨rfl, List.getElem?_set_self this, .init v, hj, by simp⟩
        · left; simp [List.getElem?_set_ne hkj]

theorem opPost_dead (locals : List LocalSlot) (op : Operand) (k : Nat) :
    (opPost locals op)[k]? = some .dead ↔ locals[k]? = some .dead := by
  rcases opPost_get locals op k with h | ⟨_, h1, s, h2, h3⟩
  · rw [h]
  · rw [h1, h2]; simp [h3]

theorem rvPost_dead (locals : List LocalSlot) (rv : Rvalue) (k : Nat) :
    (rvPost locals rv)[k]? = some .dead ↔ locals[k]? = some .dead := by
  unfold rvPost opsPost
  generalize rvOperands rv = ops
  induction ops generalizing locals with
  | nil => rfl
  | cons op ops ih => simp only [List.foldl_cons]; rw [ih, opPost_dead]

/-- `opPost` keeps the slot facts, which hold of `.uninit`. -/
theorem opPost_slots {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {locals : List LocalSlot} (h : SlotsOk layouts decls locals) (op : Operand) :
    SlotsOk layouts decls (opPost locals op) := by
  intro i d slot hd hs
  rcases opPost_get locals op i with h1 | ⟨_, h1, _⟩
  · rw [h1] at hs; exact h i d slot hd hs
  · rw [h1] at hs; cases hs; exact declSlotOk_uninit d layouts

theorem rvPost_slots {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {locals : List LocalSlot} (h : SlotsOk layouts decls locals) (rv : Rvalue) :
    SlotsOk layouts decls (rvPost locals rv) := by
  unfold rvPost opsPost
  generalize rvOperands rv = ops
  induction ops generalizing locals with
  | nil => exact h
  | cons op ops ih => simp only [List.foldl_cons]; exact ih (opPost_slots h op)

theorem opWithLocals_ok {r : PlaceReadResult} {L : List LocalSlot}
    (h : ∀ v L', r = .ok v L' → L' = L) : opWithLocals r L = r := by
  cases r with
  | ok v L' => rw [h v L' rfl]; rfl
  | ub => rfl
  | unsupported => rfl

theorem local_mem_placeLocals (p : Place) : p.local_ ∈ placeLocals p := by
  rcases p with ⟨j, projs⟩
  cases projs with
  | nil => simp [placeLocals]
  | cons hd tl =>
    cases hd <;> cases tl <;> simp [placeLocals]

theorem simpleProj_nonDeref {projs : List ProjectionElem} (hs : simpleProj projs = true) :
    ∀ rest, projs ≠ .deref :: rest := by
  intro rest hr
  subst hr
  cases rest <;> simp [simpleProj, allFields] at hs

theorem readProjectedValue_allFields_frame (L L' : List LocalSlot) (v : Value)
    (projs : List ProjectionElem) (hf : allFields projs = true) :
    readProjectedValue L' v projs = readProjectedValue L v projs := by
  induction projs generalizing v with
  | nil => rfl
  | cons p rest ih =>
    cases p <;> simp [allFields] at hf
    rename_i idx ty
    cases v with
    | aggregate varIdx fields =>
      simp only [readProjectedValue]
      cases get? fields idx with
      | none => rfl
      | some fv => exact ih fv hf
    | scalar sc =>
      cases idx with
      | zero => simp only [readProjectedValue]; exact ih (.scalar sc) hf
      | succ _ => rfl
    | ptr p sz =>
      cases idx with
      | zero => simp only [readProjectedValue]; exact ih (.ptr p sz) hf
      | succ _ => rfl
    | unit =>
      cases idx with
      | zero => simp only [readProjectedValue]; exact ih .unit hf
      | succ _ => rfl

theorem readProjectedValue_simpleProj_frame (L L' : List LocalSlot) (j : Nat) (v : Value)
    (projs : List ProjectionElem) (hs : simpleProj projs = true)
    (hagree : ∀ k ∈ placeLocals ⟨j, projs⟩, L'[k]? = L[k]?) :
    readProjectedValue L' v projs = readProjectedValue L v projs := by
  cases projs with
  | nil => rfl
  | cons p rest =>
    cases p with
    | field idx ty =>
      have hf : allFields (.field idx ty :: rest) = true := by
        cases rest with
        | nil => rfl
        | cons _ _ => exact hs
      exact readProjectedValue_allFields_frame L L' v (.field idx ty :: rest) hf
    | index idxLocal =>
      cases rest with
      | cons _ _ => simp [simpleProj, allFields] at hs
      | nil =>
        have hidx : L'[idxLocal]? = L[idxLocal]? := hagree idxLocal (by simp [placeLocals])
        cases v with
        | aggregate varIdx fields =>
          cases varIdx with
          | zero =>
            unfold readProjectedValue
            simp only [get?, hidx]
            cases L[idxLocal]? with
            | none => rfl
            | some slot =>
              cases slot with
              | dead => rfl
              | uninit => rfl
              | init iv =>
                cases iv with
                | scalar sc =>
                  cases fields[sc.bits]? <;> rfl
                | _ => rfl
          | succ _ => rfl
        | _ => rfl
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | cons _ _ => simp [simpleProj, allFields] at hs
      | nil =>
        cases v with
        | aggregate varIdx fields =>
          cases varIdx with
          | zero =>
            unfold readProjectedValue
            cases Nat.ble minLen (length fields) with
            | false => rfl
            | true =>
              dsimp only []
              cases get? fields (match fromEnd with | true => Nat.sub (length fields) offset | false => offset) <;>
                rfl
          | succ _ => rfl
        | _ => rfl
    | _ => simp [simpleProj, allFields] at hs

/-- Reading a fragment operand's `copy` form depends only on the slots of the
locals it reads, and returns the slots unchanged. -/
theorem evalOperand_copy_frame (L L' : List LocalSlot) (op : Operand) (hs : simpleOp op = true)
    (hagree : ∀ j ∈ opLocals op, L'[j]? = L[j]?)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand L' (copyOp op) borrows globals layouts callerLocals =
      opWithLocals (evalOperand L (copyOp op) borrows globals layouts callerLocals) L' := by
  cases op with
  | constant c =>
    simp only [copyOp, evalOperand]
    (repeat' split) <;> simp_all [opWithLocals]
  | copy p =>
    have hsp : simpleProj p.projection = true := by rcases p with ⟨_, _⟩; exact hs
    have hnd := simpleProj_nonDeref hsp
    have hj : L'[p.local_]? = L[p.local_]? := hagree p.local_ (local_mem_placeLocals p)
    simp only [copyOp]
    rw [evalOperand_copy_nonDeref L' p hnd, evalOperand_copy_nonDeref L p hnd]
    simp only [get?, hj]
    cases L[p.local_]? with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | uninit => rfl
      | init rootVal =>
        simp only []
        rw [readProjectedValue_simpleProj_frame L L' p.local_ rootVal p.projection hsp
          (by rcases p with ⟨_, _⟩; exact hagree)]
        cases readProjectedValue L rootVal p.projection <;> rfl
  | move p =>
    have hsp : simpleProj p.projection = true := by rcases p with ⟨_, _⟩; exact hs
    have hnd := simpleProj_nonDeref hsp
    have hj : L'[p.local_]? = L[p.local_]? := hagree p.local_ (local_mem_placeLocals p)
    simp only [copyOp]
    rw [evalOperand_copy_nonDeref L' p hnd, evalOperand_copy_nonDeref L p hnd]
    simp only [get?, hj]
    cases L[p.local_]? with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | uninit => rfl
      | init rootVal =>
        simp only []
        rw [readProjectedValue_simpleProj_frame L L' p.local_ rootVal p.projection hsp
          (by rcases p with ⟨_, _⟩; exact hagree)]
        cases readProjectedValue L rootVal p.projection <;> rfl

/-- Reading a fragment operand: its `move` form reads like its `copy` form,
then de-initializes a root local (`opPost`). -/
theorem evalOperand_move (locals : List LocalSlot) (op : Operand) (hs : simpleOp op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand locals op borrows globals layouts callerLocals =
      opWithLocals (evalOperand locals (copyOp op) borrows globals layouts callerLocals)
        (opPost locals op) := by
  cases op with
  | constant c =>
    exact evalOperand_copy_frame locals locals (.constant c) hs (fun _ _ => rfl) _ _ _ _
  | copy p =>
    exact evalOperand_copy_frame locals locals (.copy p) hs (fun _ _ => rfl) _ _ _ _
  | move p =>
    rcases p with ⟨j, projs⟩
    cases projs with
    | nil =>
      simp only [copyOp, opPost, opMoved, evalOperand, get?, set?]
      cases hj : locals[j]? with
      | none => rfl
      | some s =>
        have hjl := (List.getElem?_eq_some_iff.mp hj).1
        cases s with
        | dead => rfl
        | uninit => rfl
        | init v => simp [hjl, readProjectedValue, opWithLocals]
    | cons hd tl =>
      have hsp : simpleProj (hd :: tl) = true := hs
      have hnd := simpleProj_nonDeref hsp
      have hmv_eq : evalOperand locals (.move ⟨j, hd :: tl⟩) borrows globals layouts callerLocals =
          evalOperand locals (.copy ⟨j, hd :: tl⟩) borrows globals layouts callerLocals := by
        cases hd with
        | deref => exact False.elim (hnd tl rfl)
        | _ => rfl
      have hpost : opPost locals (.move ⟨j, hd :: tl⟩) = locals := rfl
      rw [hmv_eq, hpost]
      exact evalOperand_copy_frame locals locals (.copy ⟨j, hd :: tl⟩) hs (fun _ _ => rfl) _ _ _ _

theorem evalSignedDiv_locals (x y sz : Nat) (L L' : List LocalSlot) (mem : MirSemantics.Memory) :
    MirSemantics.evalSignedDiv x y sz L' mem =
      rvWithLocals (MirSemantics.evalSignedDiv x y sz L mem) L' := by
  simp only [MirSemantics.evalSignedDiv]
  (repeat' split) <;> rfl

theorem evalSignedRem_locals (x y sz : Nat) (L L' : List LocalSlot) (mem : MirSemantics.Memory) :
    MirSemantics.evalSignedRem x y sz L' mem =
      rvWithLocals (MirSemantics.evalSignedRem x y sz L mem) L' := by
  simp only [MirSemantics.evalSignedRem]
  (repeat' split) <;> rfl

theorem evalScalarBinOp_locals (op : BinOp) (lhs rhs : ScalarInt) (L L' : List LocalSlot)
    (mem : MirSemantics.Memory) (s : Bool) :
    evalScalarBinOp op lhs rhs L' mem s = rvWithLocals (evalScalarBinOp op lhs rhs L mem s) L' := by
  unfold evalScalarBinOp
  split
  · rfl
  · cases op <;> simp only [] <;> (repeat' split) <;>
      first | rfl | exact evalSignedDiv_locals _ _ _ _ _ _ | exact evalSignedRem_locals _ _ _ _ _ _

theorem evalUnaryNot_locals (sc : ScalarInt) (ty : Option Ty) (L L' : List LocalSlot)
    (mem : MirSemantics.Memory) :
    evalUnaryNot sc ty L' mem = rvWithLocals (evalUnaryNot sc ty L mem) L' := by
  unfold evalUnaryNot
  (repeat' split) <;> rfl

theorem operandTy_copyOp (decls : List LocalDecl) (layouts : Layout.LayoutTable) (op : Operand) :
    operandTy decls layouts (copyOp op) = operandTy decls layouts op := by
  cases op <;> rfl

theorem operandIsSigned_copyOp (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (op : Operand) :
    operandIsSigned decls (copyOp op) layouts = operandIsSigned decls op layouts := by
  cases op <;> rfl

/-- The operands that `readsOk mo ops` accepts are simple and read no local
of `mo`. -/
theorem readsOk_spec {mo : List Nat} {ops : List Operand} (h : readsOk mo ops = true) :
    ∀ op ∈ ops, simpleOp op = true ∧ ∀ j ∈ opLocals op, j ∉ mo := by
  induction ops generalizing mo with
  | nil => simp
  | cons op ops ih =>
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hs, hr⟩, hrest⟩ := h
    intro op' hop'
    rcases List.mem_cons.mp hop' with rfl | hin
    · refine ⟨hs, fun j hj => ?_⟩
      simpa using hr j hj
    · obtain ⟨hs', hr'⟩ := ih hrest op' hin
      refine ⟨hs', fun j hj hjm => hr' j hj ?_⟩
      unfold moveOut
      split <;> simp [hjm]

/-- `opPost` changes only the local that `op` moves out of. -/
theorem opPost_get_of_ne (locals : List LocalSlot) (op : Operand) (k : Nat)
    (hk : opMoved op ≠ some k) : (opPost locals op)[k]? = locals[k]? := by
  rcases opPost_get locals op k with h | ⟨h, _⟩
  · exact h
  · exact absurd h hk

theorem opsPost_get_of_not_mem (locals : List LocalSlot) (ops : List Operand) (k : Nat)
    (hk : ∀ op ∈ ops, opMoved op ≠ some k) : (opsPost locals ops)[k]? = locals[k]? := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op ops ih =>
    simp only [opsPost, List.foldl_cons] at ih ⊢
    rw [ih _ (fun op' h => hk op' (by simp [h])), opPost_get_of_ne _ _ _ (hk op (by simp))]

/-- Under `readsOk`, an operand never reads a local that an earlier operand
moves out of. -/
theorem readsOk_moved {mo : List Nat} {op : Operand} {ops : List Operand}
    (h : readsOk mo (op :: ops) = true) :
    ∀ op' ∈ ops, ∀ j ∈ opLocals op', opMoved op ≠ some j := by
  intro op' hop' j hj hm
  simp only [readsOk, Bool.and_eq_true] at h
  have := (readsOk_spec h.2 op' hop').2 j hj
  apply this
  simp [moveOut, hm]

theorem opResult_locals {r : PlaceReadResult} {L : List LocalSlot} (h : r = opWithLocals r L)
    {v : Value} {L1 : List LocalSlot} (hr : r = .ok v L1) : L1 = L := by
  rw [hr] at h
  simpa [opWithLocals] using h

/-- Reading the operands of a fragment aggregate: the `move` forms read like the
`copy` forms, then de-initialize the root locals they move out of. -/
theorem evalOperands_move (mo : List Nat) (locals : List LocalSlot) (ops : List Operand)
    (h : readsOk mo ops = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    evalOperands locals ops borrows globals layouts callerLocals =
      opsWithLocals (evalOperands locals (ops.map copyOp) borrows globals layouts callerLocals)
        (opsPost locals ops) ∧
    ∀ L', (∀ op ∈ ops, ∀ j ∈ opLocals op, L'[j]? = locals[j]?) →
      evalOperands L' (ops.map copyOp) borrows globals layouts callerLocals =
        opsWithLocals (evalOperands locals (ops.map copyOp) borrows globals layouts callerLocals) L' := by
  induction ops generalizing mo locals with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons op ops ih =>
    have hspec := readsOk_spec h
    obtain ⟨hs, _⟩ := hspec op (by simp)
    have hrest : readsOk (moveOut mo op) ops = true := by
      simp only [readsOk, Bool.and_eq_true] at h; exact h.2
    have hmv := readsOk_moved h
    have hmove := evalOperand_move locals op hs borrows globals layouts callerLocals
    have hcopy := evalOperand_copy_frame locals locals op hs (fun _ _ => rfl) borrows globals
      layouts callerLocals
    obtain ⟨ih1, ih2⟩ := ih (moveOut mo op) (opPost locals op) hrest
    obtain ⟨_, ih2'⟩ := ih (moveOut mo op) locals hrest
    refine ⟨?_, fun L' hL' => ?_⟩
    · simp only [List.map_cons, evalOperands]
      rw [hmove]
      cases hc : evalOperand locals (copyOp op) borrows globals layouts callerLocals with
      | ok v L1 =>
        rw [opResult_locals hcopy hc]
        simp only [opWithLocals]
        rw [ih1, ih2' (opPost locals op) (fun op' hop' j hj =>
          opPost_get_of_ne _ _ _ (hmv op' hop' j hj))]
        cases evalOperands locals (ops.map copyOp) borrows globals layouts callerLocals <;> rfl
      | ub => rfl
      | unsupported => rfl
    · simp only [List.map_cons, evalOperands]
      rw [evalOperand_copy_frame locals L' op hs (fun j hj => hL' op (by simp) j hj)]
      cases hc : evalOperand locals (copyOp op) borrows globals layouts callerLocals with
      | ok v L1 =>
        rw [opResult_locals hcopy hc]
        simp only [opWithLocals]
        rw [ih2' L' (fun op' hop' j hj => hL' op' (by simp [hop']) j hj)]
        cases evalOperands locals (ops.map copyOp) borrows globals layouts callerLocals <;> rfl
      | ub => rfl
      | unsupported => rfl

/-- The rvalue kinds whose evaluation `evalRvalue_move` reduces: those of
the fragment (including `CopyForDeref` and the cast kinds `IntToInt`,
`PtrToPtr`, and `Transmute`). -/
def moveKind : Rvalue → Bool
  | .use _ | .copyForDeref _ | .repeat _ _ | .len _ | .unaryOp .not _ | .unaryOp .neg _
  | .binaryOp _ _ _ | .cast .intToInt _ _ | .cast .ptrToPtr _ _ | .cast .transmute _ _
  | .aggregate .tuple _ | .aggregate (.array _) _ | .aggregate (.adt _ 0 none) _ => true
  | _ => false

theorem opsResult_locals {r : OperandsEvalResult} {L : List LocalSlot} (h : r = opsWithLocals r L)
    {vs : List Value} {L1 : List LocalSlot} (hr : r = .ok vs L1) : L1 = L := by
  rw [hr] at h
  simpa [opsWithLocals] using h

/-- Evaluating a fragment rvalue: its `move` operands read like their `copy`
forms, then the moved-out root locals are uninitialized (`rvPost`). -/
theorem evalRvalue_move (locals : List LocalSlot) (rv : Rvalue) (hk : moveKind rv = true)
    (hr : readsOk [] (rvOperands rv) = true)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable) :
    evalRvalue locals rv mem decls layouts =
      rvWithLocals (evalRvalue locals (copyRv rv) mem decls layouts) (rvPost locals rv) := by
  have hspec := readsOk_spec hr
  match rv, hk with
  | .use op, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals <;> rfl
  | .copyForDeref p, _ =>
    obtain ⟨hs, _⟩ := hspec (.copy p) (by simp [rvOperands])
    have hcopy := evalOperand_copy_frame locals locals (.copy p) hs (fun _ _ => rfl)
      mem.borrows mem.globals layouts mem.callerLocals
    have hpost : opPost locals (.copy p) = locals := rfl
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl, hpost]
    cases hc : evalOperand locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      rw [opResult_locals hcopy hc]
      rfl
    | ub => rfl
    | unsupported => rfl
  | .repeat op c, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals <;> rfl
  | .len p, _ =>
    obtain ⟨hs, _⟩ := hspec (.copy p) (by simp [rvOperands])
    have hcopy := evalOperand_copy_frame locals locals (.copy p) hs (fun _ _ => rfl)
      mem.borrows mem.globals layouts mem.callerLocals
    have hpost : opPost locals (.copy p) = locals := rfl
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl, hpost]
    cases hc : evalOperand locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      rw [opResult_locals hcopy hc]
      cases v with
      | aggregate varIdx elems => cases varIdx <;> rfl
      | _ => rfl
    | ub => rfl
    | unsupported => rfl
  | .unaryOp .not op, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs, operandTy_copyOp]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      cases v <;> simp only [opWithLocals] <;> first | rfl | exact evalUnaryNot_locals _ _ _ _ _
    | ub => rfl
    | unsupported => rfl
  | .unaryOp .neg op, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      cases v <;> simp only [opWithLocals] <;> try rfl
      split <;> rfl
    | ub => rfl
    | unsupported => rfl
  | .binaryOp bop a b, _ =>
    obtain ⟨hsa, _⟩ := hspec a (by simp [rvOperands])
    obtain ⟨hsb, _⟩ := hspec b (by simp [rvOperands])
    have hmv := readsOk_moved (op := a) (ops := [b]) hr
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals a hsa, operandIsSigned_copyOp]
    have hca := evalOperand_copy_frame locals locals a hsa (fun _ _ => rfl) mem.borrows mem.globals
      layouts mem.callerLocals
    have hcb := evalOperand_copy_frame locals locals b hsb (fun _ _ => rfl) mem.borrows mem.globals
      layouts mem.callerLocals
    cases hc : evalOperand locals (copyOp a) mem.borrows mem.globals layouts mem.callerLocals with
    | ok va L1 =>
      rw [opResult_locals hca hc]
      simp only [opWithLocals]
      rw [evalOperand_move (opPost locals a) b hsb,
        evalOperand_copy_frame locals (opPost locals a) b hsb
          (fun j hj => opPost_get_of_ne _ _ _ (hmv b (by simp) j hj))]
      cases hd : evalOperand locals (copyOp b) mem.borrows mem.globals layouts mem.callerLocals with
      | ok vb L2 =>
        rw [opResult_locals hcb hd]
        simp only [opWithLocals]
        cases va <;> cases vb <;> simp only [] <;>
          first | rfl | exact evalScalarBinOp_locals _ _ _ _ _ _ _ | (cases bop <;> rfl)
      | ub => rfl
      | unsupported => rfl
    | ub => rfl
    | unsupported => rfl
  | .cast .intToInt op ty, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs, operandIsSigned_copyOp]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      cases v <;> simp only [opWithLocals] <;> try rfl
      split
      · rfl
      · split <;> rfl
    | ub => rfl
    | unsupported => rfl
  | .cast .ptrToPtr op ty, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      simp only [opWithLocals]
      rcases v with _ | _ | _ | ⟨idx, fields⟩
      · rfl
      · rfl
      · rfl
      · rcases fields with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩ <;>
          rcases idx with _ | idx <;>
          (try rcases e1 with _ | _ | _ | _) <;>
          (try rcases e2 with _ | _ | _ | _) <;>
          rfl
    | ub => rfl
    | unsupported => rfl
  | .cast .transmute op ty, _ =>
    obtain ⟨hs, _⟩ := hspec op (by simp [rvOperands])
    simp only [evalRvalue, evalByteCast, copyRv, rvPost, opsPost, rvOperands, List.foldl]
    rw [evalOperand_move locals op hs, operandTy_copyOp]
    cases evalOperand locals (copyOp op) mem.borrows mem.globals layouts mem.callerLocals with
    | ok v L1 =>
      simp only [opWithLocals]
      repeat (first | rfl | split | dsimp only [])
    | ub => rfl
    | unsupported => rfl
  | .aggregate .tuple ops, _ =>
    simp only [evalRvalue, copyRv, rvPost, rvOperands]
    rw [(evalOperands_move [] locals ops hr mem.borrows mem.globals layouts mem.callerLocals).1]
    cases evalOperands locals (ops.map copyOp) mem.borrows mem.globals layouts mem.callerLocals <;>
      rfl
  | .aggregate (.array elemTy) ops, _ =>
    simp only [evalRvalue, copyRv, rvPost, rvOperands]
    rw [(evalOperands_move [] locals ops hr mem.borrows mem.globals layouts mem.callerLocals).1]
    cases evalOperands locals (ops.map copyOp) mem.borrows mem.globals layouts mem.callerLocals <;>
      rfl
  | .aggregate (.adt defId 0 none) ops, _ =>
    simp only [evalRvalue, copyRv, rvPost, rvOperands]
    rw [(evalOperands_move [] locals ops hr mem.borrows mem.globals layouts mem.callerLocals).1]
    cases evalOperands locals (ops.map copyOp) mem.borrows mem.globals layouts mem.callerLocals <;>
      rfl

theorem copyRv_copyRv (rv : Rvalue) : copyRv (copyRv rv) = copyRv rv := by
  have hop : ∀ op : Operand, copyOp (copyOp op) = copyOp op := by intro op; cases op <;> rfl
  cases rv <;> first | rfl | simp [copyRv, hop]

theorem rvOperands_copyRv (rv : Rvalue) : rvOperands (copyRv rv) = (rvOperands rv).map copyOp := by
  cases rv <;> simp [copyRv, rvOperands, copyOp]

theorem opRead_copyOp (op : Operand) : opRead (copyOp op) = opRead op := by
  cases op <;> rfl

theorem opLocals_copyOp (op : Operand) : opLocals (copyOp op) = opLocals op := by
  cases op <;> rfl

theorem opMoved_copyOp (op : Operand) : opMoved (copyOp op) = none := by
  cases op <;> rfl

theorem simpleOp_copyOp (op : Operand) : simpleOp (copyOp op) = simpleOp op := by
  cases op <;> rfl

theorem moveKind_copyRv {rv : Rvalue} (h : moveKind rv = true) : moveKind (copyRv rv) = true := by
  match rv, h with
  | .use _, _ | .copyForDeref _, _ | .repeat _ _, _ | .len _, _
  | .unaryOp .not _, _ | .unaryOp .neg _, _
  | .binaryOp _ _ _, _ | .cast .intToInt _ _, _ | .cast .ptrToPtr _ _, _
  | .cast .transmute _ _, _
  | .aggregate .tuple _, _ | .aggregate (.array _) _, _ | .aggregate (.adt _ 0 none) _, _ => rfl

theorem readsOk_copy {mo : List Nat} {ops : List Operand} (h : readsOk mo ops = true) :
    readsOk [] (ops.map copyOp) = true := by
  induction ops generalizing mo with
  | nil => rfl
  | cons op ops ih =>
    simp only [readsOk, Bool.and_eq_true] at h
    have hm : moveOut [] (copyOp op) = [] := by simp [moveOut, opMoved_copyOp]
    simp [readsOk, simpleOp_copyOp, opLocals_copyOp, h.1.1, hm, ih h.2]

theorem opsPost_copy (locals : List LocalSlot) (ops : List Operand) :
    opsPost locals (ops.map copyOp) = locals := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons, opsPost, List.foldl_cons] at ih ⊢
    have : opPost locals (copyOp op) = locals := by simp [opPost, opMoved_copyOp]
    rw [this, ih]

/-- Evaluating the `copy` form of a fragment rvalue returns the slots
unchanged. -/
theorem evalRvalue_copy_locals (locals : List LocalSlot) (rv : Rvalue) (hk : moveKind rv = true)
    (hr : readsOk [] (rvOperands rv) = true)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {v : Value} {L1 : List LocalSlot} {mem1 : MirSemantics.Memory}
    (h : evalRvalue locals (copyRv rv) mem decls layouts = .ok v L1 mem1) : L1 = locals := by
  have hc := evalRvalue_move locals (copyRv rv) (moveKind_copyRv hk)
    (by rw [rvOperands_copyRv]; exact readsOk_copy hr) mem decls layouts
  rw [copyRv_copyRv, h] at hc
  have hp : rvPost locals (copyRv rv) = locals := by
    unfold rvPost; rw [rvOperands_copyRv]; exact opsPost_copy locals _
  rw [hp] at hc
  simpa [rvWithLocals] using hc

/-- Anneal's assignment to the root local `_i` from a fragment rvalue: like
the assignment from its `copy` form, except that the locals it moves out of
end up uninitialized (`rvPost`); a dead `_i` is UB. -/
theorem evalStmt_assign_move (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (rv : Rvalue) (span : String)
    (hk : moveKind rv = true) (hr : readsOk [] (rvOperands rv) = true)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ v, evalRvalue s.frame.locals (copyRv rv) s.memory decls layouts =
        .ok v s.frame.locals s.memory →
      (s.frame.locals[i]? ≠ some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
          .tau (.running (advanceStmt s ((rvPost s.frame.locals rv).set i (.init v))
            s.memory))) ∧
      (s.frame.locals[i]? = some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub)) ∧
    (evalRvalue s.frame.locals (copyRv rv) s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hR := evalRvalue_move s.frame.locals rv hk hr s.memory decls layouts
  have hil : i < (rvPost s.frame.locals rv).length := by rw [rvPost_length]; exact hi
  have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
  refine ⟨fun v hv => ⟨fun hlive => ?_, fun hdead => ?_⟩, fun hu => ?_⟩
  · simp only [evalStmt]
    rw [hR, hv]
    simp only [rvWithLocals, get?]
    cases hsl : (rvPost s.frame.locals rv)[i]? with
    | none => simp [hil] at hsl
    | some slot =>
      cases slot with
      | dead => exact absurd ((rvPost_dead _ _ _).mp hsl) hlive
      | uninit => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
      | init w => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp only [evalStmt]
    rw [hR, hv]
    simp only [rvWithLocals, get?, (rvPost_dead _ _ _).mpr hdead]
  · simp only [evalStmt]
    rw [hR, hu]
    rfl

theorem projIdx_frame {L V : List LocalSlot} (j count : Nat) (proj : ProjectionElem)
    (h : ∀ k ∈ placeLocals ⟨j, [proj]⟩, L[k]? = V[k]?) :
    projIdx L count proj = projIdx V count proj := by
  cases proj with
  | index idxLocal =>
    have hk : L[idxLocal]? = V[idxLocal]? := h idxLocal (by simp [placeLocals])
    simp [projIdx, hk]
  | constantIndex _ _ _ => rfl
  | _ => rfl

theorem opBits_frame {L V : List LocalSlot} (op : Operand)
    (h : ∀ k ∈ opLocals op, L[k]? = V[k]?) : opBits L op = opBits V op := by
  cases op with
  | constant _ => rfl
  | move _ => rfl
  | copy p =>
    rcases p with ⟨j, projs⟩
    have hj : L[j]? = V[j]? := h j (local_mem_placeLocals ⟨j, projs⟩)
    cases projs with
    | nil => simp [opBits, hj]
    | cons hd tl =>
      by_cases hfield : ∃ idx fieldTy, hd = .field idx fieldTy
      · obtain ⟨idx, fieldTy, rfl⟩ := hfield
        simp [opBits, hj]
      · cases tl with
        | cons _ _ =>
          cases hd with
          | field idx fieldTy => exact False.elim (hfield ⟨idx, fieldTy, rfl⟩)
          | _ => rfl
        | nil =>
          have hp : ∀ count, projIdx L count hd = projIdx V count hd := fun count =>
            projIdx_frame j count hd h
          have hop : ∀ X, opBits X (.copy ⟨j, [hd]⟩) =
              match X[j]? with
              | some (.init (.aggregate 0 elems)) =>
                match projIdx X elems.length hd with
                | some idx =>
                  match elems[idx]? with
                  | some (.scalar sc) => some sc.bits
                  | _ => none
                | none => none
              | _ => none := by
            intro X
            cases hd with
            | field idx fieldTy => exact False.elim (hfield ⟨idx, fieldTy, rfl⟩)
            | _ => rfl
          rw [hop L, hop V, hj]
          cases V[j]? with
          | none => rfl
          | some slot =>
            cases slot with
            | dead => rfl
            | uninit => rfl
            | init v =>
              cases v with
              | aggregate varIdx elems =>
                cases varIdx with
                | zero => simp only []; rw [hp elems.length]
                | succ _ => rfl
              | _ => rfl

theorem opTupleBits_frame {L V : List LocalSlot} (op : Operand)
    (h : ∀ k ∈ opLocals op, L[k]? = V[k]?) : opTupleBits L op = opTupleBits V op := by
  cases op with
  | copy p =>
    rcases p with ⟨j, projs⟩
    cases projs with
    | nil =>
      have hj : L[j]? = V[j]? := h j (by simp [opLocals, placeLocals])
      simp [opTupleBits, hj]
    | cons _ _ => rfl
  | _ => rfl

/-- The slots `L` and `V` agree on every local that the operands `ops` read. -/
def ReadsAgree (L V : List LocalSlot) (ops : List Operand) : Prop :=
  ∀ op ∈ ops, ∀ j ∈ opLocals op, L[j]? = V[j]?

theorem ReadsAgree.of_copyRv {L V : List LocalSlot} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    ReadsAgree L V (rvOperands (copyRv rv)) := by
  intro op hop j hj
  rw [rvOperands_copyRv] at hop
  obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
  rw [opLocals_copyOp] at hj
  exact h op0 hop0 j hj

theorem ReadsAgree.copy {L V : List LocalSlot} {ops : List Operand} (h : ReadsAgree L V ops) :
    ∀ op ∈ ops.map copyOp, opBits L op = opBits V op ∧ opTupleBits L op = opTupleBits V op := by
  intro op hop
  obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
  have h' : ∀ j ∈ opLocals (copyOp op0), L[j]? = V[j]? := by
    rw [opLocals_copyOp]; exact h op0 hop0
  exact ⟨opBits_frame _ h', opTupleBits_frame _ h'⟩

theorem rvBits_frame_raw {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {L V : List LocalSlot} {it : Gen.IntType} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    rvBits decls L it layouts rv = rvBits decls V it layouts rv := by
  have hop : ∀ op ∈ rvOperands rv, opBits L op = opBits V op :=
    fun op hop => opBits_frame op (h op hop)
  unfold rvBits
  split <;> simp_all [rvOperands]

theorem rvBits_frame {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {L V : List LocalSlot} {it : Gen.IntType} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    rvBits decls L it layouts (copyRv rv) = rvBits decls V it layouts (copyRv rv) :=
  rvBits_frame_raw h.of_copyRv

theorem rvBitsB_frame {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {L V : List LocalSlot} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    rvBitsB decls L (copyRv rv) layouts = rvBitsB decls V (copyRv rv) layouts := by
  have h' := h.copy
  rw [← rvOperands_copyRv] at h'
  generalize copyRv rv = rv' at h'
  unfold rvBitsB
  split <;> simp_all [rvOperands]

theorem rvBitsO_frame {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {L V : List LocalSlot} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    rvBitsO decls L (copyRv rv) layouts = rvBitsO decls V (copyRv rv) layouts := by
  have h' := h.copy
  rw [← rvOperands_copyRv] at h'
  generalize copyRv rv = rv' at h'
  unfold rvBitsO
  split <;> simp_all [rvOperands]

theorem rvTupleBits_frame {L V : List LocalSlot} {it : Gen.IntType} {rv : Rvalue}
    (h : ReadsAgree L V (rvOperands rv)) :
    rvTupleBits L it (copyRv rv) = rvTupleBits V it (copyRv rv) := by
  have h' := h.copy
  rw [← rvOperands_copyRv] at h'
  generalize copyRv rv = rv' at h'
  unfold rvTupleBits
  split <;> simp_all [rvOperands]

theorem specOpVal_frame {L V : List LocalSlot} (spec : TupleSpec) (op : Operand)
    (h : ∀ k ∈ opLocals op, L[k]? = V[k]?) :
    specOpVal L spec op = specOpVal V spec op := by
  cases spec with
  | scalar it => simp [specOpVal, opBits_frame op h]
  | tuple _ _ _ =>
    cases op with
    | copy p =>
      rcases p with ⟨j, projs⟩
      have hj : L[j]? = V[j]? := h j (local_mem_placeLocals ⟨j, projs⟩)
      simp [specOpVal, hj]
    | _ => rfl

theorem tupleFieldsOpsVal_frame {L V : List LocalSlot}
    (fields : List (Nat × TupleSpec)) (ops : List Operand)
    (h : ReadsAgree L V ops) :
    tupleFieldsOpsVal L fields ops = tupleFieldsOpsVal V fields ops := by
  induction fields generalizing ops with
  | nil => cases ops <;> rfl
  | cons f restF ih =>
    cases ops with
    | nil => rfl
    | cons op restOps =>
      obtain ⟨_, fSpec⟩ := f
      have hop := specOpVal_frame fSpec op (h op (by simp))
      have hrest := ih restOps (fun op' hop' => h op' (by simp [hop']))
      simp [tupleFieldsOpsVal, hop, hrest]

theorem tupleRvVal_frame {L V : List LocalSlot}
    (fields : List (Nat × TupleSpec)) (rv : Rvalue)
    (h : ReadsAgree L V (rvOperands rv)) :
    tupleRvVal L fields rv = tupleRvVal V fields rv := by
  match rv with
  | .use (.copy ⟨j, projs⟩) =>
    have hj : L[j]? = V[j]? :=
      h (.copy ⟨j, projs⟩) (by simp [rvOperands]) j (local_mem_placeLocals ⟨j, projs⟩)
    simp [tupleRvVal, hj]
  | .use (.move _) | .use (.constant _) => rfl
  | .aggregate .tuple ops =>
    have hops := tupleFieldsOpsVal_frame fields ops (by simpa [rvOperands] using h)
    simp [tupleRvVal, hops]
  | .aggregate (.adt _ 0 none) ops =>
    have hops := tupleFieldsOpsVal_frame fields ops (by simpa [rvOperands] using h)
    simp [tupleRvVal, hops]
  | .aggregate (.adt _ (.succ _) _) _ | .aggregate (.adt _ 0 (some _)) _
  | .aggregate (.array _) _ | .aggregate (.rawPtr _ _) _
  | .aggregate (.closure _) _ | .aggregate (.coroutine _) _
  | .repeat _ _ | .ref _ _ | .threadLocalRef _ | .rawPtr _ _ | .len _
  | .cast _ _ _ | .binaryOp _ _ _ | .nullaryOp _ _ | .unaryOp _ _
  | .discriminant _ | .shallowInitBox _ _ | .copyForDeref _ | .wrapUnsafeBinder _ _ => rfl

theorem arrayRvElems_frame {L V : List LocalSlot} (elemIt : Gen.IntType) (rv : Rvalue)
    (h : ReadsAgree L V (rvOperands rv)) :
    arrayRvElems L elemIt rv = arrayRvElems V elemIt rv := by
  match rv with
  | .use (.copy ⟨j, []⟩) =>
    have hj : L[j]? = V[j]? :=
      h (.copy ⟨j, []⟩) (by simp [rvOperands]) j (by simp [opLocals, placeLocals])
    simp [arrayRvElems, hj]
  | .use (.copy ⟨_, _ :: _⟩) | .use (.move _) | .use (.constant _) => rfl
  | .repeat op count =>
    have hop := opBits_frame op (h op (by simp [rvOperands]))
    simp [arrayRvElems, hop]
  | .aggregate (.array _) ops =>
    simp only [arrayRvElems]
    have key : ∀ (ops' : List Operand), ReadsAgree L V ops' →
        ops'.mapM (fun op => do let b ← opBits L op; pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) =
        ops'.mapM (fun op => do let b ← opBits V op; pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) := by
      intro ops' hops'
      induction ops' with
      | nil => rfl
      | cons op rest ih =>
        rw [List.mapM_cons, List.mapM_cons, opBits_frame op (hops' op (by simp)),
          ih (fun op' hop' => hops' op' (by simp [hop']))]
    exact key ops (by simpa [rvOperands] using h)
  | .aggregate .tuple _ | .aggregate (.adt _ _ _) _ | .aggregate (.rawPtr _ _) _
  | .aggregate (.closure _) _ | .aggregate (.coroutine _) _
  | .ref _ _ | .threadLocalRef _ | .rawPtr _ _ | .len _
  | .cast _ _ _ | .binaryOp _ _ _ | .nullaryOp _ _ | .unaryOp _ _
  | .discriminant _ | .shallowInitBox _ _ | .copyForDeref _ | .wrapUnsafeBinder _ _ => rfl

theorem NonScalarLive.opsInit {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body locals lm)
    (ops : List Operand) :
    OpsNonScalarInit body.localDecls locals ops := by
  intro op _ j _ d slot hd hs hnone hnp
  exact (hns j d slot hd hs hnone hnp).1

theorem NonScalarLive.opsInit_of_readsAgree {body : CapturedMir} {L V : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body V lm)
    {ops : List Operand} (hr : ReadsAgree L V ops) :
    OpsNonScalarInit body.localDecls L ops := by
  intro op hop j hj d slot hd hs hnone hnp
  rw [hr op hop j hj] at hs
  exact (hns j d slot hd hs hnone hnp).1

theorem OpsNonScalarInit.copy {decls : List LocalDecl} {locals : List LocalSlot}
    {rv : Rvalue} (h : OpsNonScalarInit decls locals (rvOperands rv)) :
    OpsNonScalarInit decls locals (rvOperands (copyRv rv)) := by
  intro op hop j hj d slot hd hs hnone hnp
  rw [rvOperands_copyRv] at hop
  obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
  rw [opLocals_copyOp] at hj
  exact h op0 hop0 j hj d slot hd hs hnone hnp

theorem stepMirFn_stmt (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (stmt : MirAst.Statement) (hcallee : s.memory.activeCallee = none)
    (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some stmt) :
    stepMirFn body s = evalStmt s stmt body.localDecls body.layouts := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hst]

theorem stepMirFn_term (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (hcallee : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlen : s.frame.stmtIdx = bb.statements.length) :
    stepMirFn body s = evalTerminator s bb.terminator (some body) := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hlen, length]

/-! ## Multi-frame `TerminatorKind.call` and `return_` evaluation -/

theorem stepMirFn_active_stmt (entry curBody : CapturedMir) (s : MachineState)
    (bb : BasicBlockData) (stmt : MirAst.Statement)
    (hcur : s.memory.activeCallee.getD entry = curBody)
    (hphase : curBody.phase = .runtimePostCleanup)
    (hbb : curBody.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some stmt) :
    stepMirFn entry s = evalStmt s stmt curBody.localDecls curBody.layouts := by
  simp [stepMirFn, hcur, hphase, get?, hbb, hst]

theorem stepMirFn_active_term (entry curBody : CapturedMir) (s : MachineState)
    (bb : BasicBlockData)
    (hcur : s.memory.activeCallee.getD entry = curBody)
    (hphase : curBody.phase = .runtimePostCleanup)
    (hbb : curBody.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlen : s.frame.stmtIdx = bb.statements.length) :
    stepMirFn entry s = evalTerminator s bb.terminator (some curBody) := by
  simp [stepMirFn, hcur, hphase, get?, hbb, hlen, length]

theorem extractCalleeDefPath?_of_extractFnDefPath {func : Operand} {dp : String}
    (h : extractFnDefPath func = some dp) :
    MirSemantics.extractCalleeDefPath? func = some dp := by
  cases func with
  | constant c =>
    simp only [extractFnDefPath] at h
    cases hk : c.ty.kind <;> simp_all [MirSemantics.extractCalleeDefPath?]
  | copy _ | move _ => simp [extractFnDefPath] at h

theorem SlotsOk.set_uninit {decls : List LocalDecl} {locals : List LocalSlot}
    (h : SlotsOk layouts decls locals) (j : Nat) :
    SlotsOk layouts decls (locals.set j .uninit) := by
  intro i d slot hd hs
  by_cases hij : i = j
  · subst hij
    have hilt : i < locals.length := by
      have hlen := (List.getElem?_eq_some_iff.mp hs).1
      rwa [List.length_set] at hlen
    rw [List.getElem?_set_self hilt, Option.some.injEq] at hs
    subst hs
    exact declSlotOk_uninit d layouts
  · rw [List.getElem?_set_ne (Ne.symm hij)] at hs
    exact h i d slot hd hs

/-- Evaluating a single fragment call argument `op` in Anneal's `evalOperand`:
agrees with `callArgVal`, updates `locals` by `opMoveLocal`, and preserves
`SlotsOk` while producing a `SlotOk (tyOf pd)` argument value. -/
theorem evalCallOperand_spec {decls : List LocalDecl} {locals : List LocalSlot}
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    {pd : LocalDecl} {op : Operand} {argExpr : Gen.ArgumentExpr}
    (hdecls : decls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hok : callArgOk layouts decls pd op = true) (htr : translateCallArg decls op = some argExpr)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (evalLayouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    (∀ v, callArgVal locals op = some v →
      evalOperand locals op borrows globals evalLayouts callerLocals =
        .ok v (opMoveLocal locals op) ∧
      SlotOk (tyOf pd) (.init v) ∧
      (opMoveLocal locals op).length = decls.length ∧
      SlotsOk layouts decls (opMoveLocal locals op)) ∧
    (callArgVal locals op = none →
      evalOperand locals op borrows globals evalLayouts callerLocals = .ub) := by
  rcases callArgOk_cases hdecls hok htr with
    ⟨j, hj, hsame⟩ | ⟨j, hj, hsame⟩ | ⟨j, fTy, it, hj, hpd, hfTy, htup⟩ |
      ⟨j, fTy, hj, hpd, hfTy, htup⟩ | ⟨c, sc, e, hc, hscOk, _⟩
  · have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨_, _, ⟨T, hT1, hT2⟩, _⟩ := sameFragmentTy_spec (hsame d hd)
    have hpdT : tyOf pd = T := tyOf_of_scalarTypeOf hT2
    have hs : locals[j]? = some locals[j] := List.getElem?_eq_getElem hjl
    have hslot : SlotOk T locals[j] := hslots.slotOk_scalar hd hs hT1
    unfold evalOperand
    simp only [callArgVal, opMoveLocal, opMoved, get?, hs]
    cases hsl : locals[j] with
    | dead => simp
    | uninit => simp
    | init v0 =>
      rw [hsl] at hslot
      refine ⟨fun v hv => ?_, fun hn' => by simp at hn'⟩
      simp at hv; subst hv
      exact ⟨by simp [readProjectedValue], hpdT ▸ hslot, hn, hslots⟩
  · have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨_, _, ⟨T, hT1, hT2⟩, _⟩ := sameFragmentTy_spec (hsame d hd)
    have hpdT : tyOf pd = T := tyOf_of_scalarTypeOf hT2
    have hs : locals[j]? = some locals[j] := List.getElem?_eq_getElem hjl
    have hslot : SlotOk T locals[j] := hslots.slotOk_scalar hd hs hT1
    unfold evalOperand
    simp only [callArgVal, opMoveLocal, opMoved, get?, hs]
    cases hsl : locals[j] with
    | dead => simp
    | uninit => simp
    | init v0 =>
      rw [hsl] at hslot
      refine ⟨fun v hv => ?_, fun hn' => by simp at hn'⟩
      simp at hv; subst hv
      exact ⟨by simp [set?, hjl], hpdT ▸ hslot, by simp [hn], hslots.set_uninit j⟩
  · have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    have hdTup := htup d hd
    have hpdTy : tyOf pd = .Int it := (tyOf_int hpd).1
    have hs : locals[j]? = some locals[j] := List.getElem?_eq_getElem hjl
    have hslot : SlotOk (intBoolTupleTy it) locals[j] :=
      hslots.slotOk_scalar hd hs (scalarTypeOf_tuple hdTup)
    unfold evalOperand
    simp only [callArgVal, opMoveLocal, opMoved, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .dead, _ => simp [hs]
    | .uninit, _ => simp [hs]
    | .init (.scalar _), ⟨_, hvb⟩ => simp [intBoolTupleTy, ValidBits] at hvb
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, hsz0, hb0, _, _⟩ =>
      simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
      subst htyT
      refine ⟨fun v hv => ?_, fun hn' => by simp [hs] at hn'⟩
      simp [hs] at hv; subst hv
      refine ⟨by simp [hs, readProjectedValue, get?], ?_, hn, hslots⟩
      rw [hpdTy]; exact ⟨hsz0, hb0⟩
  · have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨it, hdTup⟩ := htup d hd
    have hpdTy : tyOf pd = .Bool := (tyOf_bool hpd).1
    have hs : locals[j]? = some locals[j] := List.getElem?_eq_getElem hjl
    have hslot : SlotOk (intBoolTupleTy it) locals[j] :=
      hslots.slotOk_scalar hd hs (scalarTypeOf_tuple hdTup)
    unfold evalOperand
    simp only [callArgVal, opMoveLocal, opMoved, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .dead, _ => simp [hs]
    | .uninit, _ => simp [hs]
    | .init (.scalar _), ⟨_, hvb⟩ => simp [intBoolTupleTy, ValidBits] at hvb
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, _, _, _, hsz1, hb1⟩ =>
      refine ⟨fun v hv => ?_, fun hn' => by simp [hs] at hn'⟩
      simp [hs] at hv; subst hv
      refine ⟨by simp [hs, readProjectedValue, get?], ?_, hn, hslots⟩
      rw [hpdTy]; exact ⟨hsz1, hb1⟩
  · refine ⟨fun v hv => ?_, fun hn' => by simp [callArgVal, hc] at hn'⟩
    simp [callArgVal, hc] at hv; subst hv
    exact ⟨by simp [evalOperand, hc, evalConstValue, opMoveLocal, opMoved], hscOk, hn, hslots⟩

/-- Sequential left-to-right evaluation of call arguments in Anneal's
`evalOperands`: agrees with `callArgsEval` and preserves `SlotsOk`. -/
theorem evalCallOperands_spec {decls : List LocalDecl} {locals : List LocalSlot}
    (hslots : SlotsOk layouts decls locals) (hn : locals.length = decls.length)
    {paramDecls : List LocalDecl} {argOps : List Operand} {argExprs : List Gen.ArgumentExpr}
    (hdecls : decls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hargsOk : callArgsOk layouts decls paramDecls argOps = true)
    (htrArgs : argOps.mapM (translateCallArg decls) = some argExprs)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (evalLayouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    (∀ vs locals', callArgsEval locals argOps = some (vs, locals') →
      evalOperands locals argOps borrows globals evalLayouts callerLocals = .ok vs locals' ∧
      vs.length = paramDecls.length ∧
      (∀ (k : Nat) pd v, paramDecls[k]? = some pd → vs[k]? = some v → SlotOk (tyOf pd) (.init v)) ∧
      locals'.length = decls.length ∧
      SlotsOk layouts decls locals') ∧
    (callArgsEval locals argOps = none →
      evalOperands locals argOps borrows globals evalLayouts callerLocals = .ub) := by
  induction paramDecls generalizing locals argOps argExprs with
  | nil =>
    cases argOps with
    | nil =>
      refine ⟨fun vs locals' h => ?_, fun h => by simp [callArgsEval] at h⟩
      simp [callArgsEval] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, fun _ _ _ hk _ => by simp at hk, hn, hslots⟩
    | cons _ _ => simp [callArgsOk] at hargsOk
  | cons pd pds ih =>
    cases argOps with
    | nil => simp [callArgsOk] at hargsOk
    | cons op ops =>
      simp only [callArgsOk, Bool.and_eq_true] at hargsOk
      simp only [List.mapM_cons, Option.bind_eq_bind] at htrArgs
      cases htr1 : translateCallArg decls op with
      | none => simp [htr1] at htrArgs
      | some ae =>
        cases htrRest : ops.mapM (translateCallArg decls) with
        | none => simp [htr1, htrRest] at htrArgs
        | some aes =>
          obtain ⟨h1Ok, h1Ub⟩ := evalCallOperand_spec hslots hn hdecls hargsOk.1 htr1
            borrows globals evalLayouts callerLocals
          refine ⟨fun vs locals' hev => ?_, fun hnone => ?_⟩
          · simp only [callArgsEval, Option.bind_eq_bind] at hev
            cases hv1 : callArgVal locals op with
            | none => simp [hv1] at hev
            | some v1 =>
              obtain ⟨heval1, hv1Ok, hn1, hslots1⟩ := h1Ok v1 hv1
              obtain ⟨ihOk, _⟩ := ih hslots1 hn1 hargsOk.2 htrRest
              cases hrest : callArgsEval (opMoveLocal locals op) ops with
              | none => simp [hv1, hrest] at hev
              | some p =>
                obtain ⟨vsRest, locals2⟩ := p
                simp [hv1, hrest] at hev
                obtain ⟨rfl, rfl⟩ := hev
                obtain ⟨hevalRest, hvslen, hvsOk, hn2, hslots2⟩ := ihOk vsRest locals2 hrest
                refine ⟨by simp [evalOperands, heval1, hevalRest], by simp [hvslen], ?_, hn2, hslots2⟩
                intro k pd' v' hpd' hv'
                cases k with
                | zero => simp at hpd' hv'; subst hpd' hv'; exact hv1Ok
                | succ k => simp at hpd' hv'; exact hvsOk k pd' v' hpd' hv'
          · simp only [callArgsEval, Option.bind_eq_bind] at hnone
            cases hv1 : callArgVal locals op with
            | none => simp [evalOperands, h1Ub hv1]
            | some v1 =>
              obtain ⟨heval1, _, hn1, hslots1⟩ := h1Ok v1 hv1
              obtain ⟨_, ihUb⟩ := ih hslots1 hn1 hargsOk.2 htrRest
              cases hrest : callArgsEval (opMoveLocal locals op) ops with
              | none => simp [evalOperands, heval1, ihUb hrest]
              | some p => cases p; simp [hv1, hrest] at hnone

/-- Writing `retVal` to a fragment call destination under `CallerDestRel` in
Anneal's `writePlaceValue` always succeeds with `writeCallDest`. -/
theorem writePlaceValue_callDest {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation} {calleeRetPtr : Ptr}
    {destination : Place}
    (hdest : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination)
    (borrows : List BorrowEntry) (retVal : Value) :
    MirSemantics.writePlaceValue callerActual borrows destination retVal =
      .ok (writeCallDest callerActual destination retVal) := by
  cases hdest with
  | root dst dDst callerSlot hActual hLive _ _ _ _ _ =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    have hActElem : callerActual[dst]'hlt = callerSlot := by
      simpa [List.getElem?_eq_getElem hlt] using hActual
    cases callerSlot with
    | dead => exact absurd rfl hLive
    | uninit => simp [writePlaceValue, writeCallDest, get?, set?, hlt, hActElem]
    | init v0 => simp [writePlaceValue, writeCallDest, get?, set?, hlt, hActElem]
  | field0 dst fTy dDst it sc0 sc1 allocPre idDst hActual _ _ _ _ _ _ _ _ _ _ _ =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    have hActElem : callerActual[dst]'hlt = .init (.aggregate 0 [.scalar sc0, .scalar sc1]) := by
      simpa [List.getElem?_eq_getElem hlt] using hActual
    simp [writePlaceValue, writeProjectedValue, writeCallDest, get?, set?, hlt, hActElem]
  | field1 dst fTy dDst it sc0 sc1 allocPre pDst idDst hActual _ _ _ _ _ _ _ _ _ _ _ _ =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    have hActElem : callerActual[dst]'hlt = .init (.aggregate 0 [.scalar sc0, .scalar sc1]) := by
      simpa [List.getElem?_eq_getElem hlt] using hActual
    simp [writePlaceValue, writeProjectedValue, writeCallDest, get?, set?, hlt, hActElem]

/-- Anneal's `evalTerminator` on a direct intra-program `TerminatorKind.call`
either raises UB when argument evaluation fails, or pushes a `SavedCallerFrame`
and enters `calleeBody` at `(0, 0)` with `initLocals calleeBody argVals`. -/
theorem evalTerminator_call_anneal {s : MachineState} {callerBody calleeBody : CapturedMir}
    {func : Operand} {argOps : List Operand} {destination : Place}
    {targetBb : Nat} {unwind : UnwindAction} {span : String} {dp : String}
    {paramDecls : List LocalDecl} {argExprs : List Gen.ArgumentExpr}
    (hextr : extractFnDefPath func = some dp)
    (hfind : MirSemantics.findCallee? s.memory.callees dp = some calleeBody)
    (hslots : SlotsOk callerBody.layouts callerBody.localDecls s.frame.locals)
    (hn : s.frame.locals.length = callerBody.localDecls.length)
    (hdecls : callerBody.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hargsOk : callArgsOk callerBody.layouts callerBody.localDecls paramDecls argOps = true)
    (htrArgs : argOps.mapM (translateCallArg callerBody.localDecls) = some argExprs) :
    (∀ argVals locals', callArgsEval s.frame.locals argOps = some (argVals, locals') →
      MirSemantics.evalTerminator s ⟨.call func argOps destination (some targetBb) unwind, span⟩
          (some callerBody) =
        .tau (.running {
          frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals }
          memory := {
            s.memory with
            callStack := {
              callerBody := callerBody
              frame := { s.frame with locals := locals' }
              destination := destination
              returnTarget := targetBb
              calleeProtectors := s.memory.activeProtectors
            } :: s.memory.callStack
            activeCallee := some calleeBody
          }
        }) ∧
      argVals.length = paramDecls.length ∧
      (∀ (k : Nat) pd v, paramDecls[k]? = some pd → argVals[k]? = some v → SlotOk (tyOf pd) (.init v)) ∧
      locals'.length = callerBody.localDecls.length ∧
      SlotsOk callerBody.layouts callerBody.localDecls locals') ∧
    (callArgsEval s.frame.locals argOps = none →
      MirSemantics.evalTerminator s ⟨.call func argOps destination (some targetBb) unwind, span⟩
        (some callerBody) = MirStepNode.fail .ub) := by
  have hextr' := extractCalleeDefPath?_of_extractFnDefPath hextr
  obtain ⟨hOk, hUb⟩ := evalCallOperands_spec hslots hn hdecls hargsOk htrArgs
    s.memory.borrows s.memory.globals callerBody.layouts s.memory.callerLocals
  refine ⟨fun argVals locals' hev => ?_, fun hnone => ?_⟩
  · obtain ⟨heval, hvslen, hvsOk, hlen, hslots'⟩ := hOk argVals locals' hev
    exact ⟨by simp [MirSemantics.evalTerminator, hextr', heval, hfind, MirStepNode.step],
      hvslen, hvsOk, hlen, hslots'⟩
  · simp [MirSemantics.evalTerminator, hextr', hUb hnone]

/-- Anneal's `evalTerminator` on `TerminatorKind.return_` from a non-root callee
frame (`s.memory.callStack = savedCaller :: restStack`) under `CallerDestRel`:
either `_0` is uninitialized/dead/missing and `evalTerminator` raises UB, or
`_0` holds `retVal` and execution resumes `savedCaller` at `returnTarget, 0`
with `writeCallDest`. -/
theorem evalTerminator_return_caller_anneal {s : MachineState} {curBody callerBody : CapturedMir}
    {savedCaller : SavedCallerFrame} {restStack : List SavedCallerFrame} {span : String}
    {callerCtx : Ctx} {callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation} {calleeRetPtr : Ptr}
    (hstack : s.memory.callStack = savedCaller :: restStack)
    (hprotNone : savedCaller.callerProtector = none)
    (hcalleeProts : savedCaller.calleeProtectors = [])
    (hdest : CallerDestRel callerBody callerCtx savedCaller.frame.locals callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr savedCaller.destination) :
    (∀ retVal, s.frame.locals[0]? = some (.init retVal) →
      MirSemantics.evalTerminator s ⟨.return_, span⟩ (some curBody) =
        .tau (.running {
          frame := {
            savedCaller.frame with
            blockIdx := savedCaller.returnTarget
            stmtIdx := 0
            locals := writeCallDest savedCaller.frame.locals savedCaller.destination retVal
          }
          memory := {
            s.memory with
            callStack := restStack
            activeCallee := some savedCaller.callerBody
            activeProtectors := []
          }
        })) ∧
    ((s.frame.locals[0]? = some .uninit ∨ s.frame.locals[0]? = some .dead ∨
        s.frame.locals[0]? = none) →
      MirSemantics.evalTerminator s ⟨.return_, span⟩ (some curBody) = MirStepNode.fail .ub) := by
  refine ⟨fun retVal h0 => ?_, fun hub => ?_⟩
  · have hw := writePlaceValue_callDest hdest s.memory.borrows retVal
    simp [MirSemantics.evalTerminator, get?, h0, hstack, hw, hprotNone, hcalleeProts, MirStepNode.step]
  · rcases hub with h | h | h <;> simp [MirSemantics.evalTerminator, get?, h]

/-- Anneal's `evalStmt` on `StatementKind.intrinsic (.assume op)`: evaluates `op`
(moving out on `move _j`), raising UB if `op` is uninitialized or `false` (`0`)
and advancing to `stmtIdx + 1` with `opPost s.frame.locals op` when `op` is
`true` (`1`). -/
theorem evalStmt_assume_anneal (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (op : Operand) (span : String)
    (hslots : SlotsOk layouts decls s.frame.locals) (hn : s.frame.locals.length = decls.length)
    (hsimple : simpleOp op = true) (hokB : operandOkB layouts decls (copyOp op) = true) :
    (opBits s.frame.locals (copyOp op) = none →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (opBits s.frame.locals (copyOp op) = some 0 →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (opBits s.frame.locals (copyOp op) = some 1 →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ decls layouts =
        MirStepNode.step (advanceStmt s (opPost s.frame.locals op))) := by
  obtain ⟨hAok, hAnone⟩ := evalOperand_fragT decls s.frame.locals hslots hn
    (.bool : FragTy .Bool u8Ty) (copyOp op) (operandOkB_T hokB)
    s.memory.borrows s.memory.globals s.memory.callerLocals
  have hmove := evalOperand_move s.frame.locals op hsimple
    s.memory.borrows s.memory.globals layouts s.memory.callerLocals
  refine ⟨fun hnone => ?_, fun h0 => ?_, fun h1 => ?_⟩
  · simp [evalStmt, hmove, hAnone hnone, opWithLocals]
  · simp [evalStmt, hmove, hAok 0 h0, opWithLocals, u8Ty]
  · simp [evalStmt, hmove, hAok 1 h1, opWithLocals, u8Ty]

end MiniRustSpec.Correspondence
