/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.PlaceAndRvalue
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Trusted.Rustc.V2026_08_01.MirSemantics.Places

/-!
# Unions — Offset-0 Field Decoding, `kani#5159` 0-Byte Field Reads, and `kani#5176` `[(); N]` Arms

Extracted from `Anneal.Mir.AdtAndControl` Section 6 (`namespace Anneal.Mir.AdtAndControl.UnionZst`)
so every theorem is public and independently audited under `Anneal.*`, while keeping
`AdtAndControl.lean` focused and `<3,500`-LOC modular.

Stated and proved directly against `Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValueUnionAware`
(with 5-constructor `Value` including `Value.uninit`) and mirrored on
`Trusted.Rustc.V2026_08_01.MirSemantics.readProjectedValueUnionAware` in Section 6f:
- Every union field sits at offset `0`, and a field read reinterprets the union's storage at the
  field's type (`readUnion_posField_offset0`, `decodeUnionBytes_roundtrip`,
  `readDecodedUnion_posField_offset0`, `readDecodedUnion_trailing_bytes_ignored`).
- Loading a value of an **uninhabited leaf** (`tyIsUninhabited layouts leafTy = true`, or
  `tyIsUninhabited layouts rFieldTy = true` at the field root `rest = .nil`) faults with `.ub`
  (`kani#5159`), regardless of whether the uninhabited leaf is 0-byte, positive-sized, or lacks a
  byte size in `tyByteSize` (`readUnion_zeroByte_root`, `readUnion_unsized_root`,
  `kani5159_uninhabited_field_root_ub`, `kani5159_uninhabited_subProj_ub`).
- Reading an **inhabited leaf** through an uninhabited intermediate container
  (`tyIsUninhabited layouts leafTy = false`, while `tyIsUninhabited layouts rFieldTy = true` or
  `subProjTouchesUninhabited ... = true`; or a non-empty `rest = _ :: _` fallthrough when
  `tyIsUninhabited layouts rFieldTy = true`) fails closed with **`.unsupported`** (never `.ub`),
  matching Miri/MiniRust's offset-only place projection semantics and `crates/anneal-mir`'s
  `MirLowerError::InactiveUnionField` (`readUnion_zeroByte_subProj`, `readUnion_zeroByte_subProj_iff`,
  `kani5159_inhabitedLeaf_through_uninhabitedContainer_subProj_unsupported`,
  `readUnion_posLeaf_subProj`, `readUnion_zeroByte_fieldRoot`,
  `readUnion_uninhabited_nonEmpty_fallthrough_unsupported`, with non-vacuity witnesses on every
  `tyByteSize rFieldTy` arm in `kani5159_witness_nonStatic_fallthrough`,
  `kani5159_v2026_08_01_nonStatic_fallthrough_parity`, and
  `kani5159_v2026_08_01_nonEmpty_fallthrough_parity`).
- A 0-byte field or sub-place occupies no storage, so an inhabited one not passing through an
  uninhabited container reads its unique value even from all-`.uninit` storage (`kani#5176`:
  `kani5176_uninit_storage_zst_field`, `kani5176_uninit_storage_zst_subProj`,
  `kani5176_uninit_storage_int_field_ub`).
-/

namespace Anneal.Mir.AdtAndControl.UnionZst

section V2026_06_01

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Section 6a: The union field read, `Value.uninit` invariants, and gates -/

/-- `takeAbstractBytes` equals `List.take`. -/
theorem takeAbstractBytes_eq_take :
    ∀ (n : Nat) (bs : List AbstractByte), takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: bs => by
    simp only [takeAbstractBytes, List.take_succ_cons, takeAbstractBytes_eq_take n bs]

/-- `dropAbstractBytes` equals `List.drop`. -/
theorem dropAbstractBytes_eq_drop :
    ∀ (n : Nat) (bs : List AbstractByte), dropAbstractBytes n bs = bs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: bs => by
    simp only [dropAbstractBytes, List.drop_succ_cons, dropAbstractBytes_eq_drop n bs]

/-- `replicateUninitBytes` equals `List.replicate _ .uninit`. -/
theorem replicateUninitBytes_eq_replicate :
    ∀ n : Nat, replicateUninitBytes n = List.replicate n AbstractByte.uninit
  | 0 => rfl
  | n + 1 => by
    simp only [replicateUninitBytes, List.replicate_succ, replicateUninitBytes_eq_replicate n]

/-- `replicateUninitBytes n` has length `n`. -/
theorem length_replicateUninitBytes (n : Nat) : (replicateUninitBytes n).length = n := by
  rw [replicateUninitBytes_eq_replicate, List.length_replicate]

/-- `replicateValue count .unit` contains no `Value.uninit`. -/
theorem valueListContainsUninit_replicateValue_unit :
    ∀ count : Nat, valueListContainsUninit (replicateValue count .unit) = false
  | 0 => rfl
  | k + 1 => by
    simp only [replicateValue, valueListContainsUninit_replicateValue_unit k]

/-- `encodeRawAbstractByteVals` emits only `.scalar` and `.aggregate` values (never `Value.uninit`). -/
theorem valueListContainsUninit_encodeRawAbstractByteVals :
    ∀ bs : List AbstractByte, valueListContainsUninit (encodeRawAbstractByteVals bs) = false
  | [] => rfl
  | .uninit :: rest => by
    simp only [encodeRawAbstractByteVals, valueListContainsUninit_encodeRawAbstractByteVals rest]
  | .init _ none :: rest => by
    simp only [encodeRawAbstractByteVals, valueListContainsUninit_encodeRawAbstractByteVals rest]
  | .init _ (some _) :: rest => by
    simp only [encodeRawAbstractByteVals, valueListContainsUninit_encodeRawAbstractByteVals rest]

/-- `appendValueList` preserves `valueListContainsUninit = false`. -/
theorem valueListContainsUninit_appendValueList :
    ∀ (xs ys : List Value),
      valueListContainsUninit xs = false →
      valueListContainsUninit ys = false →
      valueListContainsUninit (appendValueList xs ys) = false
  | [], ys, _, hys => hys
  | x :: xs, ys, hxs, hys => by
    simp only [valueListContainsUninit] at hxs
    cases hx : valueContainsUninit x with
    | true => rw [hx] at hxs; nomatch hxs
    | false =>
      rw [hx] at hxs
      simp only [valueListContainsUninit, hx,
        valueListContainsUninit_appendValueList xs ys hxs hys]

/-- `forceValueListOpt` is the identity on value lists (it only forces the spine). -/
theorem forceValueListOpt_eq : ∀ l : List Value, forceValueListOpt l = some l
  | [] => rfl
  | v :: vs => by simp only [forceValueListOpt, forceValueListOpt_eq vs]

/-- `decodeArrayChunksWith` preserves `valueContainsUninit = false`. -/
theorem valueListContainsUninit_decodeArrayChunksWith
    (f : List AbstractByte → Option Value)
    (hf : ∀ bs v, f bs = some v → valueContainsUninit v = false)
    (stride : Nat) :
    ∀ (n : Nat) (bs : List AbstractByte) (vs : List Value),
      decodeArrayChunksWith f stride n bs = some vs →
      valueListContainsUninit vs = false
  | 0, [], _, h => by
    unfold decodeArrayChunksWith at h
    cases h
    rfl
  | 0, _ :: _, _, h => by
    unfold decodeArrayChunksWith at h
    nomatch h
  | k + 1, bs, vs, h => by
    unfold decodeArrayChunksWith at h
    cases hB : Nat.ble stride (length bs) with
    | false => rw [hB] at h; nomatch h
    | true =>
      rw [hB] at h; dsimp only at h
      cases h1 : f (takeAbstractBytes stride bs) with
      | none => rw [h1] at h; nomatch h
      | some v =>
        rw [h1] at h; dsimp only at h
        cases h2 : decodeArrayChunksWith f stride k (dropAbstractBytes stride bs) with
        | none => rw [h2] at h; nomatch h
        | some rest =>
          rw [h2] at h; cases h
          simp only [valueListContainsUninit, hf _ _ h1,
            valueListContainsUninit_decodeArrayChunksWith f hf stride k _ _ h2]

/-- `decodeTypedKindsAndLayoutsAtOffsets` preserves `valueContainsUninit = false`. -/
theorem valueListContainsUninit_decodeTypedKindsAndLayoutsAtOffsets
    (f : Ty → List AbstractByte → Option Value)
    (hf : ∀ ty bs v, f ty bs = some v → valueContainsUninit v = false)
    (layouts : LayoutTable) (bs : List AbstractByte) :
    ∀ (offs : List Size) (ks : List RigidTy) (fls : List Nat) (vs : List Value),
      decodeTypedKindsAndLayoutsAtOffsets f layouts bs offs ks fls = some vs →
      valueListContainsUninit vs = false
  | [], [], [], _, h => by cases h; rfl
  | off :: offs, k :: ks, fl :: fls, vs, h => by
    unfold decodeTypedKindsAndLayoutsAtOffsets at h
    cases hL : LayoutTable.lookup layouts fl with
    | none => rw [hL] at h; nomatch h
    | some l =>
      rw [hL] at h; dsimp only at h
      cases hS : sliceAbstractBytes bs off.bytes l.size.bytes with
      | none => rw [hS] at h; nomatch h
      | some fSlice =>
        rw [hS] at h; dsimp only at h
        cases h1 : f { kind := k, layoutIdx := fl } fSlice with
        | none => rw [h1] at h; nomatch h
        | some v =>
          rw [h1] at h; dsimp only at h
          cases h2 : decodeTypedKindsAndLayoutsAtOffsets f layouts bs offs ks fls with
          | none => rw [h2] at h; nomatch h
          | some rest =>
            rw [h2] at h; cases h
            simp only [valueListContainsUninit, hf _ _ _ h1,
              valueListContainsUninit_decodeTypedKindsAndLayoutsAtOffsets f hf layouts bs offs ks fls _ h2]
  | [], _ :: _, _, _, h | [], [], _ :: _, _, h | _ :: _, [], _, _, h | _ :: _, _ :: _, [], _, h => by
    nomatch h

/-- `decodeFieldsAtOffsetsWith` preserves `valueContainsUninit = false`. -/
theorem valueListContainsUninit_decodeFieldsAtOffsetsWith
    (f : RigidTy → List AbstractByte → Option Value)
    (hf : ∀ k bs v, f k bs = some v → valueContainsUninit v = false)
    (szOf : RigidTy → Option Nat) (bs : List AbstractByte) :
    ∀ (offs : List Size) (ks : List RigidTy) (vs : List Value),
      decodeFieldsAtOffsetsWith f szOf bs offs ks = some vs →
      valueListContainsUninit vs = false
  | [], [], _, h => by cases h; rfl
  | off :: offs, k :: ks, vs, h => by
    unfold decodeFieldsAtOffsetsWith at h
    cases hSz : szOf k with
    | none => rw [hSz] at h; nomatch h
    | some sz =>
      rw [hSz] at h; dsimp only at h
      cases hS : sliceAbstractBytes bs off.bytes sz with
      | none => rw [hS] at h; nomatch h
      | some fSlice =>
        rw [hS] at h; dsimp only at h
        cases h1 : f k fSlice with
        | none => rw [h1] at h; nomatch h
        | some v =>
          rw [h1] at h; dsimp only at h
          cases h2 : decodeFieldsAtOffsetsWith f szOf bs offs ks with
          | none => rw [h2] at h; nomatch h
          | some rest =>
            rw [h2] at h; cases h
            simp only [valueListContainsUninit, hf _ _ _ h1,
              valueListContainsUninit_decodeFieldsAtOffsetsWith f hf szOf bs offs ks _ h2]
  | [], _ :: _, _, h | _ :: _, [], _, h => by nomatch h

/-- `decodeSeqFieldsWith` preserves `valueContainsUninit = false`. -/
theorem valueListContainsUninit_decodeSeqFieldsWith
    (f : RigidTy → List AbstractByte → Option Value)
    (hf : ∀ k bs v, f k bs = some v → valueContainsUninit v = false)
    (szOf : RigidTy → Option Nat) :
    ∀ (ks : List RigidTy) (bs : List AbstractByte) (vs : List Value),
      decodeSeqFieldsWith f szOf ks bs = some vs →
      valueListContainsUninit vs = false
  | [], bs, _, h => by
    unfold decodeSeqFieldsWith at h
    cases bs <;> cases h; rfl
  | k :: ks, bs, vs, h => by
    unfold decodeSeqFieldsWith at h
    cases hSz : szOf k with
    | none => rw [hSz] at h; nomatch h
    | some sz =>
      rw [hSz] at h; dsimp only at h
      cases hB : Nat.ble sz (length bs) with
      | false => rw [hB] at h; nomatch h
      | true =>
        rw [hB] at h; dsimp only at h
        cases h1 : f k (takeAbstractBytes sz bs) with
        | none => rw [h1] at h; nomatch h
        | some v =>
          rw [h1] at h; dsimp only at h
          cases h2 : decodeSeqFieldsWith f szOf ks (dropAbstractBytes sz bs) with
          | none => rw [h2] at h; nomatch h
          | some rest =>
            rw [h2] at h; cases h
            simp only [valueListContainsUninit, hf _ _ _ h1,
              valueListContainsUninit_decodeSeqFieldsWith f hf szOf ks _ _ h2]

/-- `decodeFieldsByLayoutIdxs` preserves `valueContainsUninit = false`. -/
theorem valueListContainsUninit_decodeFieldsByLayoutIdxs
    (f : Nat → List AbstractByte → Option Value)
    (hf : ∀ fl bs v, f fl bs = some v → valueContainsUninit v = false)
    (layouts : LayoutTable) (bs : List AbstractByte) :
    ∀ (offs : List Size) (fls : List Nat) (vs : List Value),
      decodeFieldsByLayoutIdxs f layouts bs offs fls = some vs →
      valueListContainsUninit vs = false
  | [], [], _, h => by cases h; rfl
  | off :: offs, fl :: fls, vs, h => by
    unfold decodeFieldsByLayoutIdxs at h
    cases hL : LayoutTable.lookup layouts fl with
    | none => rw [hL] at h; nomatch h
    | some l =>
      rw [hL] at h; dsimp only at h
      cases hS : sliceAbstractBytes bs off.bytes l.size.bytes with
      | none => rw [hS] at h; nomatch h
      | some fSlice =>
        rw [hS] at h; dsimp only at h
        cases h1 : f fl fSlice with
        | none => rw [h1] at h; nomatch h
        | some v =>
          rw [h1] at h; dsimp only at h
          cases h2 : decodeFieldsByLayoutIdxs f layouts bs offs fls with
          | none => rw [h2] at h; nomatch h
          | some rest =>
            rw [h2] at h; cases h
            simp only [valueListContainsUninit, hf _ _ _ h1,
              valueListContainsUninit_decodeFieldsByLayoutIdxs f hf layouts bs offs fls _ h2]
  | [], _ :: _, _, h | _ :: _, [], _, h => by nomatch h

/-- `decodeFieldsBySpan` only constructs `.scalar` or `.unit` field values (never `Value.uninit`). -/
theorem valueListContainsUninit_decodeFieldsBySpan (bs : List AbstractByte) (totalSz : Nat) :
    ∀ (offs : List Size) (vs : List Value),
      decodeFieldsBySpan bs totalSz offs = some vs →
      valueListContainsUninit vs = false
  | [], _, h => by cases h; rfl
  | off :: offs, vs, h => by
    unfold decodeFieldsBySpan at h
    dsimp at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i v hFVal
          split at h
          · rename_i rest hRest
            cases h
            have hV : valueContainsUninit v = false := by
              repeat (first | contradiction | (cases hFVal; rfl) | split at hFVal)
            simp only [valueListContainsUninit, hV,
              valueListContainsUninit_decodeFieldsBySpan bs totalSz offs rest hRest]
          · cases h

/-- `decodeScalarLayoutBytes` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodeScalarLayoutBytes (sl : ScalarLayout) (bs : List AbstractByte) (v : Value)
    (h : decodeScalarLayoutBytes sl bs = some v) :
    valueContainsUninit v = false := by
  unfold decodeScalarLayoutBytes at h
  cases sl <;> simp only [] at h <;>
    repeat (first | contradiction | (cases h; rfl) | split at h)

/-- `decodeScalarLayoutBytesNoForge` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodeScalarLayoutBytesNoForge (sl : ScalarLayout) (bs : List AbstractByte)
    (v : Value) (h : decodeScalarLayoutBytesNoForge sl bs = some v) :
    valueContainsUninit v = false := by
  unfold decodeScalarLayoutBytesNoForge at h
  repeat (first | contradiction | (cases h; rfl) | split at h)

/-- `decodePtrBytesNoForge` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodePtrBytesNoForge (isRef : Bool) (pointee : RigidTy) (ptrBytes : Nat)
    (bs : List AbstractByte) (v : Value) (h : decodePtrBytesNoForge isRef pointee ptrBytes bs = some v) :
    valueContainsUninit v = false := by
  unfold decodePtrBytesNoForge at h
  dsimp at h
  split at h
  · repeat (first | contradiction | (cases h; rfl) | split at h)
  · split at h
    · cases h
    · split at h
      · rename_i dataVal metaVal hData hMeta
        cases h
        have hD : valueContainsUninit dataVal = false := by
          repeat (first | contradiction | (cases hData; rfl) | split at hData)
        have hM : valueContainsUninit metaVal = false := by
          repeat (first | contradiction | (cases hMeta; rfl) | split at hMeta)
        simp only [valueContainsUninit, valueListContainsUninit, hD, hM]
      · cases h

/-- `decodeUnionBytesWithCountOpt` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodeUnionBytesWithCountOpt (layouts : LayoutTable) (layoutIdx count : Nat)
    (bs : List AbstractByte) (v : Value)
    (h : decodeUnionBytesWithCountOpt layouts layoutIdx count bs = some v) :
    valueContainsUninit v = false := by
  unfold decodeUnionBytesWithCountOpt finalizeUnionFieldsWithRawOverlayOpt at h
  dsimp only at h
  cases hEnc : encodeByLayoutIdxAux 8 layouts layoutIdx (.aggregate 0 (replicateValue count .unit)) with
  | none =>
    rw [hEnc] at h
    simp only [forceValueListOpt_eq] at h
    cases h
    simp only [valueContainsUninit]
    exact valueListContainsUninit_appendValueList _ _
      (valueListContainsUninit_replicateValue_unit count)
      (by simp only [valueListContainsUninit, valueContainsUninit,
            valueListContainsUninit_encodeRawAbstractByteVals])
  | some cur =>
    rw [hEnc] at h
    dsimp only at h
    cases hEq : abstractByteListEq cur bs with
    | true =>
      rw [hEq] at h
      simp only [forceValueListOpt_eq] at h
      cases h
      exact valueListContainsUninit_replicateValue_unit count
    | false =>
      rw [hEq] at h
      simp only [forceValueListOpt_eq] at h
      cases h
      simp only [valueContainsUninit]
      exact valueListContainsUninit_appendValueList _ _
        (valueListContainsUninit_replicateValue_unit count)
        (by simp only [valueListContainsUninit, valueContainsUninit,
              valueListContainsUninit_encodeRawAbstractByteVals])

/-- `replicateValue n v` never contains `Value.uninit` when `v` does not. -/
theorem valueListContainsUninit_replicateValue (n : Nat) (v : Value)
    (hv : valueContainsUninit v = false) :
    valueListContainsUninit (replicateValue n v) = false := by
  induction n with
  | zero => rfl
  | succ n' ih => simp only [replicateValue, valueListContainsUninit, hv, ih]

/-- `decodeUnionFieldsByLayoutIdxs` never produces `Value.uninit` when `decodeByLayout` and
`payloadVal` do not. -/
theorem valueListContainsUninit_decodeUnionFieldsByLayoutIdxs
    (f : Nat → List AbstractByte → Option Value)
    (hf : ∀ fl bs v, f fl bs = some v → valueContainsUninit v = false)
    (layouts : LayoutTable) (bs : List AbstractByte) (totalSz : Nat)
    (payloadVal : Value) (hp : valueContainsUninit payloadVal = false) :
    ∀ fls : List Nat,
      valueListContainsUninit (decodeUnionFieldsByLayoutIdxs f layouts bs totalSz payloadVal fls) = false
  | [] => rfl
  | fIdx :: fRest => by
    unfold decodeUnionFieldsByLayoutIdxs
    dsimp only
    have ih := valueListContainsUninit_decodeUnionFieldsByLayoutIdxs f hf layouts bs totalSz payloadVal hp fRest
    rw [valueListContainsUninit]
    suffices hHead : valueContainsUninit _ = false by rw [hHead]; exact ih
    split
    · exact hp
    · split
      · rfl
      · split
        · split
          · split
            · exact hf _ _ _ ‹_›
            · rfl
          · exact hp
        · split
          · rfl
          · split
            · exact hf _ _ _ ‹_›
            · split <;> rfl

/-- `decodeValueFromBytes` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodeValueFromBytes :
    ∀ (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte) (v : Value),
      decodeValueFromBytes fuel layouts ty bs = some v →
      valueContainsUninit v = false
  | 0, _, _, _, _, h => by cases h
  | fuel' + 1, layouts, ty, bs, v, h => by
    unfold decodeValueFromBytes at h
    have ih : ∀ ty' bs' v', decodeValueFromBytes fuel' layouts ty' bs' = some v' →
        valueContainsUninit v' = false :=
      valueContainsUninit_decodeValueFromBytes fuel' layouts
    cases hk : ty.kind with
    | bool | char | uint _ | int _ | float _ | rawPtr _ _ | ref _ _ | fnPtr _ _ _ _ | fnDef _ _
    | never | str | slice _ | dynamic _ | param _ | alias _ _ | foreign _ | other _ =>
      rw [hk] at h; dsimp at h
      repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
    | tuple ks =>
      cases ks with
      | nil =>
        rw [hk] at h; dsimp at h
        repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
      | cons kHead kTail =>
        rw [hk] at h; dsimp at h
        repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
        all_goals
          (cases h
           simp only [valueContainsUninit]
           try
             (first
              | rfl
              | exact valueListContainsUninit_decodeFieldsAtOffsetsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ ‹_›
              | exact valueListContainsUninit_decodeSeqFieldsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›))
    | array elemKind n =>
      rw [hk] at h; dsimp at h
      repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
      all_goals
        (cases h
         simp only [valueContainsUninit]
         try
           (first
            | rfl
            | exact valueListContainsUninit_decodeArrayChunksWith _ (fun bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›))
    | adt _ _ =>
      rw [hk] at h; dsimp at h
      repeat'
        (first
         | contradiction
         | (cases h; rfl)
         | exact valueContainsUninit_decodeScalarLayoutBytes _ _ _ h
         | split at h
         | dsimp at h)
      all_goals
        (cases h
         first
         | exact valueContainsUninit_decodeScalarLayoutBytes _ _ _ ‹_›
         | (simp only [valueContainsUninit]
            try
              (first
               | rfl
               | exact valueListContainsUninit_replicateValue _ _ rfl
               | exact valueListContainsUninit_replicateValue _ _ (valueContainsUninit_decodeScalarLayoutBytes _ _ _ ‹_›)
               | exact valueListContainsUninit_decodeFieldsBySpan _ _ _ _ ‹_›
               | exact valueListContainsUninit_decodeArrayChunksWith _ (fun bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›
               | exact valueListContainsUninit_decodeArrayChunksWith
                   (fun chunk => match decodeScalarBytes chunk false with | some (sv, _) => some (.scalar sv) | none => none)
                   (fun bs' v' hv => by cases hsc : decodeScalarBytes bs' false <;> rw [hsc] at hv <;> cases hv; rfl)
                   _ _ _ _ ‹_›
               | exact valueListContainsUninit_decodeFieldsByLayoutIdxs _ (fun fl bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ ‹_›
               | exact valueListContainsUninit_decodeUnionFieldsByLayoutIdxs _ (fun fl bs' v' hv => ih _ bs' v' hv) _ _ _ _ rfl _
               | exact valueListContainsUninit_decodeUnionFieldsByLayoutIdxs _ (fun fl bs' v' hv => ih _ bs' v' hv) _ _ _ _ (valueContainsUninit_decodeScalarLayoutBytes _ _ _ ‹_›) _
               | (rename_i h1 h2; simp only [valueListContainsUninit,
                    valueContainsUninit_decodeScalarLayoutBytes _ _ _ h1,
                    valueContainsUninit_decodeScalarLayoutBytes _ _ _ h2]; done)
               | (rename_i h1; simp only [valueListContainsUninit,
                    valueContainsUninit_decodeScalarLayoutBytes _ _ _ h1]; done)
               | (rename_i hMatch
                  split at hMatch <;> try contradiction
                  first
                  | exact valueListContainsUninit_decodeFieldsAtOffsetsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ hMatch
                  | exact valueListContainsUninit_replicateValue _ _ (ih _ _ _ hMatch)
                  | exact valueListContainsUninit_decodeUnionFieldsByLayoutIdxs _ (fun fl bs' v' hv => ih _ bs' v' hv) _ _ _ _ (ih _ _ _ hMatch) _
                  | (simp only [valueListContainsUninit, ih _ _ _ hMatch]; done)))))
    | closure _ upvars =>
      cases upvars with
      | nil =>
        rw [hk] at h; dsimp at h
        repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
      | cons u us =>
        rw [hk] at h; dsimp at h
        repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
        all_goals
          (cases h
           simp only [valueContainsUninit]
           try
             (first
              | rfl
              | exact valueListContainsUninit_decodeFieldsAtOffsetsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ ‹_›
              | exact valueListContainsUninit_decodeSeqFieldsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›))

/-- `decodeTypedValueFromBytes` never produces `Value.uninit`. -/
theorem valueContainsUninit_decodeTypedValueFromBytes :
    ∀ (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte) (v : Value),
      decodeTypedValueFromBytes fuel layouts ty bs = some v →
      valueContainsUninit v = false
  | 0, _, _, _, _, h => by cases h
  | fuel' + 1, layouts, ty, bs, v, h => by
    unfold decodeTypedValueFromBytes at h
    dsimp at h
    have ih : ∀ ty' bs' v', decodeTypedValueFromBytes fuel' layouts ty' bs' = some v' →
        valueContainsUninit v' = false :=
      valueContainsUninit_decodeTypedValueFromBytes fuel' layouts
    cases hk : (normalizeCodecTy ty).kind with
    | array elemKind n =>
      rw [hk] at h; dsimp at h
      repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
      all_goals
        (cases h
         simp only [valueContainsUninit]
         exact valueListContainsUninit_decodeArrayChunksWith _ (fun bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›)
    | tuple ks =>
      rw [hk] at h
      cases ks with
      | nil => exact valueContainsUninit_decodeValueFromBytes (fuel' + 1) layouts _ bs v h
      | cons kHead kTail =>
        dsimp at h
        repeat' (first | contradiction | (cases h; rfl) | split at h | dsimp at h)
        all_goals
          (cases h
           simp only [valueContainsUninit]
           first
           | exact valueListContainsUninit_decodeTypedKindsAndLayoutsAtOffsets _ ih layouts bs _ _ _ _ ‹_›
           | exact valueListContainsUninit_decodeFieldsAtOffsetsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ ‹_›
           | exact valueListContainsUninit_decodeSeqFieldsWith _ (fun k bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›)
    | adt _ _ =>
      rw [hk] at h; dsimp at h
      repeat'
        (first
         | contradiction
         | (cases h; rfl)
         | exact valueContainsUninit_decodeValueFromBytes (fuel' + 1) layouts _ bs v h
         | exact valueContainsUninit_decodeUnionBytesWithCountOpt layouts _ _ bs v h
         | exact valueContainsUninit_decodeScalarLayoutBytesNoForge _ bs v h
         | split at h
         | dsimp at h)
      all_goals
        (cases h
         first
         | exact valueContainsUninit_decodeScalarLayoutBytesNoForge _ _ _ ‹_›
         | (simp only [valueContainsUninit]
            first
            | rfl
            | exact valueListContainsUninit_decodeFieldsByLayoutIdxs _ (fun fl bs' v' hv => ih _ bs' v' hv) _ _ _ _ _ ‹_›
            | exact valueListContainsUninit_decodeFieldsBySpan _ _ _ _ ‹_›
            | exact valueListContainsUninit_decodeArrayChunksWith _ (fun bs' v' hv => ih _ bs' v' hv) _ _ _ _ ‹_›
            | (rename_i h1 h2; simp only [valueListContainsUninit,
                 valueContainsUninit_decodeScalarLayoutBytesNoForge _ _ _ h1,
                 valueContainsUninit_decodeScalarLayoutBytesNoForge _ _ _ h2]; done)
            | (rename_i h1; simp only [valueListContainsUninit,
                 valueContainsUninit_decodeScalarLayoutBytesNoForge _ _ _ h1]; done)))
    | bool | char | int _ | uint _ =>
      rw [hk] at h; dsimp at h
      cases hP : abstractBytesHaveProv bs with
      | true => rw [hP] at h; cases h
      | false =>
        rw [hP] at h
        exact valueContainsUninit_decodeValueFromBytes (fuel' + 1) layouts _ bs v h
    | fnPtr _ _ _ _ | rawPtr _ _ | ref _ _ =>
      rw [hk] at h; dsimp at h
      exact valueContainsUninit_decodePtrBytesNoForge _ _ _ bs v h
    | float _ | fnDef _ _ | never | str | slice _ | dynamic _ | param _ | alias _ _
    | foreign _ | closure _ _ | other _ =>
      rw [hk] at h; dsimp at h
      exact valueContainsUninit_decodeValueFromBytes (fuel' + 1) layouts _ bs v h

/-- Reading an empty projection chain on a value with `valueContainsUninit v = false` always
succeeds with `.ok v`. -/
theorem readProjectedValueUnionAware_nil_of_noUninit
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (ty : Ty) (hNoUninit : valueContainsUninit v = false) :
    readProjectedValueUnionAware locals localDecls layouts v ty [] = .ok v := by
  cases v with
  | unit => rfl
  | scalar _ => rfl
  | ptr _ _ => rfl
  | uninit => simp [valueContainsUninit] at hNoUninit
  | aggregate varIdx fs =>
    unfold readProjectedValueUnionAware
    cases isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts ty)
    · simp only [valueContainsUninit] at hNoUninit
      rw [hNoUninit]
    · rfl

/-- The resolved type `rFieldTy` at which `readProjectedValueUnionAware` reads union field `idx`
declared at `fieldTy` (the read's own `let rFieldTy`): `fieldTy` when its layout index is
resolved, else the union layout's `fieldLayouts[idx]`, else `resolveTyWithLocalDecls`. -/
def unionFieldReadTy (localDecls : List LocalDecl) (layouts : LayoutTable) (l : TypeLayout)
    (idx : Nat) (fieldTy : Ty) : Ty :=
  match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
  | false => fieldTy
  | true =>
    match get? l.fieldLayouts idx with
    | some flIdx => { fieldTy with layoutIdx := flIdx }
    | none => resolveTyWithLocalDecls localDecls layouts fieldTy

/-- Resolving a union field type keeps its kind. -/
theorem unionFieldReadTy_kind (localDecls : List LocalDecl) (layouts : LayoutTable)
    (l : TypeLayout) (idx : Nat) (fieldTy : Ty) :
    (unionFieldReadTy localDecls layouts l idx fieldTy).kind = fieldTy.kind := by
  unfold unionFieldReadTy
  cases isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;> dsimp only
  cases get? l.fieldLayouts idx <;> dsimp only
  exact Anneal.Mir.PlaceAndRvalue.resolveTyWithLocalDecls_kind localDecls layouts fieldTy

/-- The canonical value that an inhabited 0-byte read of type `ty` yields in
`readProjectedValueUnionAware`: its decoding from zero bytes (`decodeTypedValueFromBytes`), or
`.unit` when the decoder has no layout-free value for `ty` (a fieldless closure, which
`crates/anneal-mir`'s `canonical_zst_value` also represents as `MirValue::Unit`). -/
def zeroByteValue (layouts : LayoutTable) (ty : Ty) : Value :=
  match decodeTypedValueFromBytes defaultCodecFuel layouts ty .nil with
  | some v => v
  | none => .unit

/-- `zeroByteValue` never contains `Value.uninit`. -/
theorem valueContainsUninit_zeroByteValue (layouts : LayoutTable) (ty : Ty) :
    valueContainsUninit (zeroByteValue layouts ty) = false := by
  unfold zeroByteValue
  cases h : decodeTypedValueFromBytes defaultCodecFuel layouts ty .nil with
  | none => rfl
  | some v => exact valueContainsUninit_decodeTypedValueFromBytes defaultCodecFuel layouts ty .nil v h

/-- Slot `idx` of a union field list holds no direct value for a field of kind `k`
(`readProjectedValueUnionAware`'s `directFvOpt` is `.none`): the slot is absent, holds
`Value.uninit`, or holds the `.unit` placeholder of a field that is neither `()` nor a function
item (for those two the `.unit` slot is the field's value). Every typed slot of a union decoded
from bytes is inactive (`decodeUnionBytes_roundtrip`). -/
def UnionSlotInactive (fields : List Value) (idx : Nat) (k : RigidTy) : Prop :=
  get? fields idx = none ∨
    get? fields idx = some .uninit ∨
    (get? fields idx = some .unit ∧ k ≠ .tuple [] ∧ ∀ p a, k ≠ .fnDef p a)

/-- The well-formedness gate (`unionImageOk`) that `readProjectedValueUnionAware` applies before
reading an inactive slot: either no consistency check is needed (no raw-byte overlay and at most
one non-`.unit` typed slot), or the union value encodes to a storage image. -/
def UnionImageOk (layouts : LayoutTable) (uIdx count : Nat) (fields : List Value) : Prop :=
  unionNeedsConsistencyCheck count fields = false ∨
    ∃ img, encodeByLayoutIdxAux 8 layouts uIdx (.aggregate 0 fields) = some img

/-! ### Section 6b: `kani#5159` — 0-byte union field and sub-place reads -/

/-- **`kani#5159`, 0-byte field root (exact).** For a well-formed union value and an inactive
slot (absent, `Value.uninit`, or `.unit` placeholder), reading a 0-byte field `idx < count` faults
with `.ub` when the field type is uninhabited (`tyIsUninhabited`: `!`, `Infallible`, `enum Void {}`,
`[Infallible; 1]`, `ManuallyDrop<Infallible>`, ...) and otherwise returns its canonical value (`()`,
`[(); N]`, `PhantomData<Infallible>`, `[Infallible; 0]`, ...). -/
theorem readUnion_zeroByte_root
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] =
      match tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) with
      | true => .ub
      | false => .ok (zeroByteValue layouts (unionFieldReadTy localDecls layouts l idx fieldTy)) := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hSz hTk ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hSz hTk ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (simp only []; rw [hSz]; simp only []
       cases tyIsUninhabited layouts _
       · simp only []
         exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
           (zeroByteValue layouts _) _ (valueContainsUninit_zeroByteValue layouts _)
       · rfl)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;> rw [hSz] <;> simp only [] <;>
           (cases tyIsUninhabited layouts _
            · simp only []
              exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
                (zeroByteValue layouts _) _ (valueContainsUninit_zeroByteValue layouts _)
            · rfl))

set_option maxHeartbeats 400000 in
/-- **`kani#5159`, 0-byte sub-place (exact).** For a well-formed union value and an inactive slot,
reading a statically bounded (`checkStaticSubProjBounds`) sub-place of 0-byte type `leafTy` inside
field `idx` (of any size):
- faults with `.ub` iff the leaf type is uninhabited (`tyIsUninhabited layouts leafTy = true`);
- fails closed with `.unsupported` (never `.ub`) when `leafTy` is inhabited while `rFieldTy` or an
  intermediate container along the sub-projection (`subProjTouchesUninhabited`) is uninhabited
  (e.g. `_u.pair.1 : ()` with `pair : (Infallible, ())`, matching Miri/MiniRust's offset-only
  place projection semantics);
- otherwise returns `.ok (zeroByteValue layouts leafTy)`. -/
theorem readUnion_zeroByte_subProj
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (hSz : tyByteSize localDecls layouts leafTy = some 0) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) =
      match tyIsUninhabited layouts leafTy with
      | true => .ub
      | false =>
        match
          Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
            (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
              (normalizeSubsliceProjections (stripTransparentProjections idxResolved)))
        with
        | true => .unsupported
        | false => .ok (zeroByteValue layouts leafTy) := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hBounds hOff hLeaf ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hBounds hOff hLeaf ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (simp only []; rw [hRes]; simp only []; rw [hBounds]; simp only []; rw [hOff, hLeaf];
       simp only []
       cases tyIsUninhabited layouts leafTy
       · simp only []
         cases Bool.or (tyIsUninhabited layouts _) (subProjTouchesUninhabited localDecls layouts _ _)
         · simp only []; rw [hSz]; rfl
         · rfl
       · rfl)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;> rw [hRes] <;> simp only [] <;> rw [hBounds] <;>
           simp only [] <;> rw [hOff, hLeaf] <;> simp only [] <;>
           (cases tyIsUninhabited layouts leafTy
            · simp only []
              cases Bool.or (tyIsUninhabited layouts _) (subProjTouchesUninhabited localDecls layouts _ _)
              · simp only []; rw [hSz]; rfl
              · rfl
            · rfl))

set_option maxHeartbeats 400000 in
/-- **`kani#5159`, uninhabited leaf sub-projection of any leaf size.** For a well-formed union
value and an inactive slot, any statically bounded sub-projection whose **leaf** is uninhabited
(`tyIsUninhabited layouts leafTy = true`) faults with `.ub` — with no `tyByteSize` requirement on
`leafTy`. This covers 0-byte uninhabited leaves (`[Infallible; 1][0]`, `md.value`, `pair_u32.0`)
and uninhabited tuple leaves whose layout `tyByteSize` rejects (`V.p` with `p : (Infallible, ())`). -/
theorem kani5159_uninhabited_subProj_ub
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (hUninh : tyIsUninhabited layouts leafTy = true) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hBounds hOff hLeaf
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hBounds hOff hLeaf ⊢
  all_goals
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
    rcases hImg with hC | ⟨img, hEnc⟩ <;>
    (try rw [hC]) <;> (try rw [hEnc]) <;> (try cases unionNeedsConsistencyCheck count fields) <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    rw [hRes] <;> simp only [] <;> rw [hBounds] <;> simp only [] <;> rw [hOff, hLeaf] <;>
    simp only [] <;> rw [hUninh] <;> simp only []

/-- **Inhabited leaf through an uninhabited container fails closed as `.unsupported` (never `.ub`).**
When `leafTy` is inhabited (`tyIsUninhabited layouts leafTy = false`), projecting through an
uninhabited union field or intermediate container (`subProjTouchesUninhabited`) returns
`.unsupported` (with no `tyByteSize` requirement on `leafTy`), matching Miri/MiniRust's offset-only
place projection semantics and `crates/anneal-mir`'s `MirLowerError::InactiveUnionField`. -/
theorem kani5159_inhabitedLeaf_through_uninhabitedContainer_subProj_unsupported
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (hLeafInhab : tyIsUninhabited layouts leafTy = false)
    (hContainerUninh :
      Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
        (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
          (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) = true) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .unsupported := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hBounds hOff hLeaf hContainerUninh
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hBounds hOff hLeaf hContainerUninh ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields with
    | false =>
      rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
        simp only [] <;> rw [hRes] <;> simp only [] <;> rw [hBounds] <;> simp only [] <;>
        rw [hOff, hLeaf] <;> simp only [] <;> rw [hLeafInhab] <;> simp only [] <;>
        rw [hContainerUninh] <;> rfl
    | true =>
      rcases hImg with h | ⟨img, hEnc⟩
      · rw [hC] at h; cases h
      · rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
          rw [hEnc] <;> simp only [] <;> (try (cases l.fieldLayouts <;> simp only [])) <;>
          rw [hRes] <;> simp only [] <;> rw [hBounds] <;> simp only [] <;>
          rw [hOff, hLeaf] <;> simp only [] <;> rw [hLeafInhab] <;> simp only [] <;>
          rw [hContainerUninh] <;> rfl

set_option maxHeartbeats 400000 in
/-- **0-byte field root under a non-static sub-projection.** When the sub-projection `p :: ps` is
not statically bounded (for example, it downcasts or subslices past a synthetic layout), an
uninhabited field returns `.ub` iff `resolveProjectedTyResolved` resolves `normRest` to an
uninhabited leaf and `.unsupported` otherwise (never falling through to a false-positive `.ub` on
a possibly inhabited leaf), while an inhabited 0-byte field continues the projection from its
canonical value. -/
theorem readUnion_zeroByte_fieldRoot
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) =
      match tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) with
      | true =>
        match resolveProjectedTyResolved localDecls layouts
            (unionFieldReadTy localDecls layouts l idx fieldTy)
            (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) with
        | some leafTy =>
          match tyIsUninhabited layouts leafTy with
          | true => .ub
          | false => .unsupported
        | none => .unsupported
      | false =>
        readProjectedValueUnionAware locals localDecls layouts
          (zeroByteValue layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
          (unionFieldReadTy localDecls layouts l idx fieldTy) (p :: ps) := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  conv => lhs; unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hSz hBounds ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hSz hBounds ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (simp only []; rw [hRes]; simp only []; rw [hBounds]; simp only []; rw [hSz]; simp only []
       cases tyIsUninhabited layouts _ <;> rfl)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;> rw [hRes] <;> simp only [] <;> rw [hBounds] <;>
           simp only [] <;> rw [hSz] <;> simp only [] <;>
           (cases tyIsUninhabited layouts _ <;> rfl))

set_option maxHeartbeats 800000 in
/-- **Non-empty sub-projection fallthrough guard (any field size).** Whenever a non-empty
sub-projection `p :: ps` through an uninhabited union field `rFieldTy` is not statically bounded
(`checkStaticSubProjBounds = false`) and does not resolve to an uninhabited leaf,
`readProjectedValueUnionAware` fails closed with `.unsupported` (never `.ub`), regardless of
`tyByteSize rFieldTy`. -/
theorem readUnion_uninhabited_nonEmpty_fallthrough_unsupported
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hUninh : tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = true)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = false)
    (hNotUninhLeaf : ∀ leafTy,
      resolveProjectedTyResolved localDecls layouts
        (unionFieldReadTy localDecls layouts l idx fieldTy)
        (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy →
      tyIsUninhabited layouts leafTy = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .unsupported := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hUninh hBounds hNotUninhLeaf
  cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu] at hTk hUninh hBounds hNotUninhLeaf ⊢
  · rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;>
    rcases hImg with hC | ⟨img, hEnc⟩ <;>
    (try rw [hC]) <;> (try rw [hEnc]) <;> (try cases unionNeedsConsistencyCheck count fields) <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    rw [hRes] <;> simp only [] <;> rw [hBounds] <;> simp only [] <;>
    (cases tyByteSize localDecls layouts fieldTy with
     | none =>
       simp only [hUninh]
       cases hL : resolveProjectedTyResolved localDecls layouts fieldTy _ with
       | none => rfl
       | some leafTy => simp only [hNotUninhLeaf leafTy hL]
     | some sz =>
       cases sz with
       | zero =>
         simp only [hUninh]
         cases hL : resolveProjectedTyResolved localDecls layouts fieldTy _ with
         | none => rfl
         | some leafTy => simp only [hNotUninhLeaf leafTy hL]
       | succ szPred =>
         dsimp only
         cases hk : fieldTy.kind <;>
           first
           | (exfalso; unfold tyIsUninhabited at hUninh; rw [hk] at hUninh; exact Bool.false_ne_true hUninh)
           | (simp only [hUninh]
              cases hL : resolveProjectedTyResolved localDecls layouts fieldTy _ with
              | none => rfl
              | some leafTy => simp only [hNotUninhLeaf leafTy hL]))
  · cases hg : get? l.fieldLayouts idx <;>
      simp only [hg] at hTk hUninh hBounds hNotUninhLeaf ⊢ <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
    rcases hImg with hC | ⟨img, hEnc⟩ <;>
    (try rw [hC]) <;> (try rw [hEnc]) <;> (try cases unionNeedsConsistencyCheck count fields) <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    rw [hRes] <;> simp only [] <;> rw [hBounds] <;> simp only [] <;>
    (cases tyByteSize localDecls layouts _ with
     | none =>
       simp only [hUninh]
       cases hL : resolveProjectedTyResolved localDecls layouts _ _ with
       | none => rfl
       | some leafTy => simp only [hNotUninhLeaf leafTy hL]
     | some sz =>
       cases sz with
       | zero =>
         simp only [hUninh]
         cases hL : resolveProjectedTyResolved localDecls layouts _ _ with
         | none => rfl
         | some leafTy => simp only [hNotUninhLeaf leafTy hL]
       | succ szPred =>
         dsimp only
         cases hk : fieldTy.kind <;>
           first
           | (exfalso; unfold tyIsUninhabited at hUninh; (try dsimp only at hUninh);
              (try rw [hTk] at hUninh); rw [hk] at hUninh; exact Bool.false_ne_true hUninh)
           | ((try rw [hk] at hUninh); simp only [hUninh]
              cases hL : resolveProjectedTyResolved localDecls layouts _ _ with
              | none => rfl
              | some leafTy =>
                (try rw [← hk] at hL)
                simp only [hNotUninhLeaf leafTy hL]))

/-- **`kani#5159`, field root, two-sided (`.ub`).** Under the hypotheses of
`readUnion_zeroByte_root`, the read faults with `.ub` iff the field is uninhabited. -/
theorem readUnion_zeroByte_root_ub_iff
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ub ↔
      tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = true := by
  rw [readUnion_zeroByte_root locals localDecls layouts baseTy fieldTy fields idx count l d args hKind
    hLookup hFields hIdx hImg hSlot hSz]
  cases tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) <;> simp

/-- **`kani#5159`, field root, two-sided (`.ok`).** Under the hypotheses of
`readUnion_zeroByte_root`, the read returns the field's canonical value (equivalently, returns any
`.ok` value) iff the field is inhabited. -/
theorem readUnion_zeroByte_root_ok_iff
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0) :
    (readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] =
      .ok (zeroByteValue layouts (unionFieldReadTy localDecls layouts l idx fieldTy)) ↔
      tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = false) ∧
    ((∃ v, readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ok v) ↔
      tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = false) := by
  rw [readUnion_zeroByte_root locals localDecls layouts baseTy fieldTy fields idx count l d args hKind
    hLookup hFields hIdx hImg hSlot hSz]
  cases tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) <;> simp

/-- **Field root of undetermined size.** When `tyByteSize` leaves the field size undetermined
(for example, the captured layout of an uninhabited tuple `(Infallible, ())`, which
`layoutMatchesAggregateVariant` rejects), the read faults with `.ub` for an uninhabited field and
is `.unsupported` otherwise. -/
theorem readUnion_unsized_root
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = none) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] =
      match tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) with
      | true => .ub
      | false => .unsupported := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hSz hTk ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hSz hTk ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (simp only []; rw [hSz]; simp only []; cases tyIsUninhabited layouts _ <;> rfl)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;> rw [hSz] <;> simp only [] <;>
           (cases tyIsUninhabited layouts _ <;> rfl))

set_option maxHeartbeats 800000 in
/-- **`kani#5159` (field root, any size).** Reading an uninhabited union field from an inactive
slot of a well-formed union faults with `.ub` across `.none`, `.some 0`, and `.some (.succ _)`
sizes (because at `rest = .nil`, `rFieldTy` IS the leaf being loaded). -/
theorem kani5159_uninhabited_field_root_ub
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (hUninh : tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = true) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hUninh
  cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu] at hTk hUninh ⊢
  · rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;>
    rcases hImg with hC | ⟨img, hEnc⟩ <;>
    (try rw [hC]) <;> (try rw [hEnc]) <;> (try cases unionNeedsConsistencyCheck count fields) <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    (cases tyByteSize localDecls layouts fieldTy with
     | none => simp only [hUninh]
     | some sz =>
       cases sz with
       | zero => simp only [hUninh]
       | succ szPred =>
         dsimp only
         cases hk : fieldTy.kind <;>
           first
           | (exfalso; unfold tyIsUninhabited at hUninh; rw [hk] at hUninh; exact Bool.false_ne_true hUninh)
           | simp only [hUninh])
  · cases hg : get? l.fieldLayouts idx <;>
      simp only [hg] at hTk hUninh ⊢ <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
    rcases hImg with hC | ⟨img, hEnc⟩ <;>
    (try rw [hC]) <;> (try rw [hEnc]) <;> (try cases unionNeedsConsistencyCheck count fields) <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    (cases tyByteSize localDecls layouts _ with
     | none => simp only [hUninh]
     | some sz =>
       cases sz with
       | zero => simp only [hUninh]
       | succ szPred =>
         dsimp only
         cases hk : fieldTy.kind <;>
           first
           | rfl
           | (exfalso; unfold tyIsUninhabited at hUninh; (try dsimp only at hUninh);
              (try rw [hTk] at hUninh); rw [hk] at hUninh; exact Bool.false_ne_true hUninh)
           | ((try rw [hk] at hUninh); simp only [hUninh]))

/-- **`()` / function-item fields with a `.unit` slot.** For these two kinds the `.unit` slot is
the field's value: the read returns it directly (`directFvOpt`), whatever the image check needs. -/
theorem readUnion_unitKind_unitSlot_root
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hS : get? fields idx = some .unit)
    (hUnitKind : fieldTy.kind = .tuple [] ∨ ∃ p a, fieldTy.kind = .fnDef p a) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ok .unit := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk ⊢
  all_goals
    rw [hS]
    (try rw [hTk])
    rcases hUnitKind with hk | ⟨p, a, hk⟩ <;> rw [hk] <;> simp only [] <;>
    cases hC : unionNeedsConsistencyCheck count fields <;> simp only []
  all_goals
    first
    | rfl
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []; cases l.fieldLayouts <;> rfl)

/-- **An active slot is read back as stored (all 5 `Value` constructors).** When slot `idx` holds
a non-`.unit`, non-`.uninit` value `fv` containing no nested `Value.uninit` and no consistency
check is needed, the field-root read returns `fv` unchanged. -/
theorem readUnion_activeSlot_root
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hCons : unionNeedsConsistencyCheck count fields = false)
    (fv : Value) (hS : get? fields idx = some fv)
    (hNeUnit : fv ≠ .unit) (hNeUninit : fv ≠ .uninit)
    (hNoUninit : valueContainsUninit fv = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ok fv := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  rw [hS, hCons]
  cases fv with
  | unit => exact absurd rfl hNeUnit
  | uninit => exact absurd rfl hNeUninit
  | scalar _ => rfl
  | ptr _ _ => rfl
  | aggregate varIdx aggFs =>
    simp only []
    exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
      (.aggregate varIdx aggFs) _ hNoUninit

/-- **Explicit `Value.uninit` slot behaves identically to an inactive slot.** When slot `idx` holds
`some .uninit`, `readProjectedValueUnionAware` maps `directFvOpt` to `.none` and falls through to
inactive-slot byte/ZST semantics: an inhabited 0-byte field (including `()` and `fnDef`!) reads its
canonical value rather than faulting directly on `.uninit`, while an uninhabited field faults with
`.ub`. -/
theorem readUnion_uninitSlot_zeroByte_root
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hS : get? fields idx = some .uninit)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] =
      match tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) with
      | true => .ub
      | false => .ok (zeroByteValue layouts (unionFieldReadTy localDecls layouts l idx fieldTy)) :=
  readUnion_zeroByte_root locals localDecls layouts baseTy fieldTy fields idx count l d args
    hKind hLookup hFields hIdx hImg (Or.inr (Or.inl hS)) hSz

/-- **`kani#5159`, no spurious `.ub` at a 0-byte field root.** For every union value whose active
slot (if an aggregate) contains no `Value.uninit`, a 0-byte field read faults with `.ub` only if
the field is uninhabited. This holds whatever the slot holds (absent, `Value.uninit`, `.unit`, or
an initialized active value) and whether or not the value needs a consistency check. -/
theorem readUnion_zeroByte_root_ub_imp_uninhabited
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0)
    (hNoUninitSlot : ∀ varIdx aggFs, get? fields idx = some (.aggregate varIdx aggFs) →
      valueListContainsUninit aggFs = false)
    (hUb : readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ub) :
    tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = true := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware at hUb
  dsimp only at hUb
  rw [hKind, hLookup] at hUb
  dsimp only at hUb
  rw [hFields] at hUb
  dsimp only at hUb
  rw [hBle] at hUb
  simp only [] at hUb
  unfold unionFieldReadTy at hSz ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hSz hUb ⊢
  all_goals
    cases hGet : get? fields idx with
    | none =>
      rw [hGet] at hUb; simp only [] at hUb
      split at hUb
      · nomatch hUb
      · rename_i fv heq; cases heq
      · rw [hSz] at hUb; simp only [] at hUb
        split at hUb
        · assumption
        · change readProjectedValueUnionAware locals localDecls layouts (zeroByteValue layouts _) _ [] = .ub at hUb
          rw [readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
            (zeroByteValue layouts _) _ (valueContainsUninit_zeroByteValue layouts _)] at hUb
          nomatch hUb
    | some fv =>
      cases fv with
      | uninit =>
        rw [hGet] at hUb; simp only [] at hUb
        split at hUb
        · nomatch hUb
        · rename_i fv heq; cases heq
        · rw [hSz] at hUb; simp only [] at hUb
          split at hUb
          · assumption
          · change readProjectedValueUnionAware locals localDecls layouts (zeroByteValue layouts _) _ [] = .ub at hUb
            rw [readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
              (zeroByteValue layouts _) _ (valueContainsUninit_zeroByteValue layouts _)] at hUb
            nomatch hUb
      | unit =>
        rw [hGet] at hUb; simp only [] at hUb
        split at hUb
        · nomatch hUb
        · rename_i fv _ heq
          have hU : fv = .unit := by
            split at heq <;> cases heq <;> rfl
          subst hU
          simp [readProjectedValueUnionAware] at hUb
        · rw [hSz] at hUb; simp only [] at hUb
          split at hUb
          · assumption
          · change readProjectedValueUnionAware locals localDecls layouts (zeroByteValue layouts _) _ [] = .ub at hUb
            rw [readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
              (zeroByteValue layouts _) _ (valueContainsUninit_zeroByteValue layouts _)] at hUb
            nomatch hUb
      | scalar _ =>
        rw [hGet] at hUb; simp only [] at hUb
        split at hUb
        · nomatch hUb
        · rename_i fv heq; cases heq; simp [readProjectedValueUnionAware] at hUb
        · rename_i heq; cases heq
      | ptr _ _ =>
        rw [hGet] at hUb; simp only [] at hUb
        split at hUb
        · nomatch hUb
        · rename_i fv heq; cases heq; simp [readProjectedValueUnionAware] at hUb
        · rename_i heq; cases heq
      | aggregate varIdx aggFs =>
        have hNoU := hNoUninitSlot varIdx aggFs hGet
        rw [hGet] at hUb; simp only [] at hUb
        split at hUb
        · nomatch hUb
        · rename_i fv heq; cases heq
          rw [readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts
            (.aggregate varIdx aggFs) _ (by simpa [valueContainsUninit] using hNoU)] at hUb
          nomatch hUb
        · rename_i heq; cases heq

/-! ### Section 6c: Offset-0 decoding of positive-sized union fields -/

/-- An in-bounds prefix slice of a byte list is its `take`. -/
theorem sliceAbstractBytes_zero_take (bs : List AbstractByte) (n : Nat) (h : n ≤ bs.length) :
    sliceAbstractBytes bs 0 n = some (bs.take n) := by
  unfold sliceAbstractBytes
  have hBle : Nat.ble (Nat.add 0 n) (length bs) = true := by
    change Nat.ble (0 + n) bs.length = true
    rw [Nat.zero_add]
    exact Nat.ble_eq.mpr h
  rw [hBle]
  dsimp only
  rw [dropAbstractBytes_eq_drop, List.drop_zero, takeAbstractBytes_eq_take]

/-- A positive `tyByteSize` excludes the (0-byte) `()` and function-item kinds. -/
theorem tyByteSize_succ_kind (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Ty) (n : Nat)
    (h : tyByteSize localDecls layouts ty = some (n + 1)) :
    ty.kind ≠ .tuple [] ∧ ∀ p a, ty.kind ≠ .fnDef p a := by
  have hk := Anneal.Mir.PlaceAndRvalue.resolveTyWithLocalDecls_kind localDecls layouts ty
  unfold tyByteSize tyByteSizeAndAlignAux at h
  dsimp only at h
  rw [hk] at h
  refine ⟨fun hT => ?_, fun p a hF => ?_⟩
  · rw [hT] at h; simp at h
  · rw [hF] at h; simp at h

set_option maxHeartbeats 800000 in
/-- **Offset-0 decoding of a positive-sized union field (exact).** Every union field sits at
offset `0`: reading an inactive field of size `n + 1` from a union value whose storage image is
`img` faults with `.ub` when the field is uninhabited and otherwise decodes `img.take (n + 1)`,
returning `.ok` with the decoded value and `.ub` when those bytes are uninitialized or invalid at
the field type. -/
theorem readUnion_posField_offset0
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (img : List AbstractByte)
    (hEnc : encodeByLayoutIdxAux 8 layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx
      (.aggregate 0 fields) = some img)
    (n : Nat)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some (n + 1))
    (hLe : n + 1 ≤ img.length) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] =
      match tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) with
      | true => .ub
      | false =>
        match decodeTypedValueFromBytes defaultCodecFuel layouts
            (unionFieldReadTy localDecls layouts l idx fieldTy) (img.take (n + 1)) with
        | some v => .ok v
        | none => .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  have hSlice := sliceAbstractBytes_zero_take img (n + 1) hLe
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hSz hTk ⊢
  cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu] at hSz hTk ⊢
  · cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> rw [hEnc] <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    rw [hSz] <;> simp only [] <;>
    (cases hk : fieldTy.kind <;>
     first
     | (unfold tyIsUninhabited; rw [hk]; simp only [hSlice]
        cases hDec : decodeTypedValueFromBytes defaultCodecFuel layouts fieldTy (img.take (n + 1)) with
        | none => rfl
        | some v =>
          exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts v fieldTy
            (valueContainsUninit_decodeTypedValueFromBytes defaultCodecFuel layouts fieldTy _ v hDec))
     | (cases tyIsUninhabited layouts fieldTy
        · simp only [hSlice]
          cases hDec : decodeTypedValueFromBytes defaultCodecFuel layouts fieldTy (img.take (n + 1)) with
          | none => rfl
          | some v =>
            exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts v fieldTy
              (valueContainsUninit_decodeTypedValueFromBytes defaultCodecFuel layouts fieldTy _ v hDec)
        · rfl))
  · cases hg : get? l.fieldLayouts idx <;>
      simp only [hg] at hSz hTk ⊢ <;>
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;> rw [hEnc] <;>
    (try cases l.fieldLayouts) <;> simp only [] <;>
    rw [hSz] <;> simp only [] <;>
    (cases hk : fieldTy.kind <;>
     first
     | (unfold tyIsUninhabited; (try dsimp only); (try rw [hTk]); (try rw [hk]); simp only [hSlice]
        cases hDec : decodeTypedValueFromBytes defaultCodecFuel layouts _ (img.take (n + 1)) with
        | none => rfl
        | some v =>
          exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts v _
            (valueContainsUninit_decodeTypedValueFromBytes defaultCodecFuel layouts _ _ v hDec))
     | (cases tyIsUninhabited layouts _
        · simp only [hSlice]
          cases hDec : decodeTypedValueFromBytes defaultCodecFuel layouts _ (img.take (n + 1)) with
          | none => rfl
          | some v =>
            exact readProjectedValueUnionAware_nil_of_noUninit locals localDecls layouts v _
              (valueContainsUninit_decodeTypedValueFromBytes defaultCodecFuel layouts _ _ v hDec)
        · rfl))

/-- **Positive-sized sub-place of a union field (exact).** Reading a statically bounded sub-place of
positive size `n + 1` at byte offset `subOff` inside field `idx`:
- faults with `.ub` when `leafTy` is uninhabited;
- fails closed with `.unsupported` (never `.ub`) when `leafTy` is inhabited while `rFieldTy` or an
  intermediate container along the sub-projection (`subProjTouchesUninhabited`) is uninhabited
  (e.g. `(Infallible, u32).1`);
- otherwise slices `img` at `[subOff .. subOff + (n + 1))` and decodes at `leafTy`. -/
theorem readUnion_posLeaf_subProj
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (img : List AbstractByte)
    (hEnc : encodeByLayoutIdxAux 8 layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx
      (.aggregate 0 fields) = some img)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (n : Nat)
    (hSz : tyByteSize localDecls layouts leafTy = some (n + 1)) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) =
      match tyIsUninhabited layouts leafTy with
      | true => .ub
      | false =>
        match
          Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
            (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
              (normalizeSubsliceProjections (stripTransparentProjections idxResolved)))
        with
        | true => .unsupported
        | false =>
          match sliceAbstractBytes img subOff (n + 1) with
          | none => .ub
          | some leafSlice =>
            match decodeTypedValueFromBytes defaultCodecFuel layouts leafTy leafSlice with
            | some leafVal => .ok leafVal
            | none => .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTy_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTy at hTk hBounds hOff hLeaf ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hBounds hOff hLeaf ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;>
    (try rw [hEnc]) <;> simp only []
  all_goals (try (cases l.fieldLayouts <;> simp only []))
  all_goals
    rw [hRes]; simp only []; rw [hBounds]; simp only []; rw [hOff, hLeaf]; simp only []
    cases tyIsUninhabited layouts leafTy
    · simp only []
      cases Bool.or (tyIsUninhabited layouts _) (subProjTouchesUninhabited localDecls layouts _ _)
      · simp only []; rw [hSz]; simp only []; (try (rw [hEnc]; simp only []))
        cases sliceAbstractBytes img subOff (n + 1) <;> simp only []
        cases decodeTypedValueFromBytes defaultCodecFuel layouts leafTy _ <;> simp only []
      · rfl
    · rfl

/-- `splitUnionTypedAndOverlay` separates `count` inactive slots from a raw-byte overlay. -/
theorem splitUnionTypedAndOverlay_units_overlay (rawVals : List Value) :
    ∀ count : Nat,
      splitUnionTypedAndOverlay count
          (appendValueList (replicateValue count .unit) [.aggregate 0 rawVals]) =
        some (replicateValue count .unit, some rawVals)
  | 0 => rfl
  | k + 1 => by
    simp only [replicateValue, appendValueList, splitUnionTypedAndOverlay,
      splitUnionTypedAndOverlay_units_overlay rawVals k]

/-- `splitUnionTypedAndOverlay` on `count` inactive slots without an overlay. -/
theorem splitUnionTypedAndOverlay_units :
    ∀ count : Nat,
      splitUnionTypedAndOverlay count (replicateValue count .unit) =
        some (replicateValue count .unit, none)
  | 0 => rfl
  | k + 1 => by
    simp only [replicateValue, splitUnionTypedAndOverlay, splitUnionTypedAndOverlay_units k]

/-- Inactive (`.unit`) slots occupy no storage next to a raw-byte overlay. -/
theorem unionNonUnitNonZstTypedSlotCount_units (layouts : LayoutTable) :
    ∀ (count : Nat) (fls : List Nat),
      unionNonUnitNonZstTypedSlotCount layouts count fls (replicateValue count .unit) = 0
  | 0, _ => rfl
  | k + 1, [] => unionNonUnitNonZstTypedSlotCount_units layouts k []
  | k + 1, _ :: fls => unionNonUnitNonZstTypedSlotCount_units layouts k fls

/-- Inactive (`.unit`) slots occupy no layout-free storage. -/
theorem unionLayoutFreeOccupiedSlotCount_units (h : Bool) :
    ∀ count : Nat, unionLayoutFreeOccupiedSlotCount h count (replicateValue count .unit) = 0
  | 0 => rfl
  | k + 1 => by
    simp only [replicateValue, unionLayoutFreeOccupiedSlotCount,
      unionLayoutFreeOccupiedSlotCount_units h k]

/-- Merging inactive (`.unit`) slots leaves the storage image unchanged. -/
theorem mergeUnionTypedSlotsAux_units (layouts : LayoutTable)
    (encodeSlot : Nat → Value → Option (List AbstractByte)) (fallbackLayoutIdx : Nat)
    (hasOverlay : Bool) (unionSize : Nat) :
    ∀ (count : Nat) (fls : List Nat) (buf : List AbstractByte) (mask : List Bool),
      mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize fls
          (replicateValue count .unit) buf mask = some buf
  | 0, _, _, _ => by simp only [replicateValue, mergeUnionTypedSlotsAux]
  | k + 1, [], buf, mask => by
    simp only [replicateValue, mergeUnionTypedSlotsAux,
      mergeUnionTypedSlotsAux_units layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize k [] buf
        mask]
  | k + 1, _ :: fls, buf, mask => by
    simp only [replicateValue, mergeUnionTypedSlotsAux,
      mergeUnionTypedSlotsAux_units layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize k fls buf
        mask]

/-- A union value whose `count` slots are all inactive encodes to all-`.uninit` storage. -/
theorem encodeByLayoutIdxAux_units (layouts : LayoutTable) (uIdx : Nat) (uL : TypeLayout)
    (count : Nat) (hLookup : LayoutTable.lookup layouts uIdx = some uL)
    (hInhab : uL.isUninhabited = false) (hFields : uL.fields = .union count) :
    encodeByLayoutIdxAux 8 layouts uIdx (.aggregate 0 (replicateValue count .unit)) =
      some (replicateUninitBytes uL.size.bytes) := by
  unfold encodeByLayoutIdxAux
  rw [hLookup]
  dsimp only
  rw [hInhab]
  dsimp only
  rw [hFields]
  dsimp only
  unfold encodeUnionSlotsIntoBufAux
  rw [splitUnionTypedAndOverlay_units]
  dsimp only
  have h20 : Nat.ble 2 0 = false := rfl
  cases hFL : uL.fieldLayouts with
  | nil =>
    simp only [unionLayoutFreeOccupiedSlotCount_units, h20, Bool.false_and,
      mergeUnionTypedSlotsAux_units]
  | cons f fs =>
    simp only [mergeUnionTypedSlotsAux_units]

/-- A byte whose raw-overlay slot encoding (`encodeRawAbstractByteVals`) round-trips through
`overlayRawAbstractByteVals`: uninitialized, provenance-free, or carrying the canonical provenance
`(allocId, allocId)` (`ProvenancePtr.tag`). -/
def RawOverlayCanonical : AbstractByte → Prop
  | .uninit => True
  | .init _ none => True
  | .init _ (some (a, t)) => t = a

/-- The raw-byte overlay of a canonical image reproduces it over any equally long buffer. -/
theorem overlayRaw_encodeRaw :
    ∀ (img buf : List AbstractByte), buf.length = img.length →
      (∀ b ∈ img, RawOverlayCanonical b) →
      overlayRawAbstractByteVals (encodeRawAbstractByteVals img) buf = some img
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: rest, _ :: bufRest, h, hc => by
    have ih := overlayRaw_encodeRaw rest bufRest (by simpa using h)
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have hb := hc b List.mem_cons_self
    cases b with
    | uninit => simp [encodeRawAbstractByteVals, overlayRawAbstractByteVals, ih]
    | init byte prov =>
      cases prov with
      | none => simp [encodeRawAbstractByteVals, overlayRawAbstractByteVals, ih]
      | some pa =>
        obtain ⟨a, t⟩ := pa
        simp only [RawOverlayCanonical] at hb
        subst hb
        simp [encodeRawAbstractByteVals, overlayRawAbstractByteVals, ih, ProvenancePtr.tag]

/-- A union value of `count` inactive slots and the raw-byte overlay of a canonical image `img`
of the union's size encodes back to exactly `img`. -/
theorem encodeByLayoutIdxAux_rawOverlay (layouts : LayoutTable) (uIdx : Nat) (uL : TypeLayout)
    (count : Nat) (img : List AbstractByte) (hLookup : LayoutTable.lookup layouts uIdx = some uL)
    (hInhab : uL.isUninhabited = false) (hFields : uL.fields = .union count)
    (hLen : img.length = uL.size.bytes) (hCanon : ∀ b ∈ img, RawOverlayCanonical b) :
    encodeByLayoutIdxAux 8 layouts uIdx
        (.aggregate 0 (appendValueList (replicateValue count .unit)
          [.aggregate 0 (encodeRawAbstractByteVals img)])) =
      some img := by
  unfold encodeByLayoutIdxAux
  rw [hLookup]
  dsimp only
  rw [hInhab]
  dsimp only
  rw [hFields]
  dsimp only
  unfold encodeUnionSlotsIntoBufAux
  rw [splitUnionTypedAndOverlay_units_overlay]
  dsimp only
  have hLenBuf : (replicateUninitBytes uL.size.bytes).length = img.length := by
    rw [replicateUninitBytes_eq_replicate, List.length_replicate, hLen]
  have hOv := overlayRaw_encodeRaw img _ hLenBuf hCanon
  have h20 : Nat.ble 2 0 = false := rfl
  have h01 : Nat.ble 0 1 = true := rfl
  cases hFL : uL.fieldLayouts with
  | nil =>
    simp only [unionLayoutFreeOccupiedSlotCount_units, h20, Bool.false_and,
      unionNonUnitNonZstTypedSlotCount_units, h01, hOv, mergeUnionTypedSlotsAux_units]
  | cons f fs =>
    simp only [unionNonUnitNonZstTypedSlotCount_units, h01, hOv, mergeUnionTypedSlotsAux_units]

/-- `abstractByteEq` is sound for equality. -/
theorem abstractByteEq_eq_true : ∀ {a b : AbstractByte}, abstractByteEq a b = true → a = b
  | .uninit, .uninit, _ => rfl
  | .uninit, .init _ _, h => by simp [abstractByteEq] at h
  | .init _ _, .uninit, h => by simp [abstractByteEq] at h
  | .init x p, .init y q, h => by
    unfold abstractByteEq at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hxy, hpq⟩ := h
    have hx : x = y := UInt8.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hxy))
    have hp : p = q := by
      cases p with
      | none =>
        cases q with
        | none => rfl
        | some _ => simp [abstractByteProvEq] at hpq
      | some pa =>
        cases q with
        | none => simp [abstractByteProvEq] at hpq
        | some qa =>
          obtain ⟨a1, t1⟩ := pa
          obtain ⟨a2, t2⟩ := qa
          simp only [abstractByteProvEq, Bool.and_eq_true] at hpq
          rw [Nat.eq_of_beq_eq_true hpq.1, Nat.eq_of_beq_eq_true hpq.2]
    rw [hx, hp]

/-- `abstractByteListEq` is sound for equality. -/
theorem abstractByteListEq_eq_true :
    ∀ {xs ys : List AbstractByte}, abstractByteListEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [abstractByteListEq] at h
  | _ :: _, [], h => by simp [abstractByteListEq] at h
  | x :: xs, y :: ys, h => by
    unfold abstractByteListEq at h
    rw [Bool.and_eq_true] at h
    rw [abstractByteEq_eq_true h.1, abstractByteListEq_eq_true h.2]

/-- Every in-range slot of `replicateValue count v` is `v`. -/
theorem get?_replicateValue :
    ∀ (count i : Nat) (v : Value), i < count → get? (replicateValue count v) i = some v
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _ => rfl
  | k + 1, i + 1, v, h => by
    have ih := get?_replicateValue k i v (Nat.lt_of_succ_lt_succ h)
    unfold get? at ih ⊢
    simpa [replicateValue] using ih

/-- The first `count` slots of `replicateValue count v ++ ys` are `v`. -/
theorem get?_appendValueList_replicateValue :
    ∀ (count i : Nat) (v : Value) (ys : List Value), i < count →
      get? (appendValueList (replicateValue count v) ys) i = some v
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _ => rfl
  | k + 1, i + 1, v, ys, h => by
    have ih := get?_appendValueList_replicateValue k i v ys (Nat.lt_of_succ_lt_succ h)
    unfold get? at ih ⊢
    simpa [replicateValue, appendValueList] using ih

/-- **Union byte images round-trip.** Decoding a canonical byte image `img` of an inhabited
`count`-field union (`decodeUnionBytesWithCountOpt`) yields a value whose `count` typed slots are
all inactive (`.unit`) and which encodes back to exactly `img` (`encodeByLayoutIdxAux`). -/
theorem decodeUnionBytes_roundtrip (layouts : LayoutTable) (uIdx : Nat) (uL : TypeLayout)
    (count : Nat) (img : List AbstractByte) (hLookup : LayoutTable.lookup layouts uIdx = some uL)
    (hInhab : uL.isUninhabited = false) (hFields : uL.fields = .union count)
    (hLen : img.length = uL.size.bytes) (hCanon : ∀ b ∈ img, RawOverlayCanonical b) :
    ∃ fs, decodeUnionBytesWithCountOpt layouts uIdx count img = some (.aggregate 0 fs) ∧
      encodeByLayoutIdxAux 8 layouts uIdx (.aggregate 0 fs) = some img ∧
      ∀ i, i < count → get? fs i = some .unit := by
  have hEmpty := encodeByLayoutIdxAux_units layouts uIdx uL count hLookup hInhab hFields
  unfold decodeUnionBytesWithCountOpt finalizeUnionFieldsWithRawOverlayOpt
  dsimp only
  rw [hEmpty]
  dsimp only
  cases hEq : abstractByteListEq (replicateUninitBytes uL.size.bytes) img with
  | true =>
    have himg := abstractByteListEq_eq_true hEq
    simp only [forceValueListOpt_eq]
    exact ⟨_, rfl, by rw [hEmpty, himg], fun i hi => get?_replicateValue count i .unit hi⟩
  | false =>
    simp only [forceValueListOpt_eq]
    exact ⟨_, rfl,
      encodeByLayoutIdxAux_rawOverlay layouts uIdx uL count img hLookup hInhab hFields hLen hCanon,
      fun i hi => get?_appendValueList_replicateValue count i .unit _ hi⟩

/-- **`kani#5159`, 0-byte sub-place, three-way exact characterization.** Under the hypotheses of
`readUnion_zeroByte_subProj`:
1. `.ub` iff `leafTy` is uninhabited;
2. `.unsupported` iff `leafTy` is inhabited while `rFieldTy` or an intermediate container along the
   sub-projection is uninhabited;
3. `.ok (zeroByteValue layouts leafTy)` (equivalently `∃ v, ... = .ok v`) iff `leafTy`, `rFieldTy`,
   and all intermediate containers are inhabited. -/
theorem readUnion_zeroByte_subProj_iff
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOk layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactive fields idx fieldTy.kind)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (hSz : tyByteSize localDecls layouts leafTy = some 0) :
    (readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .ub ↔
      tyIsUninhabited layouts leafTy = true) ∧
    (readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .unsupported ↔
      tyIsUninhabited layouts leafTy = false ∧
        Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
          (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
            (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) = true) ∧
    (readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .ok (zeroByteValue layouts leafTy) ↔
      tyIsUninhabited layouts leafTy = false ∧
        Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
          (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
            (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) = false) ∧
    ((∃ v, readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) = .ok v) ↔
      tyIsUninhabited layouts leafTy = false ∧
        Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
          (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
            (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) = false) := by
  rw [readUnion_zeroByte_subProj locals localDecls layouts baseTy fieldTy fields idx count l d args hKind
    hLookup hFields hIdx hImg hSlot p ps idxResolved hRes hBounds subOff hOff leafTy hLeaf hSz]
  cases tyIsUninhabited layouts leafTy <;>
    cases Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
      (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
        (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) <;>
    simp

/-- **Offset-0 decoding of unions materialized from bytes.** An inhabited field of size `n + 1` of
the union decoded from the canonical image `img` reads `decodeTypedValueFromBytes` of
`img.take (n + 1)`, as `crates/anneal-mir`'s `decode_mir_value` / `decode_union_value` decode the
field at offset `0`. -/
theorem readDecodedUnion_posField_offset0
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (idx count : Nat) (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count) (hInhab : l.isUninhabited = false)
    (hIdx : idx < count)
    (img : List AbstractByte) (hLen : img.length = l.size.bytes)
    (hCanon : ∀ b ∈ img, RawOverlayCanonical b)
    (n : Nat)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some (n + 1))
    (hFieldInhab : tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = false)
    (hLe : n + 1 ≤ img.length) :
    ∃ fs,
      decodeUnionBytesWithCountOpt layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx
          count img = some (.aggregate 0 fs) ∧
      readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fs) baseTy
          [.field idx fieldTy] =
        match decodeTypedValueFromBytes defaultCodecFuel layouts
            (unionFieldReadTy localDecls layouts l idx fieldTy) (img.take (n + 1)) with
        | some v => .ok v
        | none => .ub := by
  obtain ⟨fs, hDec, hEnc, hUnits⟩ :=
    decodeUnionBytes_roundtrip layouts _ l count img hLookup hInhab hFields hLen hCanon
  have hK := tyByteSize_succ_kind localDecls layouts _ n hSz
  rw [unionFieldReadTy_kind] at hK
  refine ⟨fs, hDec, ?_⟩
  rw [readUnion_posField_offset0 locals localDecls layouts baseTy fieldTy fs idx count l d args hKind
    hLookup hFields hIdx (Or.inr (Or.inr ⟨hUnits idx hIdx, hK.1, hK.2⟩)) img hEnc n hSz hLe,
    hFieldInhab]

/-- **Trailing bytes are ignored.** For a union decoded from `fieldBytes ++ pad`, an inhabited
field of size `fieldBytes.length` reads `fieldBytes` alone: the bytes `[fieldSz, unionSz)`
(`.uninit` padding or anything else) never affect the read. -/
theorem readDecodedUnion_trailing_bytes_ignored
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (idx count : Nat) (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count) (hInhab : l.isUninhabited = false)
    (hIdx : idx < count)
    (fieldBytes pad : List AbstractByte) (hLen : (fieldBytes ++ pad).length = l.size.bytes)
    (hCanon : ∀ b ∈ fieldBytes ++ pad, RawOverlayCanonical b)
    (n : Nat) (hFb : fieldBytes.length = n + 1)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some (n + 1))
    (hFieldInhab : tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = false) :
    ∃ fs,
      decodeUnionBytesWithCountOpt layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx
          count (fieldBytes ++ pad) = some (.aggregate 0 fs) ∧
      readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fs) baseTy
          [.field idx fieldTy] =
        match decodeTypedValueFromBytes defaultCodecFuel layouts
            (unionFieldReadTy localDecls layouts l idx fieldTy) fieldBytes with
        | some v => .ok v
        | none => .ub := by
  have hLe : n + 1 ≤ (fieldBytes ++ pad).length := by
    rw [List.length_append, hFb]; exact Nat.le_add_right _ _
  have hTake : (fieldBytes ++ pad).take (n + 1) = fieldBytes := by
    rw [← hFb]; exact List.take_left
  have h := readDecodedUnion_posField_offset0 locals localDecls layouts baseTy fieldTy idx count l d args
    hKind hLookup hFields hInhab hIdx (fieldBytes ++ pad) hLen hCanon n hSz hFieldInhab hLe
  rw [hTake] at h
  exact h

/-! ### Section 6d: `kani#5176` — `[(); N]` arms of uninitialized unions -/

/-- `replicateValue count v` has `count` slots. -/
theorem length_replicateValue : ∀ (count : Nat) (v : Value), length (replicateValue count v) = count
  | 0, _ => rfl
  | k + 1, v => by
    have ih := length_replicateValue k v
    unfold length at ih ⊢
    simp [replicateValue, ih]

/-- Inactive (`.unit`) slots are not counted as typed values. -/
theorem unionNonUnitTypedSlotCount_units :
    ∀ count : Nat, unionNonUnitTypedSlotCount count (replicateValue count .unit) = 0
  | 0 => rfl
  | k + 1 => by
    simp only [replicateValue, unionNonUnitTypedSlotCount, unionNonUnitTypedSlotCount_units k]

/-- A union value with only inactive slots needs no consistency check. -/
theorem unionNeedsConsistencyCheck_units (count : Nat) :
    unionNeedsConsistencyCheck count (replicateValue count .unit) = false := by
  unfold unionNeedsConsistencyCheck
  rw [length_replicateValue, unionNonUnitTypedSlotCount_units]
  have h1 : Nat.blt count count = false := by
    cases h : Nat.blt count count with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self count)
  rw [h1]
  rfl

/-- Uninitialized bytes carry no provenance. -/
theorem abstractBytesHaveProv_replicate_uninit :
    ∀ n : Nat, abstractBytesHaveProv (List.replicate n AbstractByte.uninit) = false
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ]
    exact abstractBytesHaveProv_replicate_uninit n

/-- Integers never decode from uninitialized bytes. -/
theorem decodeTypedValueFromBytes_int_uninit (layouts : LayoutTable) (ty : Ty) (n : Nat)
    (hInt : (∃ w, ty.kind = .uint w) ∨ (∃ w, ty.kind = .int w)) :
    decodeTypedValueFromBytes defaultCodecFuel layouts ty (List.replicate (n + 1) .uninit) = none := by
  have hP := abstractBytesHaveProv_replicate_uninit (n + 1)
  have hD : ∀ s, decodeScalarBytes (List.replicate (n + 1) AbstractByte.uninit) s = none := by
    intro s
    rw [List.replicate_succ]
    unfold decodeScalarBytes
    simp [Nat.beq]
  rw [show defaultCodecFuel = 15 + 1 from rfl]
  rcases hInt with ⟨w, hw⟩ | ⟨w, hw⟩
  · unfold decodeTypedValueFromBytes
    simp only [normalizeCodecTy, hw]
    rw [hP]
    simp only []
    unfold decodeValueFromBytes
    simp only [hw, hD]
    split <;> (try rfl)
    split <;> rfl
  · unfold decodeTypedValueFromBytes
    simp only [normalizeCodecTy, hw]
    rw [hP]
    simp only []
    unfold decodeValueFromBytes
    simp only [hw, hD]
    split <;> (try rfl)
    split <;> rfl

/-- **`kani#5176`, 0-byte arm.** From all-`.uninit` storage (every slot inactive, as for
`MaybeUninit::uninit()` or a union decoded from uninitialized bytes), an inhabited 0-byte arm such
as `[(); N]` reads its canonical value. -/
theorem kani5176_uninit_storage_zst_field
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (idx count : Nat) (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hNU : fieldTy.kind ≠ .tuple []) (hNF : ∀ p a, fieldTy.kind ≠ .fnDef p a)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some 0)
    (hInh : tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 (replicateValue count .unit))
        baseTy [.field idx fieldTy] =
      .ok (zeroByteValue layouts (unionFieldReadTy localDecls layouts l idx fieldTy)) := by
  rw [readUnion_zeroByte_root locals localDecls layouts baseTy fieldTy (replicateValue count .unit) idx
    count l d args hKind hLookup hFields hIdx (Or.inl (unionNeedsConsistencyCheck_units count))
    (Or.inr (Or.inr ⟨get?_replicateValue count idx .unit hIdx, hNU, hNF⟩)) hSz, hInh]

/-- **`kani#5176`, 0-byte sub-place of an arm (`[(); N][i]`).** From all-`.uninit` storage, any
statically bounded inhabited 0-byte sub-place not passing through an uninhabited container (such as
element `z[i]` of `z : [(); N]`) reads its canonical value without touching the uninitialized bytes. -/
theorem kani5176_uninit_storage_zst_subProj
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (idx count : Nat) (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hNU : fieldTy.kind ≠ .tuple []) (hNF : ∀ p a, fieldTy.kind ≠ .fnDef p a)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = true)
    (subOff : Nat)
    (hOff : projectionChainByteOffset? layouts (some (unionFieldReadTy localDecls layouts l idx fieldTy))
      none none 0 localDecls (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) =
        some subOff)
    (leafTy : Ty)
    (hLeaf : resolveProjectedTyResolved localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = some leafTy)
    (hSz : tyByteSize localDecls layouts leafTy = some 0)
    (hLeafInh : tyIsUninhabited layouts leafTy = false)
    (hContInh :
      Bool.or (tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy))
        (subProjTouchesUninhabited localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
          (normalizeSubsliceProjections (stripTransparentProjections idxResolved))) = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 (replicateValue count .unit))
        baseTy (.field idx fieldTy :: p :: ps) =
      .ok (zeroByteValue layouts leafTy) := by
  rw [readUnion_zeroByte_subProj locals localDecls layouts baseTy fieldTy (replicateValue count .unit)
    idx count l d args hKind hLookup hFields hIdx (Or.inl (unionNeedsConsistencyCheck_units count))
    (Or.inr (Or.inr ⟨get?_replicateValue count idx .unit hIdx, hNU, hNF⟩)) p ps idxResolved hRes
    hBounds subOff hOff leafTy hLeaf hSz, hLeafInh, hContInh]

/-- **`kani#5176`, positive-sized scalar arm.** From all-`.uninit` storage, an integer arm faults
with `.ub`: its bytes are uninitialized. -/
theorem kani5176_uninit_storage_int_field_ub
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (idx count : Nat) (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count) (hInhab : l.isUninhabited = false)
    (hIdx : idx < count)
    (hInt : (∃ w, fieldTy.kind = .uint w) ∨ (∃ w, fieldTy.kind = .int w))
    (n : Nat)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTy localDecls layouts l idx fieldTy) = some (n + 1))
    (hLe : n + 1 ≤ l.size.bytes) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 (replicateValue count .unit))
        baseTy [.field idx fieldTy] = .ub := by
  have hEnc := encodeByLayoutIdxAux_units layouts _ l count hLookup hInhab hFields
  have hK := tyByteSize_succ_kind localDecls layouts _ n hSz
  rw [unionFieldReadTy_kind] at hK
  have hLe' : n + 1 ≤ (replicateUninitBytes l.size.bytes).length := by
    rw [length_replicateUninitBytes]; exact hLe
  rw [readUnion_posField_offset0 locals localDecls layouts baseTy fieldTy (replicateValue count .unit)
    idx count l d args hKind hLookup hFields hIdx
    (Or.inr (Or.inr ⟨get?_replicateValue count idx .unit hIdx, hK.1, hK.2⟩)) _ hEnc n hSz hLe']
  have hTake : (replicateUninitBytes l.size.bytes).take (n + 1) = List.replicate (n + 1) .uninit := by
    rw [replicateUninitBytes_eq_replicate, List.take_replicate, Nat.min_eq_left hLe]
  have hIntR : (∃ w, (unionFieldReadTy localDecls layouts l idx fieldTy).kind = .uint w) ∨
      (∃ w, (unionFieldReadTy localDecls layouts l idx fieldTy).kind = .int w) := by
    rw [unionFieldReadTy_kind]; exact hInt
  cases tyIsUninhabited layouts (unionFieldReadTy localDecls layouts l idx fieldTy)
  · simp only []; rw [hTake, decodeTypedValueFromBytes_int_uninit layouts _ n hIntR]
  · rfl

/-! ### Section 6e: Kernel-checked witnesses on `rustc`-shaped layout tables (`V2026_06_01`) -/

/-- `core::convert::Infallible` (`enum Infallible {}`). -/
def wInfK : RigidTy := .adt "core::convert::Infallible" []

/-- A user-defined empty enum `enum CustomVoid {}` (known uninhabited only via `TypeLayout.isUninhabited`,
not by a hardcoded `DefPath` in `rigidTyIsUninhabited`). -/
def wVoidK : RigidTy := .adt "CustomVoid" []

/-- A 0-byte, 1-aligned `TypeLayout` of the given shape. -/
def wZstLayout (fields : FieldsShape) (variants : VariantsShape) (uninhabited : Bool)
    (fls : List Nat) : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := fields, variants := variants,
    isUninhabited := uninhabited, fieldLayouts := fls }

/-- `u32`. -/
def wU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `(Infallible, u32)`: a 4-byte uninhabited tuple whose `.1 : u32` field sits at byte offset `0`. -/
def wPairU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
    variants := .single 0, isUninhabited := true, fieldLayouts := [3, 0] }

/-- The 4-byte union `U` with thirteen fields (layout indices `0..=12`). -/
def wULayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 13,
    variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] }

def wLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [
      wU32Layout,
      wZstLayout (.arbitrary [] []) (.single 0) false [],
      wZstLayout .primitive .empty true [],
      wZstLayout .primitive .empty true [],
      wZstLayout (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) (.single 0) true [3, 1],
      wZstLayout (.array ⟨0⟩ 1) (.single 0) true [3],
      wZstLayout (.arbitrary [⟨0⟩] [0]) (.single 0) true [3],
      wZstLayout (.arbitrary [] []) (.single 0) false [],
      wZstLayout (.array ⟨0⟩ 0) (.single 0) false [3],
      wZstLayout (.array ⟨0⟩ 3) (.single 0) false [1],
      wZstLayout (.union 2) (.single 0) false [4, 1],
      wPairU32Layout,
      wZstLayout (.array ⟨0⟩ 2) (.single 0) false [10],
      wULayout] }

def wU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def wUnitTy : Ty := { kind := .tuple [], layoutIdx := 1 }
def wNeverTy : Ty := { kind := .never, layoutIdx := 2 }
def wInfTy : Ty := { kind := wInfK, layoutIdx := 3 }
def wPairTy : Ty := { kind := .tuple [wInfK, .tuple []], layoutIdx := 4 }
def wVoidPairUnresolvedTy : Ty := { kind := .tuple [wVoidK, .tuple []], layoutIdx := 0 }
def wArr1Ty : Ty := { kind := .array wInfK 1, layoutIdx := 5 }
def wMdTy : Ty := { kind := .adt "core::mem::ManuallyDrop" [wInfK], layoutIdx := 6 }
def wPhTy : Ty := { kind := .adt "core::marker::PhantomData" [wInfK], layoutIdx := 7 }
def wArr0Ty : Ty := { kind := .array wInfK 0, layoutIdx := 8 }
def wZArrTy : Ty := { kind := .array (.tuple []) 3, layoutIdx := 9 }
def wVTy : Ty := { kind := .adt "V" [], layoutIdx := 10 }
def wPairU32Ty : Ty := { kind := .tuple [wInfK, .uint .u32], layoutIdx := 11 }
def wArr2VTy : Ty := { kind := .array (.adt "V" []) 2, layoutIdx := 12 }
def wUTy : Ty := { kind := .adt "U" [], layoutIdx := 13 }

def wDecls : List LocalDecl := [{ mutability := .mut, ty := wUTy, debugName := none }]

/-- `U { val: 42 }`: slot `0` holds the active `u32`, every other slot is inactive. -/
def wUVal : Value := .aggregate 0 (.scalar ⟨42, 4⟩ :: replicateValue 12 .unit)

/-- `U { val: 42 }` with explicit `Value.uninit` in every inactive slot. -/
def wUValUninitSlots : Value := .aggregate 0 (.scalar ⟨42, 4⟩ :: replicateValue 12 .uninit)

/-- **`kani#5159` witness reads (distinguishing uninhabited leaves `.ub` from inhabited leaves
through uninhabited containers `.unsupported`).** On `U { val: 42 }`:
- Active `u32` and inhabited 0-byte fields (`()`, `PhantomData<Infallible>`, `[Infallible; 0]`,
  `[(); 3]`, `[(); 3][2]`, `V`, `V.y`) read their values (`.ok`);
- Uninhabited leaf reads (`!`, `Infallible`, `pair` root, `arr1` root, `arr1[0]`, `md` root,
  `md.value`, `V.p`, `pair_u32` root, `pair_u32.0`, `arr2_v[0..-1][0].p.0`) fault with `.ub`;
- Inhabited-leaf reads through uninhabited containers (`pair.1`, `V.p.1`, `pair_u32.1`,
  `arr2_v[0..-1][0].p.1`) fail closed with `.unsupported` (and are explicitly proved `≠ .ub`). -/
theorem kani5159_witness_reads :
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 0 wU32Ty] =
        .ok (.scalar ⟨42, 4⟩) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 1 wUnitTy] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 2 wNeverTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 3 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 4 wPairTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 4 wPairTy, .field 1 wUnitTy] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 4 wPairTy, .field 1 wUnitTy] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 5 wArr1Ty] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 5 wArr1Ty, .constantIndex 0 1 false] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 6 wMdTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 6 wMdTy, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 7 wPhTy] =
        .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 8 wArr0Ty] =
        .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 9 wZArrTy] =
        .ok (.aggregate 0 [.unit, .unit, .unit]) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 9 wZArrTy, .constantIndex 2 3 false] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 10 wVTy] =
        .ok (.aggregate 0 [.unit, .unit]) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 1 wUnitTy] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 0 wPairTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 0 wPairTy, .field 1 wUnitTy] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 0 wPairTy, .field 1 wUnitTy] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 11 wPairU32Ty] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 11 wPairU32Ty, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 11 wPairU32Ty, .field 1 wU32Ty] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 11 wPairU32Ty, .field 1 wU32Ty] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 12 wArr2VTy, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 12 wArr2VTy, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 12 wArr2VTy, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] ≠ .ub := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, (by intro h; cases h), rfl, rfl, rfl, (by intro h; cases h), rfl, rfl,
    (by intro h; cases h)⟩

/-- Witness that explicit `Value.uninit` inactive slots agree with `.unit` placeholder inactive slots:
inhabited 0-byte fields read `.ok`, uninhabited leaves fault `.ub`, and inhabited leaves through
uninhabited containers fail closed `.unsupported`. -/
theorem kani5159_witness_uninit_slots :
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy [.field 0 wU32Ty] =
        .ok (.scalar ⟨42, 4⟩) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy [.field 1 wUnitTy] =
        .ok .unit ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy [.field 3 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy [.field 7 wPhTy] =
        .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy
        [.field 4 wPairTy, .field 1 wUnitTy] = .unsupported := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of the general field-root, `Value.uninit` slot, and sub-projection theorems on `wUVal`. -/
theorem kani5159_witness_general_instances :
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 0 wU32Ty] =
      .ok (.scalar ⟨42, 4⟩) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 1 wUnitTy] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 3 wInfTy] = .ub ∧
    tyIsUninhabited wLayouts (unionFieldReadTy wDecls wLayouts wULayout 3 wInfTy) = true ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 4 wPairTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 7 wPhTy] =
      .ok (zeroByteValue wLayouts wPhTy) ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 0 wPairTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 11 wPairU32Ty, .field 1 wU32Ty] = .unsupported ∧
    (readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 10 wVTy, .field 0 wPairTy, .field 1 wUnitTy] = .unsupported ↔
      tyIsUninhabited wLayouts wUnitTy = false ∧
        Bool.or (tyIsUninhabited wLayouts wVTy)
          (subProjTouchesUninhabited wDecls wLayouts wVTy [.field 0 wPairTy, .field 1 wUnitTy]) = true) ∧
    tyIsUninhabited wLayouts wVTy = false ∧ tyIsUninhabited wLayouts wUnitTy = false ∧
    subProjTouchesUninhabited wDecls wLayouts wVTy [.field 0 wPairTy, .field 1 wUnitTy] = true ∧
    subProjTouchesUninhabited wDecls wLayouts wArr2VTy
      [.subslice 0 1 true, .constantIndex 0 1 false,
       .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] = true ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUValUninitSlots wUTy [.field 7 wPhTy] =
      .ok (zeroByteValue wLayouts wPhTy) := by
  have hSlot : ∀ i, 1 ≤ i → i < 13 → ∀ k : RigidTy, k ≠ .tuple [] → (∀ p a, k ≠ .fnDef p a) →
      UnionSlotInactive (.scalar ⟨42, 4⟩ :: replicateValue 12 .unit) i k := by
    intro i h1 h2 k hNU hNF
    refine Or.inr (Or.inr ⟨?_, hNU, hNF⟩)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    unfold get?
    simpa using get?_replicateValue 12 j .unit (by omega)
  have hInfUb : readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy [.field 3 wInfTy] = .ub :=
    kani5159_uninhabited_field_root_ub [] wDecls wLayouts wUTy wInfTy _ 3 13 wULayout "U" [] rfl rfl
      rfl (by decide) (Or.inl rfl) (hSlot 3 (by decide) (by decide) _ (by intro h; cases h) (by intro p a h; cases h))
      rfl
  refine ⟨?_, ?_, hInfUb, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact readUnion_activeSlot_root [] wDecls wLayouts wUTy wU32Ty _ 0 13 wULayout "U" [] rfl rfl rfl
      (by decide) rfl (.scalar ⟨42, 4⟩) rfl (by intro h; cases h) (by intro h; cases h) rfl
  · exact readUnion_unitKind_unitSlot_root [] wDecls wLayouts wUTy wUnitTy _ 1 13 wULayout "U" [] rfl
      rfl rfl (by decide) (Or.inl rfl) rfl (Or.inl rfl)
  · exact readUnion_zeroByte_root_ub_imp_uninhabited [] wDecls wLayouts wUTy wInfTy _ 3 13 wULayout
      "U" [] rfl rfl rfl (by decide) rfl (by intro _ _ h; cases h) hInfUb
  · exact kani5159_uninhabited_field_root_ub [] wDecls wLayouts wUTy wPairTy _ 4 13 wULayout "U" [] rfl
      rfl rfl (by decide) (Or.inl rfl)
      (hSlot 4 (by decide) (by decide) _ (by intro h; cases h) (by intro p a h; cases h)) rfl
  · exact readUnion_zeroByte_root [] wDecls wLayouts wUTy wPhTy _ 7 13 wULayout "U" [] rfl rfl rfl
      (by decide) (Or.inl rfl) (hSlot 7 (by decide) (by decide) _ (by intro h; cases h) (by intro p a h; cases h))
      rfl
  · exact kani5159_uninhabited_subProj_ub [] wDecls wLayouts wUTy wVTy _ 10 13 wULayout "U" [] rfl rfl rfl
      (by decide) (Or.inl rfl)
      (hSlot 10 (by decide) (by decide) _ (by intro h; cases h) (by intro p a h; cases h))
      (.field 0 wPairTy) [] [.field 0 wPairTy] rfl rfl 0 rfl wPairTy rfl rfl
  · exact kani5159_inhabitedLeaf_through_uninhabitedContainer_subProj_unsupported [] wDecls wLayouts
      wUTy wPairU32Ty _ 11 13 wULayout "U" [] rfl rfl rfl (by decide) (Or.inl rfl)
      (hSlot 11 (by decide) (by decide) _ (by intro h; cases h) (by intro p a h; cases h))
      (.field 1 wU32Ty) [] [.field 1 wU32Ty] rfl rfl 0 rfl wU32Ty rfl rfl rfl
  · exact (readUnion_zeroByte_subProj_iff [] wDecls wLayouts wUTy wVTy _ 10 13 wULayout "U" [] rfl rfl
      rfl (by decide) (Or.inl rfl) (hSlot 10 (by decide) (by decide) _ (by intro h; cases h)
        (by intro p a h; cases h))
      (.field 0 wPairTy) [.field 1 wUnitTy] [.field 0 wPairTy, .field 1 wUnitTy] rfl rfl 0 rfl wUnitTy
      rfl rfl).2.1
  · exact readUnion_uninitSlot_zeroByte_root [] wDecls wLayouts wUTy wPhTy _ 7 13 wULayout "U" [] rfl
      rfl rfl (by decide) (Or.inl rfl) rfl rfl

/-! `kani#5176` witness: `#[repr(C)] union PU { payload: Padded, x: u32, z: [(); 2] }` with
`#[repr(C)] struct Padded { a: u8, b: u32 }` (bytes `1..4` of `payload` are padding). -/

def wU8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def wPaddedLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [14, 0] }

def wPULayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 3, variants := .single 0,
    isUninhabited := false, fieldLayouts := [15, 0, 16] }

def wLayouts5176 : LayoutTable :=
  { wLayouts with
    entries := wLayouts.entries ++
      [wU8Layout, wPaddedLayout, wZstLayout (.array ⟨0⟩ 2) (.single 0) false [1], wPULayout] }

def wU8Ty : Ty := { kind := .uint .u8, layoutIdx := 14 }
def wPaddedTy : Ty := { kind := .adt "Padded" [], layoutIdx := 15 }
def wZ2Ty : Ty := { kind := .array (.tuple []) 2, layoutIdx := 16 }
def wPUTy : Ty := { kind := .adt "PU" [], layoutIdx := 17 }
def wDecls5176 : List LocalDecl := [{ mutability := .mut, ty := wPUTy, debugName := none }]

/-- `PU { payload: Padded { a: 1, b: 2 } }`. -/
def wPUPayload : Value :=
  .aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 4⟩], .unit, .unit]

/-- **`kani#5176` witness reads.** From all-`.uninit` storage of `PU` (exactly the decoding of eight
uninitialized bytes), `z` and `z[1]` read their values while `x : u32` and `payload` fault; with
`payload` active, `z`, `z[1]`, and `payload.b` read their values while `x` faults on the
padding bytes `1..4` of `payload`; on the bytes of `write_bytes(_, 0x5a, 8)`, `x` reads
`0x5a5a5a5a`. -/
theorem kani5176_witness_reads :
    decodeUnionBytesWithCountOpt wLayouts5176 17 3 (List.replicate 8 .uninit) =
        some (.aggregate 0 (replicateValue 3 .unit)) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 2 wZ2Ty] = .ok (.aggregate 0 [.unit, .unit]) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 2 wZ2Ty, .constantIndex 1 2 false] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 1 wU32Ty] = .ub ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 0 wPaddedTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 wPUPayload wPUTy [.field 2 wZ2Ty] =
        .ok (.aggregate 0 [.unit, .unit]) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 wPUPayload wPUTy
        [.field 2 wZ2Ty, .constantIndex 1 2 false] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 wPUPayload wPUTy
        [.field 0 wPaddedTy, .field 1 wU32Ty] = .ok (.scalar ⟨2, 4⟩) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 wPUPayload wPUTy [.field 1 wU32Ty] = .ub ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176
        (.aggregate 0 (replicateValue 3 .unit ++
          [.aggregate 0 (encodeRawAbstractByteVals (List.replicate 8 (.init 0x5a none)))]))
        wPUTy [.field 1 wU32Ty] = .ok (.scalar ⟨0x5a5a5a5a, 4⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Non-vacuity of the `kani#5176` and trailing-byte theorems on `PU`. -/
theorem kani5176_witness_general_instances :
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 2 wZ2Ty] = .ok (zeroByteValue wLayouts5176 wZ2Ty) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 2 wZ2Ty, .constantIndex 1 2 false] = .ok (zeroByteValue wLayouts5176 wUnitTy) ∧
    readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 (replicateValue 3 .unit))
        wPUTy [.field 1 wU32Ty] = .ub ∧
    ∃ fs,
      decodeUnionBytesWithCountOpt wLayouts5176 17 3
          (List.replicate 4 (.init 0x5a none) ++ List.replicate 4 .uninit) = some (.aggregate 0 fs) ∧
      readProjectedValueUnionAware [] wDecls5176 wLayouts5176 (.aggregate 0 fs) wPUTy
          [.field 1 wU32Ty] =
        match decodeTypedValueFromBytes defaultCodecFuel wLayouts5176 wU32Ty
            (List.replicate 4 (.init 0x5a none)) with
        | some v => .ok v
        | none => .ub := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact kani5176_uninit_storage_zst_field [] wDecls5176 wLayouts5176 wPUTy wZ2Ty 2 3 wPULayout "PU" []
      rfl rfl rfl (by decide) (by intro h; cases h) (by intro p a h; cases h) rfl rfl
  · exact kani5176_uninit_storage_zst_subProj [] wDecls5176 wLayouts5176 wPUTy wZ2Ty 2 3 wPULayout "PU"
      [] rfl rfl rfl (by decide) (by intro h; cases h) (by intro p a h; cases h)
      (.constantIndex 1 2 false) [] [.constantIndex 1 2 false] rfl rfl 0 rfl wUnitTy rfl rfl rfl rfl
  · exact kani5176_uninit_storage_int_field_ub [] wDecls5176 wLayouts5176 wPUTy wU32Ty 1 3 wPULayout "PU"
      [] rfl rfl rfl rfl (by decide) (Or.inl ⟨.u32, rfl⟩) 3 rfl (by decide)
  · exact readDecodedUnion_trailing_bytes_ignored [] wDecls5176 wLayouts5176 wPUTy wU32Ty 1 3 wPULayout
      "PU" [] rfl rfl rfl rfl (by decide) _ _ rfl
      (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> trivial) 3 rfl rfl rfl

/-- **`kani#5159` at the MIR place-read level.** `evalPlaceRead` (the read behind
`copy`/`move` operands) of `wUVal`'s uninhabited leaves (`Infallible`, `pair` root, `md.value`,
`pair_u32.0`) faults with `.ub`; inhabited leaves through uninhabited containers (`pair.1`, `V.p.1`,
`pair_u32.1`) fail closed with `.unsupported` (never `.ub`); active and inhabited 0-byte fields
read their values. -/
theorem kani5159_witness_evalPlaceRead :
    evalPlaceRead [.init wUVal] ⟨0, [.field 0 wU32Ty]⟩ [] [] wLayouts [] wDecls =
      .ok (.scalar ⟨42, 4⟩) [.init wUVal] ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 1 wUnitTy]⟩ [] [] wLayouts [] wDecls =
      .ok .unit [.init wUVal] ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 3 wInfTy]⟩ [] [] wLayouts [] wDecls = .ub ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 4 wPairTy]⟩ [] [] wLayouts [] wDecls = .ub ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 4 wPairTy, .field 1 wUnitTy]⟩ [] [] wLayouts []
      wDecls = .unsupported ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 6 wMdTy, .field 0 wInfTy]⟩ [] [] wLayouts []
      wDecls = .ub ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 10 wVTy, .field 0 wPairTy]⟩ [] []
      wLayouts [] wDecls = .ub ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 10 wVTy, .field 0 wPairTy, .field 1 wUnitTy]⟩ [] []
      wLayouts [] wDecls = .unsupported ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 11 wPairU32Ty, .field 0 wInfTy]⟩ [] []
      wLayouts [] wDecls = .ub ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 11 wPairU32Ty, .field 1 wU32Ty]⟩ [] []
      wLayouts [] wDecls = .unsupported ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 7 wPhTy]⟩ [] [] wLayouts [] wDecls =
      .ok (.aggregate 0 []) [.init wUVal] ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 9 wZArrTy, .constantIndex 2 3 false]⟩ [] [] wLayouts []
      wDecls = .ok .unit [.init wUVal] ∧
    evalPlaceRead [.init wUVal] ⟨0, [.field 10 wVTy, .field 1 wUnitTy]⟩ [] [] wLayouts [] wDecls =
      .ok .unit [.init wUVal] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! `readUnion_zeroByte_fieldRoot` witness: `enum E { A(()), B(Infallible) }`, zero-sized because
`B` is absent (laid out as `A`'s fields), in `union UE { e: E, x: u32 }`. A downcast is not
statically bounded, so the read decodes `e` from zero bytes and continues from there. -/

/-- `E`: the present variant `A` with its `()` field at offset `0`. -/
def wELayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩] [0],
    variants := .single 0, isUninhabited := false, fieldLayouts := [1] }

/-- `UE`: a 4-byte union of `e : E` (layout `14`) and `x : u32` (layout `0`). -/
def wUELayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 2, variants := .single 0,
    isUninhabited := false, fieldLayouts := [14, 0] }

/-- `wLayouts` extended with `E` (`14`) and `UE` (`15`). -/
def wLayoutsE : LayoutTable :=
  { wLayouts with entries := wLayouts.entries ++ [wELayout, wUELayout] }

def wETy : Ty := { kind := .adt "E" [], layoutIdx := 14 }
def wUETy : Ty := { kind := .adt "UE" [], layoutIdx := 15 }
def wDeclsE : List LocalDecl := [{ mutability := .mut, ty := wUETy, debugName := none }]

/-- `UE { x: 7 }`. -/
def wUEVal : Value := .aggregate 0 [.unit, .scalar ⟨7, 4⟩]

theorem kani5159_witness_fieldRoot_downcast :
    readProjectedValueUnionAware [] wDeclsE wLayoutsE wUEVal wUETy
        [.field 0 wETy, .downcast (some "A") 0, .field 0 wUnitTy] = .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDeclsE wLayoutsE wUEVal wUETy
        [.field 0 wETy, .downcast (some "B") 1, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDeclsE wLayoutsE wUEVal wUETy
        [.field 0 wETy, .downcast (some "A") 0, .field 0 wUnitTy] =
      match tyIsUninhabited wLayoutsE wETy with
      | true =>
        match resolveProjectedTyResolved wDeclsE wLayoutsE wETy
            (normalizeSubsliceProjections (stripTransparentProjections
              [.downcast (some "A") 0, .field 0 wUnitTy])) with
        | some leafTy =>
          match tyIsUninhabited wLayoutsE leafTy with
          | true => .ub
          | false => .unsupported
        | none => .unsupported
      | false =>
        readProjectedValueUnionAware [] wDeclsE wLayoutsE (zeroByteValue wLayoutsE wETy) wETy
          [.downcast (some "A") 0, .field 0 wUnitTy] := by
  refine ⟨rfl, rfl, ?_⟩
  exact readUnion_zeroByte_fieldRoot [] wDeclsE wLayoutsE wUETy wETy _ 0 2 wUELayout "UE" [] rfl rfl
    rfl (by decide) (Or.inl rfl) (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩)) rfl
    (.downcast (some "A") 0) [.field 0 wUnitTy] [.downcast (some "A") 0, .field 0 wUnitTy] rfl rfl

/-- **`arr2_v[0..-1][0].p.{0,1}` and `arr2_v[0..-1][0].y`, step by step.** The sub-projection after
`arr2_v` is not statically bounded: the `fromEnd = true` subslice's synthesized `[V; 1]` type has
no captured layout, so `checkStaticSubProjBounds` cannot reach `V`'s fields. The read therefore
takes the 0-byte field-root path (`readUnion_zeroByte_fieldRoot`): the inhabited `[V; 2]` is
decoded from zero bytes as two all-inactive `V` values, and the subslice and constant index select
one `V`. Inside `V`'s own union read:
- `p.0 : Infallible` has an uninhabited leaf -> `.ub` (`kani5159_uninhabited_subProj_ub`);
- `p.1 : ()` has an inhabited leaf through uninhabited `p : (CustomVoid, ())` -> `.unsupported`
  (`kani5159_inhabitedLeaf_through_uninhabitedContainer_subProj_unsupported`, never `.ub`);
- `y : ()` reads `.ok .unit`. -/
theorem kani5159_witness_arr2v_fieldRoot_path :
    checkStaticSubProjBounds wDecls wLayouts wArr2VTy
        (normalizeSubsliceProjections (stripTransparentProjections
          [.subslice 0 1 true, .constantIndex 0 1 false, .field 0 wVoidPairUnresolvedTy,
           .field 1 wUnitTy])) = false ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 12 wArr2VTy, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] =
      (match tyIsUninhabited wLayouts (unionFieldReadTy wDecls wLayouts wULayout 12 wArr2VTy) with
      | true =>
        match resolveProjectedTyResolved wDecls wLayouts
            (unionFieldReadTy wDecls wLayouts wULayout 12 wArr2VTy)
            (normalizeSubsliceProjections (stripTransparentProjections
              [.subslice 0 1 true, .constantIndex 0 1 false, .field 0 wVoidPairUnresolvedTy,
               .field 1 wUnitTy])) with
        | some leafTy =>
          match tyIsUninhabited wLayouts leafTy with
          | true => .ub
          | false => .unsupported
        | none => .unsupported
      | false =>
        readProjectedValueUnionAware [] wDecls wLayouts
          (zeroByteValue wLayouts (unionFieldReadTy wDecls wLayouts wULayout 12 wArr2VTy))
          (unionFieldReadTy wDecls wLayouts wULayout 12 wArr2VTy)
          [.subslice 0 1 true, .constantIndex 0 1 false, .field 0 wVoidPairUnresolvedTy,
           .field 1 wUnitTy]) ∧
    tyIsUninhabited wLayouts (unionFieldReadTy wDecls wLayouts wULayout 12 wArr2VTy) = false ∧
    zeroByteValue wLayouts wArr2VTy =
      .aggregate 0 [.aggregate 0 [.unit, .unit], .aggregate 0 [.unit, .unit]] ∧
    readProjectedValueUnionAware [] wDecls wLayouts (.aggregate 0 [.unit, .unit]) wVTy
        [.field 0 wVoidPairUnresolvedTy, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDecls wLayouts (.aggregate 0 [.unit, .unit]) wVTy
        [.field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls wLayouts (.aggregate 0 [.unit, .unit]) wVTy
        [.field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy] ≠ .ub ∧
    tyIsUninhabited wLayouts
      (unionFieldReadTy wDecls wLayouts (wZstLayout (.union 2) (.single 0) false [4, 1]) 0
        wVoidPairUnresolvedTy) = true ∧
    readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 12 wArr2VTy, .subslice 0 1 true, .constantIndex 0 1 false, .field 1 wUnitTy] =
      .ok .unit := by
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, (by intro h; cases h), rfl, rfl⟩
  · exact readUnion_zeroByte_fieldRoot [] wDecls wLayouts wUTy wArr2VTy _ 12 13 wULayout "U" [] rfl rfl
      rfl (by decide) (Or.inl rfl) (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩))
      rfl (.subslice 0 1 true)
      [.constantIndex 0 1 false, .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy]
      [.subslice 0 1 true, .constantIndex 0 1 false, .field 0 wVoidPairUnresolvedTy, .field 1 wUnitTy]
      rfl rfl
  · exact kani5159_uninhabited_subProj_ub [] wDecls wLayouts wVTy wVoidPairUnresolvedTy [.unit, .unit] 0 2
      (wZstLayout (.union 2) (.single 0) false [4, 1]) "V" [] rfl rfl rfl (by decide) (Or.inl rfl)
      (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩))
      (.field 0 wInfTy) [] [.field 0 wInfTy] rfl rfl 0 rfl wInfTy rfl rfl
  · exact kani5159_inhabitedLeaf_through_uninhabitedContainer_subProj_unsupported [] wDecls wLayouts
      wVTy wVoidPairUnresolvedTy [.unit, .unit] 0 2
      (wZstLayout (.union 2) (.single 0) false [4, 1]) "V" [] rfl rfl rfl (by decide) (Or.inl rfl)
      (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩))
      (.field 1 wUnitTy) [] [.field 1 wUnitTy] rfl rfl 0 rfl wUnitTy rfl rfl rfl

/-! Non-static fallthrough witness: `union UW { w0: W0, w4: W4, x: u32 }` with the uninhabited
single-variant enums `enum W0 { A(Infallible, ()) }` (0 bytes) and `enum W4 { A(Infallible, u32) }`
(4 bytes). A `.downcast` is never statically bounded (`checkStaticSubProjBounds = false`), so reads
through `w0` / `w4` take the field-root fallthrough on its `.some 0` and `.some (.succ _)` arms. -/

/-- `enum W0 { A(Infallible, ()) }`: a 0-byte single-variant uninhabited enum. -/
def wW0Layout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
    variants := .single 0, isUninhabited := true, fieldLayouts := [3, 1] }

/-- `enum W4 { A(Infallible, u32) }`: a 4-byte single-variant uninhabited enum. -/
def wW4Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
    variants := .single 0, isUninhabited := true, fieldLayouts := [3, 0] }

/-- `UW`: a 4-byte union of `w0 : W0` (layout `14`), `w4 : W4` (layout `15`), and `x : u32`. -/
def wUWLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 3, variants := .single 0,
    isUninhabited := false, fieldLayouts := [14, 15, 0] }

/-- `wLayouts` extended with `W0` (`14`), `W4` (`15`), and `UW` (`16`). -/
def wLayoutsW : LayoutTable :=
  { wLayouts with entries := wLayouts.entries ++ [wW0Layout, wW4Layout, wUWLayout] }

def wW0Ty : Ty := { kind := .adt "W0" [], layoutIdx := 14 }
def wW4Ty : Ty := { kind := .adt "W4" [], layoutIdx := 15 }
def wUWTy : Ty := { kind := .adt "UW" [], layoutIdx := 16 }
def wDeclsW : List LocalDecl := [{ mutability := .mut, ty := wUWTy, debugName := none }]

/-- `UW { x: 7 }`. -/
def wUWVal : Value := .aggregate 0 [.unit, .unit, .scalar ⟨7, 4⟩]

/-- **Non-static fallthrough through an uninhabited union field (`.some 0` and `.some (.succ _)`
arms).** Non-vacuity of `readUnion_uninhabited_nonEmpty_fallthrough_unsupported`: reading the
inhabited leaf `.1` of the uninhabited variant `A` through a `.downcast` fails closed with
`.unsupported` (never `.ub`) for both the 0-byte `W0` and the 4-byte `W4`, while reading the
uninhabited leaf `.0 : Infallible` on the same paths is a genuine leaf load and faults with `.ub`.
The `tyByteSize = none` arm is covered by `kani5159_v2026_08_01_nonEmpty_fallthrough_parity`. -/
theorem kani5159_witness_nonStatic_fallthrough :
    tyByteSize wDeclsW wLayoutsW wW0Ty = some 0 ∧
    tyByteSize wDeclsW wLayoutsW wW4Ty = some 4 ∧
    tyByteSize wDecls wLayouts wPairTy = none ∧
    checkStaticSubProjBounds wDeclsW wLayoutsW wW4Ty [.downcast (some "A") 0, .field 1 wU32Ty] =
      false ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy [.field 2 wU32Ty] =
      .ok (.scalar ⟨7, 4⟩) ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 0 wW0Ty, .downcast (some "A") 0, .field 1 wUnitTy] = .unsupported ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 0 wW0Ty, .downcast (some "A") 0, .field 1 wUnitTy] ≠ .ub ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 0 wW0Ty, .downcast (some "A") 0, .field 0 wInfTy] = .ub ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 1 wW4Ty, .downcast (some "A") 0, .field 1 wU32Ty] = .unsupported ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 1 wW4Ty, .downcast (some "A") 0, .field 1 wU32Ty] ≠ .ub ∧
    readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal wUWTy
        [.field 1 wW4Ty, .downcast (some "A") 0, .field 0 wInfTy] = .ub := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, (by intro h; cases h), rfl, ?_, (by intro h; cases h), rfl⟩
  · exact readUnion_uninhabited_nonEmpty_fallthrough_unsupported [] wDeclsW wLayoutsW wUWTy wW0Ty _ 0 3
      wUWLayout "UW" [] rfl rfl rfl (by decide) (Or.inl rfl)
      (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩)) rfl
      (.downcast (some "A") 0) [.field 1 wUnitTy] [.downcast (some "A") 0, .field 1 wUnitTy] rfl rfl
      (fun leafTy h => by
        obtain rfl := Option.some.inj (h.symm.trans (rfl : _ = some wUnitTy))
        rfl)
  · exact readUnion_uninhabited_nonEmpty_fallthrough_unsupported [] wDeclsW wLayoutsW wUWTy wW4Ty _ 1 3
      wUWLayout "UW" [] rfl rfl rfl (by decide) (Or.inl rfl)
      (Or.inr (Or.inr ⟨rfl, (by intro h; cases h), (by intro p a h; cases h)⟩)) rfl
      (.downcast (some "A") 0) [.field 1 wU32Ty] [.downcast (some "A") 0, .field 1 wU32Ty] rfl rfl
      (fun leafTy h => by
        obtain rfl := Option.some.inj (h.symm.trans (rfl : _ = some wU32Ty))
        rfl)

end V2026_06_01

/-! ### Section 6f: `V2026_08_01` Dialect Parity Witnesses -/

namespace V2026_08_01Parity

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirSemantics

def wInfK08 : RigidTy := .adt "core::convert::Infallible" []
def wVoidK08 : RigidTy := .adt "CustomVoid" []

def wZstLayout08 (fields : FieldsShape) (variants : VariantsShape) (uninhabited : Bool)
    (fls : List Nat) : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := fields, variants := variants,
    isUninhabited := uninhabited, fieldLayouts := fls }

def wU32Layout08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def wPairU32Layout08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
    variants := .single 0, isUninhabited := true, fieldLayouts := [3, 0] }

def wULayout08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 13,
    variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] }

def wLayouts08 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [
      wU32Layout08,
      wZstLayout08 (.arbitrary [] []) (.single 0) false [],
      wZstLayout08 .primitive .empty true [],
      wZstLayout08 .primitive .empty true [],
      wZstLayout08 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) (.single 0) true [3, 1],
      wZstLayout08 (.array ⟨0⟩ 1) (.single 0) true [3],
      wZstLayout08 (.arbitrary [⟨0⟩] [0]) (.single 0) true [3],
      wZstLayout08 (.arbitrary [] []) (.single 0) false [],
      wZstLayout08 (.array ⟨0⟩ 0) (.single 0) false [3],
      wZstLayout08 (.array ⟨0⟩ 3) (.single 0) false [1],
      wZstLayout08 (.union 2) (.single 0) false [4, 1],
      wPairU32Layout08,
      wZstLayout08 (.array ⟨0⟩ 2) (.single 0) false [10],
      wULayout08] }

def wU32Ty08 : Ty := { kind := .uint .u32, layoutIdx := 0 }
def wUnitTy08 : Ty := { kind := .tuple [], layoutIdx := 1 }
def wNeverTy08 : Ty := { kind := .never, layoutIdx := 2 }
def wInfTy08 : Ty := { kind := wInfK08, layoutIdx := 3 }
def wPairTy08 : Ty := { kind := .tuple [wInfK08, .tuple []], layoutIdx := 4 }
def wVoidPairUnresolvedTy08 : Ty := { kind := .tuple [wVoidK08, .tuple []], layoutIdx := 0 }
def wArr1Ty08 : Ty := { kind := .array wInfK08 1, layoutIdx := 5 }
def wMdTy08 : Ty := { kind := .adt "core::mem::ManuallyDrop" [wInfK08], layoutIdx := 6 }
def wPhTy08 : Ty := { kind := .adt "core::marker::PhantomData" [wInfK08], layoutIdx := 7 }
def wArr0Ty08 : Ty := { kind := .array wInfK08 0, layoutIdx := 8 }
def wZArrTy08 : Ty := { kind := .array (.tuple []) 3, layoutIdx := 9 }
def wVTy08 : Ty := { kind := .adt "V" [], layoutIdx := 10 }
def wPairU32Ty08 : Ty := { kind := .tuple [wInfK08, .uint .u32], layoutIdx := 11 }
def wArr2VTy08 : Ty := { kind := .array (.adt "V" []) 2, layoutIdx := 12 }
def wUTy08 : Ty := { kind := .adt "U" [], layoutIdx := 13 }

def wDecls08 : List LocalDecl := [{ mutability := .mut, ty := wUTy08, debugName := none }]
def wUVal08 : Value := .aggregate 0 (.scalar ⟨42, 4⟩ :: replicateValue 12 .unit)

/-- **Dialect parity (`V2026_08_01`) for `kani#5159` union reads.** Mirrors `kani5159_witness_reads`
on `Trusted.Rustc.V2026_08_01.MirSemantics.readProjectedValueUnionAware`: uninhabited leaf loads
fault with `.ub`, inhabited-leaf reads through uninhabited containers fail closed with
`.unsupported` (and `≠ .ub`), and inhabited 0-byte fields read their canonical values. -/
theorem kani5159_v2026_08_01_parity_reads :
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 0 wU32Ty08] =
        .ok (.scalar ⟨42, 4⟩) ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 1 wUnitTy08] =
        .ok .unit ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 2 wNeverTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 3 wInfTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 4 wPairTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 4 wPairTy08, .field 1 wUnitTy08] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 4 wPairTy08, .field 1 wUnitTy08] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 5 wArr1Ty08, .constantIndex 0 1 false] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 6 wMdTy08, .field 0 wInfTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 7 wPhTy08] =
        .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 8 wArr0Ty08] =
        .ok (.aggregate 0 []) ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 9 wZArrTy08, .constantIndex 2 3 false] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 10 wVTy08, .field 1 wUnitTy08] = .ok .unit ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 10 wVTy08, .field 0 wPairTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 10 wVTy08, .field 0 wPairTy08, .field 1 wUnitTy08] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 10 wVTy08, .field 0 wPairTy08, .field 1 wUnitTy08] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08 [.field 11 wPairU32Ty08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 11 wPairU32Ty08, .field 0 wInfTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 11 wPairU32Ty08, .field 1 wU32Ty08] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 11 wPairU32Ty08, .field 1 wU32Ty08] ≠ .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 12 wArr2VTy08, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy08, .field 0 wInfTy08] = .ub ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 12 wArr2VTy08, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy08, .field 1 wUnitTy08] = .unsupported ∧
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 12 wArr2VTy08, .subslice 0 1 true, .constantIndex 0 1 false,
         .field 0 wVoidPairUnresolvedTy08, .field 1 wUnitTy08] ≠ .ub := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, (by intro h; cases h), rfl, rfl, rfl, (by intro h; cases h), rfl, rfl,
    (by intro h; cases h)⟩

/-- **Dialect parity (`V2026_08_01`) for non-empty fallthrough guard.** A non-static downcast
sub-projection on an uninhabited union field fails closed with `.unsupported` (not `.ub`) in both
`V2026_06_01` and `V2026_08_01`. -/
theorem kani5159_v2026_08_01_nonEmpty_fallthrough_parity :
    readProjectedValueUnionAware [] wDecls08 wLayouts08 wUVal08 wUTy08
        [.field 4 wPairTy08, .downcast none 0, .field 1 wUnitTy08] = .unsupported ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValueUnionAware [] wDecls wLayouts wUVal wUTy
        [.field 4 wPairTy, .downcast none 0, .field 1 wUnitTy] = .unsupported :=
  ⟨rfl, rfl⟩

def wW0Ty08 : Ty := { kind := .adt "W0" [], layoutIdx := 14 }
def wW4Ty08 : Ty := { kind := .adt "W4" [], layoutIdx := 15 }
def wUWTy08 : Ty := { kind := .adt "UW" [], layoutIdx := 16 }
def wDeclsW08 : List LocalDecl := [{ mutability := .mut, ty := wUWTy08, debugName := none }]
def wUWVal08 : Value := .aggregate 0 [.unit, .unit, .scalar ⟨7, 4⟩]

/-- `wLayouts08` extended with `V2026_08_01` copies of `W0` (`14`), `W4` (`15`), and `UW` (`16`)
(see `kani5159_witness_nonStatic_fallthrough`). -/
def wLayoutsW08 : LayoutTable :=
  { wLayouts08 with
    entries := wLayouts08.entries ++ [
      { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
        variants := .single 0, isUninhabited := true, fieldLayouts := [3, 1] },
      { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1],
        variants := .single 0, isUninhabited := true, fieldLayouts := [3, 0] },
      { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory, fields := .union 3, variants := .single 0,
        isUninhabited := false, fieldLayouts := [14, 15, 0] }] }

/-- **Dialect parity (`V2026_08_01`) for the non-static fallthrough on the `.some 0` and
`.some (.succ _)` arms.** Mirrors `kani5159_witness_nonStatic_fallthrough`: inhabited leaves through
the uninhabited variants of `W0` / `W4` fail closed with `.unsupported`, uninhabited leaves fault
with `.ub`, in both dialects. -/
theorem kani5159_v2026_08_01_nonStatic_fallthrough_parity :
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 0 wW0Ty08, .downcast (some "A") 0, .field 1 wUnitTy08] = .unsupported ∧
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 0 wW0Ty08, .downcast (some "A") 0, .field 1 wUnitTy08] ≠ .ub ∧
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 0 wW0Ty08, .downcast (some "A") 0, .field 0 wInfTy08] = .ub ∧
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 1 wW4Ty08, .downcast (some "A") 0, .field 1 wU32Ty08] = .unsupported ∧
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 1 wW4Ty08, .downcast (some "A") 0, .field 1 wU32Ty08] ≠ .ub ∧
    readProjectedValueUnionAware [] wDeclsW08 wLayoutsW08 wUWVal08 wUWTy08
        [.field 1 wW4Ty08, .downcast (some "A") 0, .field 0 wInfTy08] = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal
        wUWTy [.field 0 wW0Ty, .downcast (some "A") 0, .field 1 wUnitTy] = .unsupported ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValueUnionAware [] wDeclsW wLayoutsW wUWVal
        wUWTy [.field 1 wW4Ty, .downcast (some "A") 0, .field 1 wU32Ty] = .unsupported :=
  ⟨rfl, (by intro h; cases h), rfl, rfl, (by intro h; cases h), rfl, rfl, rfl⟩

end V2026_08_01Parity

end Anneal.Mir.AdtAndControl.UnionZst
