/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.AdtAndControl
import MiniRustSpec.Correspondence.AnnealEval

/-!
# Projected `Deinit`: Anneal's `PartialShell` model and MiniRust's byte-slice `Uninit` store

`Trusted.MirSemantics.evalStmt` keeps the value of a projected `Deinit` place (it only checks that
the place is readable, `Statements.lean:2593-2600`), whereas MiniRust's `Statement::Deinit` stores
`AbstractByte::Uninit` over the place's byte slice and leaves every other byte intact.
`crates/anneal-mir`'s projected `Deinit` (formalized as
`Anneal.Mir.AdtAndControl.evalDeinitPlace`) explodes the local into a `PartialShell` whose
deinitialized part is `Uninit`. This module connects that model with MiniRust's actual memory
operation, without any flow-sensitive overwrite guard:

* `toAbstractBytes` reads Anneal's reference byte image (`ByteImage = List (Option UInt8)`:
  `none` is `Uninit`) as MiniRust abstract bytes (`Uninit` / provenance-free `Init b`);
* `toAbstractBytes_deinitBytes`: Anneal's `deinitBytes img off len` is exactly MiniRust's
  `write_subslice_at_index` of `len` `Uninit` bytes at `off` (`spliceAt`);
* `evalDeinitPlace_spec_minirust_store_simulation`: for a spec-laid-out ADT local whose MiniRust
  allocation holds the image of Anneal's initialized slot, MiniRust's `ConcurrentMemory::store` of
  the `Uninit` slice at the place's byte range (`pathRange`, which is also the synthetic sub-place
  range `subplaceAt` of `Anneal.Mir.AdtAndControl`) succeeds; its new allocation holds the image
  `deinitBytes img off len`, which represents Anneal's post-`Deinit` `PartialShell`
  (`Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation`), while every byte outside the
  slice is unchanged.
-/

namespace MiniRustSpec.Correspondence.DeinitBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- Anneal's reference byte image as MiniRust abstract bytes: `none` is `Uninit`, `some b` the
provenance-free initialized byte `b`. -/
def toAbstractBytes (img : Anneal.Mir.AdtAndControl.ByteImage) : List Byte :=
  img.map fun
    | none => .Uninit
    | some b => .Init b none

theorem length_toAbstractBytes (img : Anneal.Mir.AdtAndControl.ByteImage) :
    (toAbstractBytes img).length = img.length := by
  simp [toAbstractBytes]

/-- **Anneal's `deinitBytes` is MiniRust's `Uninit` slice store (`toAbstractBytes_deinitBytes`)**:
writing `Uninit` over `[off, off + len)` of an image in Anneal's reference model is MiniRust's
`write_subslice_at_index` of `len` `Uninit` bytes at `off`. -/
theorem toAbstractBytes_deinitBytes (img : Anneal.Mir.AdtAndControl.ByteImage) (off len : Nat)
    (h : off + len ≤ img.length) :
    toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len) =
      (toAbstractBytes img).take off ++ List.replicate len .Uninit ++
        (toAbstractBytes img).drop (off + len) := by
  apply List.ext_getElem?
  intro i
  have hLA := length_toAbstractBytes img
  have hTake : ((toAbstractBytes img).take off).length = off := by
    rw [List.length_take, hLA]; omega
  have hAB : ((toAbstractBytes img).take off ++
      List.replicate len (Gen.AbstractByte.Uninit : Byte)).length = off + len := by
    rw [List.length_append, hTake, List.length_replicate]
  have hMap : ∀ j : Nat, (toAbstractBytes img)[j]? = img[j]?.map (fun
      | none => (Gen.AbstractByte.Uninit : Byte)
      | some b => .Init b none) := fun j => by simp only [toAbstractBytes, List.getElem?_map]
  by_cases hIn : off ≤ i ∧ i < off + len
  · have hD := Anneal.Mir.AdtAndControl.deinitBytes_getElem?_inside (img := img) hIn (by omega)
    have hLHS : (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        some .Uninit := by
      simp [toAbstractBytes, hD]
    rw [hLHS, List.getElem?_append_left (by rw [hAB]; omega),
      List.getElem?_append_right (by rw [hTake]; omega), hTake, List.getElem?_replicate]
    simp [show i - off < len by omega]
  · have hD := Anneal.Mir.AdtAndControl.deinitBytes_getElem?_outside (img := img) hIn
    have hLHS : (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        (toAbstractBytes img)[i]? := by
      rw [hMap]
      simp [toAbstractBytes, hD]
    rw [hLHS]
    rcases Nat.lt_or_ge i off with hlt | hge
    · rw [List.getElem?_append_left (by rw [hAB]; omega),
        List.getElem?_append_left (by rw [hTake]; omega), List.getElem?_take_of_lt hlt]
    · have hge' : off + len ≤ i := by omega
      rw [List.getElem?_append_right (by rw [hAB]; omega), hAB, List.getElem?_drop,
        show off + len + (i - (off + len)) = i by omega]

/-- **The `PartialShell` projected `Deinit` is MiniRust's byte-slice `Uninit` store
(`evalDeinitPlace_spec_minirust_store_simulation`)**: let an ADT local laid out by `spec` be
initialized in Anneal (`rootVal`) and represented by the byte image `img` (`SlotBytes`), and let
MiniRust's live allocation `a` for it hold `toAbstractBytes img`. For a projected place whose byte
range is `[off, off + len)` (`pathRange`, `len > 0`), Anneal's `evalDeinitPlace` and MiniRust's
`ConcurrentMemory::store` of `len` `Uninit` bytes at `a.addr + off` correspond exactly: the store
succeeds, the new allocation holds `toAbstractBytes (deinitBytes img off len)`, and that image
represents Anneal's post-`Deinit` slot, with every byte outside the slice unchanged. -/
theorem evalDeinitPlace_spec_minirust_store_simulation {ts : Bool}
    {slots slots' : List Anneal.Mir.PlaceAndRvalue.LocalSlotState} {place : Place}
    {rootVal : Value} {spec : Anneal.Mir.AdtAndControl.AdtLayoutSpec}
    (hWF : spec.WF) {v : Nat} {fs : List Anneal.Mir.AdtAndControl.FieldLayout}
    {children : List Anneal.Mir.AdtAndControl.ByteLayout} {size align : Nat}
    (hLay : Anneal.Mir.AdtAndControl.adtLayout? spec = some (size, align))
    (hVF : Anneal.Mir.AdtAndControl.variantFields spec v = some fs)
    (hPl : Anneal.Mir.AdtAndControl.SpecFieldsPlaced spec v fs)
    (hCh : Anneal.Mir.AdtAndControl.ChildrenFit fs children)
    (enc : Value → List UInt8) (img : Anneal.Mir.AdtAndControl.ByteImage)
    (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : Anneal.Mir.AdtAndControl.evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ Anneal.Mir.AdtAndControl.noDowncast place.projection = true)
    (hFits : size ≤ img.length)
    (hS : Anneal.Mir.AdtAndControl.SlotBytes enc img
      (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
      (.init rootVal))
    {off len : Nat}
    (hRange : Anneal.Mir.AdtAndControl.pathRange
      (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
      place.projection = some (off, len))
    (hLen : 0 < len)
    {cm : Gen.ConcurrentMemory BM} {p : Ptr} {id : Nat}
    (hp : p.provenance = some (⟨(id : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[id]? = some a) (hlive : a.live = true)
    (hData : a.data = toAbstractBytes img) (haddr : p.addr = a.addr + (off : Int))
    (al : Align) (hal : Align.is_aligned al p.addr = true) :
    (∃ st', slots'[place.local_]? = some st' ∧
      Anneal.Mir.AdtAndControl.SlotBytes enc (Anneal.Mir.AdtAndControl.deinitBytes img off len)
        (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
        (Anneal.Mir.AdtAndControl.slotStateToFieldSlot st')) ∧
    CM.store cm p (List.replicate len .Uninit) al .None =
      .ok { memory := { cm.memory with
              allocations := cm.memory.allocations.set id
                { a with data := toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len) } },
            accesses := cm.accesses ++ [⟨.Store, .None, p.addr, ⟨len⟩⟩] } ∧
    ∀ i, ¬ (off ≤ i ∧ i < off + len) →
      (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        (toAbstractBytes img)[i]? := by
  obtain ⟨hBound, st', hSt', hBytes, hOut⟩ :=
    Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation hWF hLay hVF hPl hCh enc img
      hRoot h hTag hFits hS hRange
  have hOI : off + len ≤ img.length := by omega
  have hne : (List.replicate len (Gen.AbstractByte.Uninit : Byte)) ≠ [] :=
    List.ne_nil_of_length_pos (by simpa using hLen)
  have hbound : off + (List.replicate len (Gen.AbstractByte.Uninit : Byte)).length ≤ a.data.length := by
    simp [hData, length_toAbstractBytes]; omega
  have hStore := CM_store_subslice_align hp hA hlive off haddr _ hne hbound al hal
  refine ⟨⟨st', hSt', hBytes⟩, ?_, fun i hi => ?_⟩
  · rw [hStore, List.length_replicate, hData, ← toAbstractBytes_deinitBytes img off len hOI]
  · simp only [toAbstractBytes, List.getElem?_map, hOut i hi]

/-! ## `TupleSpec` Projected `Deinit`, Sibling Reads, and Re-Initialization in MiniRust & Trusted MIR -/

/-- `TupleSpec.encodeVal` encodes `Value.unit` at any `TupleSpec` (scalar or nested tuple) as
`List.replicate spec.size .Uninit`. -/
theorem TupleSpec.encodeVal_unit (spec : TupleSpec) :
    spec.encodeVal .unit = List.replicate spec.size .Uninit := by
  cases spec with
  | scalar it => rfl
  | tuple fields size align => rfl

/-- Overwriting a `Value` along the same `.field` projection chain `projs` twice is idempotent:
if `writeFieldPath rootVal projs v₁ = some midVal`, then
`writeFieldPath midVal projs v₂ = writeFieldPath rootVal projs v₂`. -/
theorem writeFieldPath_idem :
    ∀ (projs : List ProjectionElem) (rootVal midVal v₁ v₂ : Value),
      writeFieldPath rootVal projs v₁ = some midVal →
      writeFieldPath midVal projs v₂ = writeFieldPath rootVal projs v₂
  | [], _, midVal, _, v₂, h => by
    simp only [writeFieldPath, Option.some.injEq] at h
    subst h
    rfl
  | .field idx fTy :: rest, rootVal, midVal, v₁, v₂, h => by
    cases rootVal with
    | aggregate var vals =>
      cases var with
      | zero =>
        simp only [writeFieldPath] at h ⊢
        cases hfv : vals[idx]? with
        | none => simp [hfv] at h
        | some oldFv =>
          simp only [hfv] at h ⊢
          cases hw : writeFieldPath oldFv rest v₁ with
          | none => simp [hw] at h
          | some midFv =>
            simp only [hw, Option.some.injEq] at h
            subst h
            have hlt : idx < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
            simp only [writeFieldPath, List.getElem?_set_self hlt,
              writeFieldPath_idem rest oldFv midFv v₁ v₂ hw]
            cases writeFieldPath oldFv rest v₂ <;> simp [List.set_set]
      | succ _ => simp [writeFieldPath] at h
    | _ => simp [writeFieldPath] at h
  | .deref :: _, rootVal, _, _, _, h
  | .index _ :: _, rootVal, _, _, _, h
  | .constantIndex _ _ _ :: _, rootVal, _, _, _, h
  | .subslice _ _ _ :: _, rootVal, _, _, _, h
  | .downcast _ _ :: _, rootVal, _, _, _, h
  | .opaqueCast _ :: _, rootVal, _, _, _, h
  | .unwrapUnsafeBinder _ :: _, rootVal, _, _, _, h => by
    cases rootVal <;> simp [writeFieldPath] at h

/-- Writing to field `idx₁` via `writeFieldPath` preserves reading any distinct sibling field
`idx₂ ≠ idx₁`. -/
theorem readFieldPath_writeFieldPath_sibling {vals : List Value} {idx₁ idx₂ : Nat}
    {fTy₁ fTy₂ : Ty} {rest₁ rest₂ : List ProjectionElem} {v midVal : Value}
    (hNe : idx₁ ≠ idx₂)
    (hw : writeFieldPath (.aggregate 0 vals) (.field idx₁ fTy₁ :: rest₁) v = some midVal) :
    readFieldPath midVal (.field idx₂ fTy₂ :: rest₂) =
      readFieldPath (.aggregate 0 vals) (.field idx₂ fTy₂ :: rest₂) := by
  simp only [writeFieldPath] at hw
  cases hfv : vals[idx₁]? with
  | none => simp [hfv] at hw
  | some oldFv =>
    simp only [hfv] at hw
    cases hw' : writeFieldPath oldFv rest₁ v with
    | none => simp [hw'] at hw
    | some newFv =>
      simp only [hw', Option.some.injEq] at hw
      subst hw
      simp [readFieldPath, List.getElem?_set_ne hNe]

/-- **Projected `TupleSpec` Deinitialization (`resolveFieldPath_deinit_unit`)**: writing `Value.unit`
at a resolved field path `projs` of a well-formed `TupleSpec` root value `rootVal` splices
`List.replicate leafSpec.size .Uninit` at `totalOff` in `rootSpec.encodeVal rootVal`, and
subsequently writing any valid `newLeafVal` at `projs` produces the exact same `newRootVal` (with
`rootSpec.valOk newRootVal = true`) as writing `newLeafVal` directly into `rootVal`. -/
theorem resolveFieldPath_deinit_unit {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    {rootSpec leafSpec : TupleSpec} {projs : List ProjectionElem} {totalOff : Nat} {rootVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    ∃ deinitVal,
      writeFieldPath rootVal projs .unit = some deinitVal ∧
      rootSpec.encodeVal deinitVal =
        spliceAt (rootSpec.encodeVal rootVal) totalOff (List.replicate leafSpec.size .Uninit) ∧
      ∀ newLeafVal, leafSpec.valOk newLeafVal = true →
        ∃ newRootVal,
          writeFieldPath deinitVal projs newLeafVal = some newRootVal ∧
          writeFieldPath rootVal projs newLeafVal = some newRootVal ∧
          rootSpec.valOk newRootVal = true ∧
          rootSpec.encodeVal newRootVal =
            spliceAt (rootSpec.encodeVal deinitVal) totalOff (leafSpec.encodeVal newLeafVal) := by
  have hEnc : ∀ (projs' : List ProjectionElem) (rSpec : TupleSpec) (tOff : Nat) (rVal : Value),
      rSpec.wf = true → rSpec.valOk rVal = true →
      resolveFieldPath layouts rSpec projs' = some (tOff, leafSpec) →
      ∃ dVal,
        writeFieldPath rVal projs' .unit = some dVal ∧
        rSpec.encodeVal dVal =
          spliceAt (rSpec.encodeVal rVal) tOff (leafSpec.encodeVal .unit) := by
    intro projs'
    induction projs' with
    | nil =>
      intro rSpec tOff rVal hrWf _ hrRes
      simp [resolveFieldPath] at hrRes
      rcases hrRes with ⟨rfl, rfl⟩
      have hlen1 := TupleSpec.encodeVal_length rSpec rVal hrWf
      have hlen2 := TupleSpec.encodeVal_length rSpec .unit hrWf
      refine ⟨.unit, rfl, ?_⟩
      rw [spliceAt_zero_full _ _ (by omega)]
    | cons p rest ih =>
      intro rSpec tOff rVal hrWf hrVal hrRes
      cases rSpec with
      | scalar _ => cases p <;> simp [resolveFieldPath] at hrRes
      | tuple fields size align =>
        cases p with
        | field idx fieldTy =>
          simp only [resolveFieldPath, Option.bind_eq_bind] at hrRes
          cases hf : fields[idx]? with
          | none => simp [hf] at hrRes
          | some pair =>
            obtain ⟨off, subSpec⟩ := pair
            simp only [hf, Option.bind_some] at hrRes
            cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
            | none => simp [hexp] at hrRes
            | some expectedSpec =>
              simp only [hexp, Option.bind_some] at hrRes
              by_cases heq : subSpec = expectedSpec
              · simp only [heq, ↓reduceIte] at hrRes
                cases hrest : resolveFieldPath layouts expectedSpec rest with
                | none => simp [hrest] at hrRes
                | some rpair =>
                  obtain ⟨restOff, leafSpec'⟩ := rpair
                  simp [hrest] at hrRes
                  rcases hrRes with ⟨rfl, rfl⟩
                  subst heq
                  cases rVal with
                  | aggregate vIdx vals =>
                    cases vIdx with
                    | zero =>
                      simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrWf
                      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hrVal
                      obtain ⟨fv, hfv, hfvOk⟩ := TupleSpec.fieldsValOk_getElem? hrVal.2 hf
                      have hslice := TupleSpec.encodeFields_field_slice size align fields vals
                        (List.replicate size .Uninit) idx off subSpec fv hrWf.2 (by simp) hf hfv
                      obtain ⟨hleafWf, hrestBound⟩ := resolveFieldPath_wf hslice.1 hrest
                      obtain ⟨newFv, hwrite, hnewFvEnc⟩ := ih subSpec restOff fv hslice.1 hfvOk hrest
                      refine ⟨.aggregate 0 (vals.set idx newFv), ?_, ?_⟩
                      · simp [writeFieldPath, hfv, hwrite]
                      · simp only [TupleSpec.encodeVal]
                        rw [TupleSpec.encodeFields_set size align fields vals
                          (List.replicate size .Uninit) idx off subSpec newFv hrWf.2 (by simp) hrVal.1 hf,
                          hnewFvEnc, ← hslice.2.2.2.2]
                        have htotLen :
                            (TupleSpec.encodeFields fields vals (List.replicate size .Uninit)).length = size :=
                          TupleSpec.encodeFields_length size align fields vals
                            (List.replicate size .Uninit) hrWf.2 (by simp)
                        have hleafLen : (leafSpec'.encodeVal .unit).length = leafSpec'.size :=
                          TupleSpec.encodeVal_length leafSpec' .unit hleafWf
                        have hoffBound : off + subSpec.size ≤ size := hslice.2.1
                        exact spliceAt_nested
                          (TupleSpec.encodeFields fields vals (List.replicate size .Uninit))
                          off subSpec.size restOff (leafSpec'.encodeVal .unit)
                          (by omega) (by omega)
                    | succ _ => simp [TupleSpec.valOk] at hrVal
                  | _ => simp [TupleSpec.valOk] at hrVal
              · simp [heq] at hrRes
        | _ => simp [resolveFieldPath] at hrRes
  obtain ⟨deinitVal, hwUnit, hEncUnit⟩ := hEnc projs rootSpec totalOff rootVal hwf hval hres
  refine ⟨deinitVal, hwUnit, ?_, fun newLeafVal hnew => ?_⟩
  · rw [hEncUnit, TupleSpec.encodeVal_unit]
  · obtain ⟨newRootVal, hwNew, hnewOk, hnewEnc, _⟩ := resolveFieldPath_write hwf hval hres hnew
    have hwIdem := writeFieldPath_idem projs rootVal deinitVal .unit newLeafVal hwUnit
    obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hwf hres
    have hlenRoot := TupleSpec.encodeVal_length rootSpec rootVal hwf
    have hlenUnit := TupleSpec.encodeVal_length leafSpec .unit hleafWf
    have hlenNew := TupleSpec.encodeVal_length leafSpec newLeafVal hleafWf
    refine ⟨newRootVal, hwIdem.trans hwNew, hwNew, hnewOk, ?_⟩
    rw [hnewEnc, hEncUnit, spliceAt_same (rootSpec.encodeVal rootVal) totalOff
      (leafSpec.encodeVal .unit) (leafSpec.encodeVal newLeafVal)
      (by omega) (by omega)]

/-- MiniRust's `evalStatement` on a translated projected `TupleSpec` field `Deinit(_i.f1...fk)`:
evaluates the field place via `evalPlace_ptr_fieldPath` and executes `CM.deinit`, replacing the
field's byte slice `[relOff, relOff + leafSpec.size)` in local `i`'s stack allocation with
`List.replicate leafSpec.size .Uninit`, which is the exact `TupleSpec.encodeVal` of `deinitVal`
(`writeFieldPath rootVal (.field idx fieldTy :: rest) .unit = some deinitVal`). -/
theorem evalStatement_deinit_fieldPath {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i idx : Nat) (fieldTy : Ty) (rest : List ProjectionElem)
    (d : LocalDecl) (rootFields : List (Nat × TupleSpec)) (rootSize rootAlign relOff : Nat)
    (leafSpec : TupleSpec) (pe : Gen.PlaceExpr) (rootVal : Value)
    (hd : body.localDecls[i]? = some d)
    (ht : tupleTypeOf body.layouts d.ty = some (rootFields, rootSize, rootAlign))
    (hs : locals[i]? = some (.init rootVal))
    (hpe : translatePlace body.localDecls ⟨i, .field idx fieldTy :: rest⟩ = some pe)
    (hres : resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign)
      (.field idx fieldTy :: rest) = some (relOff, leafSpec))
    (hpos : 0 < leafSpec.size) :
    ∃ (deinitVal : Value) (ptr : Ptr) (k : Nat),
      writeFieldPath rootVal (.field idx fieldTy :: rest) .unit = some deinitVal ∧
      mapGet lm (localName i) = some ptr ∧
      ptr.provenance = some (⟨(k : Int)⟩, ()) ∧
      evalStatement m (.Deinit pe) =
        .ok (withMem m (m.mem.memory.allocations.set k
          (stackAlloc ptr.addr (itOf d body.layouts)
            ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal deinitVal)))
          ⟨.Store, .None, (offsetPtr ptr relOff).addr, ⟨leafSpec.size⟩⟩) := by
  simp only [translatePlace] at hpe
  obtain ⟨hrootWf, hrootVal⟩ :=
    (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (h.slots i d (.init rootVal) hd hs)
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  obtain ⟨deinitVal, hwUnit, hEncUnit, _⟩ := resolveFieldPath_deinit_unit hrootWf hrootVal hres
  obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
  have hloc := (h.hf.2 i d hd).2
  rw [hTd] at hloc
  obtain ⟨ptr, hptr⟩ := h.locs.some_of_live hs (by simp)
  obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
    h.locs.storage_nonptr i d (.init rootVal) ptr hd hs hptr (isPtrTy_false_of_tupleTypeOf ht)
  rw [declSlotData_of_tupleSpec ht] at hA
  have hplaceBase := evalPlace_local_some h.shape i _ hloc ptr hptr
  have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
    TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
  have hbound : rootSize < 2 ^ 63 := by
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
    exact hrootWf.1.2
  rw [hTd] at haddrMax
  simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
  have hrootEval : evalPlace m (.Local (localName i)) =
      .ok (({ ptr := { thin_pointer := offsetPtr ptr 0, metadata := none },
               aligned := true },
             (TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy), m) := by
    simpa using hplaceBase
  have hpeEval := evalPlace_ptr_fieldPath h.shape ptr k hpk (itOf d body.layouts)
    ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA
    (by rw [hdlen]; exact hbound) haddr.nonneg (by rw [hdlen]; exact haddrMax)
    (.Local (localName i)) 0 (.tuple rootFields rootSize rootAlign) hrootEval hrootWf
    (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe relOff leafSpec hres
  simp only [Nat.zero_add] at hpeEval
  have hlay := layout_tupleSpec leafSpec hleafWf
  have hne : (List.replicate leafSpec.size (Gen.AbstractByte.Uninit : Byte)) ≠ [] :=
    List.ne_nil_of_length_pos (by simpa using hpos)
  have hsubBound : relOff + (List.replicate leafSpec.size (Gen.AbstractByte.Uninit : Byte)).length ≤
      ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length := by
    rw [List.length_replicate, hdlen]; exact hrelBound
  have hStore := CM_store_subslice_align (p := offsetPtr ptr relOff)
    (by simpa [offsetPtr] using hpk) hA rfl relOff (by simp [offsetPtr, stackAlloc])
    (List.replicate leafSpec.size .Uninit) hne hsubBound ⟨1⟩ (isAligned_one _)
  refine ⟨deinitVal, ptr, k, hwUnit, hptr, hpk, ?_⟩
  simp only [evalStatement, hpeEval, ok_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hlay, LayoutStrategy.expect_size, CM.deinit, hStore, pure_ok, withMem, stackAlloc,
    List.length_replicate]
  rw [hEncUnit]
  simp [spliceAt]

/-- Trusted's `evalStmt` on a projected `TupleSpec` field `Deinit(_i.f1...fk)` steps as a frame
no-op (`advanceStmt s s.frame.locals`) whenever `_i` holds a well-formed `TupleSpec` value. -/
theorem evalStmt_deinit_field {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    (s : MachineState) (decls : List LocalDecl) (i : Nat) (d : LocalDecl)
    (rootFields : List (Nat × TupleSpec)) (rootSize rootAlign totalOff : Nat)
    (leafSpec : TupleSpec) (proj : ProjectionElem) (rest : List ProjectionElem)
    (span : String) (rootVal : Value)
    (hd : decls[i]? = some d)
    (ht : tupleTypeOf layouts d.ty = some (rootFields, rootSize, rootAlign))
    (hslots : SlotsOk layouts decls s.frame.locals)
    (hs : s.frame.locals[i]? = some (.init rootVal))
    (hres : resolveFieldPath layouts (.tuple rootFields rootSize rootAlign) (proj :: rest) =
      some (totalOff, leafSpec)) :
    evalStmt s ⟨.deinit ⟨i, proj :: rest⟩, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) := by
  obtain ⟨hwf, hval⟩ := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (hslots i d (.init rootVal) hd hs)
  obtain ⟨leafVal, _, _, _, hprojRead⟩ := resolveFieldPath_read hwf hval hres
  simp [evalStmt, Trusted.Sequence.get?, hs, hprojRead s.frame.locals, MirStepNode.step]

/-- **Anneal `PartialShell` trace on `Padded(u8, u32, u16)` (`paddedDeinitSiblingReinit_anneal_shell_agreement`)**:
on `[.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨99, 4⟩, .scalar ⟨1541, 2⟩])]`:
1. `evalDeinitPlace` on `_1.1` explodes `_1` into the `PartialShell`
   `[.init (.scalar ⟨7, 1⟩), .uninit, .init (.scalar ⟨1541, 2⟩)]`;
2. `readPlaceState` on `_1.1` returns `.ub` while `readPlaceState` on sibling `_1.0` returns
   `.ok (.scalar ⟨7, 1⟩)`;
3. `writePlaceState` of `.scalar ⟨42, 4⟩` to `_1.1` collapses the `PartialShell` back into
   `.init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨42, 4⟩, .scalar ⟨1541, 2⟩])`, and reading `_1.1`
   then returns `.ok (.scalar ⟨42, 4⟩)`. -/
theorem paddedDeinitSiblingReinit_anneal_shell_agreement :
    let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let initSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨99, 4⟩, .scalar ⟨1541, 2⟩])]
    let shellSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .partialShell ⟨0, true, true,
        [.init (.scalar ⟨7, 1⟩), .uninit, .init (.scalar ⟨1541, 2⟩)]⟩]
    let finalSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨42, 4⟩, .scalar ⟨1541, 2⟩])]
    Anneal.Mir.AdtAndControl.evalDeinitPlace false initSlots ⟨1, [.field 1 u32Ty]⟩ =
      some shellSlots ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState shellSlots ⟨1, [.field 1 u32Ty]⟩ = .ub ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState shellSlots ⟨1, [.field 0 u8Ty]⟩ =
      .ok (.scalar ⟨7, 1⟩) ∧
    Anneal.Mir.PlaceAndRvalue.writePlaceState (fun _ _ _ => none) shellSlots
      ⟨1, [.field 1 u32Ty]⟩ u32Ty (.scalar ⟨42, 4⟩) = .ok finalSlots ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState finalSlots ⟨1, [.field 1 u32Ty]⟩ =
      .ok (.scalar ⟨42, 4⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Axiom-audit hook for Episode 2's sub-place model (`subplace_audit_closure`)**:
`MiniRustSpec.Audit`'s `#assert_all_minirustspec_standard_axioms` checks every declaration of
the imported `MiniRustSpec.*` modules (this one included, see `IntrinsicBoundary`'s import), but
not the `Anneal.*` theorems of `Anneal.Mir.AdtAndControl` Section 4 (synthetic sub-place
pointers, `Deref` places, sub-place `CopyNonOverlapping`, and their Trusted refinement and
non-vacuity witnesses). This theorem's proof term mentions each of them, so its axioms are the
union of theirs and that exhaustive audit fails unless every one uses only the standard axioms
(in particular no `sorryAx` and no `Lean.ofReduceBool`). -/
theorem subplace_audit_closure : True :=
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_eq_some
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_fits
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_disjoint
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_small
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_page_dvd
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_align_dvd
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_aligned
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_example_two_page_local
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_example_overflow_none
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_sub
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_append
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_disjoint_siblings
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_of_pathRange
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_dead
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_eq_ok
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_inbounds
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_disjoint_locals
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_disjoint_siblings
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_no_guess
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_consistent
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_ambiguous_none
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_singleton
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_of_prechecks
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_null
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_misaligned
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_rangeOverflow
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_dead
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_no_provenance
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_sound
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_evalSubplaceRef
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_stable
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_dead
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_deref_slots
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_bare
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_noDeref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_deref
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_frame
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_frame
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_get_put_init
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_put_get_init
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_put_get
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_get_put
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_read_sibling
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceDeinit_target
  let _ := @Anneal.Mir.AdtAndControl.retag_subplace_ref_dead_local
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticLocal_misses_subplace
  let _ := @Anneal.Mir.AdtAndControl.evalRetagDerefPlace_eq
  let _ := @Anneal.Mir.AdtAndControl.evalRetagDerefPlace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalOperand
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_refines_writePlaceValue
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_assign_deref_refines
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_zero_count
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_overlap_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_zst_bulk_noop
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_dead_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_read_after_copy
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_frame
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_frame
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_unit_array
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_elem_init_array_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_singleDirect
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_subplace_refines
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_null_zero
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_dangling
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_null
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_misaligned
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_dead
  let _ := @Anneal.Mir.AdtAndControl.witness_borrow
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_read
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_write_put_get
  let _ := @Anneal.Mir.AdtAndControl.witness_bases
  let _ := @Anneal.Mir.AdtAndControl.witnessCtx_wf
  let _ := @Anneal.Mir.AdtAndControl.witness_resolve
  let _ := @Anneal.Mir.AdtAndControl.witnessCtxT_wf
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_read
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_read_typed
  let _ := @Anneal.Mir.AdtAndControl.witness_tag_disambiguates_and_rejects_mismatch
  let _ := @Anneal.Mir.AdtAndControl.witness_window_copy
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_encodeSubplaceTag_same
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_tag_one_none
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_mismatch_none
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_general
  let _ := @Anneal.Mir.AdtAndControl.readSubplaceSlot_uninit_tail
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_init_unit_array
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_subslice_init_array_none
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_nested_field_ok
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_window_read_after_copy
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_resolved_ok
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_inbounds_fallback_ok
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation
  let _ := @resolveFieldPath_deinit_unit
  let _ := @evalStatement_deinit_fieldPath
  let _ := @evalStmt_deinit_field
  let _ := @paddedDeinitSiblingReinit_anneal_shell_agreement
  trivial

end MiniRustSpec.Correspondence.DeinitBridge
