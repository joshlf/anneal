/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.AnnealEval

/-!
# Projected `Deinit` of a `TupleSpec` field: MiniRust and Trusted MIR facts

The MiniRust-only and Trusted-only facts about a projected `Deinit(_i.f1...fk)` of a
layout-backed tuple/struct (`TupleSpec`) local, kept free of `Anneal.*` imports so that the
proof-heavy correspondence modules (`MiniRustSpec.Correspondence.DeinitWindow`) can use them
without importing `Anneal`'s global `@[simp]` set:

* `resolveFieldPath_deinit_unit`: writing `Value.unit` at a resolved field path splices
  `List.replicate leafSpec.size .Uninit` into the `TupleSpec.encodeVal` image, and a later
  write of a valid leaf value restores exactly the value obtained by writing it directly;
* `evalStatement_deinit_fieldPath`: MiniRust's `Statement::Deinit` of the translated field
  place stores `Uninit` over the field's byte slice of the local's stack allocation;
* `evalStmt_deinit_field`: Trusted's `evalStmt` on the projected `Deinit` advances with
  unchanged locals.

`MiniRustSpec.Correspondence.DeinitBridge` (which also imports `Anneal.Mir.AdtAndControl`)
re-exports them under the same names.
-/

namespace MiniRustSpec.Correspondence.DeinitBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## `TupleSpec` Projected `Deinit`, Sibling Reads, and Re-Initialization in MiniRust & Trusted MIR -/

/-- `TupleSpec.encodeVal` encodes `Value.unit` at any `TupleSpec` (scalar or nested tuple) as
`List.replicate spec.size .Uninit`. -/
theorem TupleSpec.encodeVal_unit (spec : TupleSpec) :
    spec.encodeVal .unit = List.replicate spec.size .Uninit := by
  cases spec with
  | scalar it => rfl
  | tuple fields size align => rfl

/-- `TupleSpec.encodeVal` encodes `Value.uninit` at any `TupleSpec` (scalar or nested tuple) as
`List.replicate spec.size .Uninit`. -/
theorem TupleSpec.encodeVal_uninit (spec : TupleSpec) :
    spec.encodeVal .uninit = List.replicate spec.size .Uninit := by
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

/-- Splicing back the exact slice `(xs.drop off).take bs.length = bs` leaves `xs` unchanged. -/
theorem spliceAt_eq_self {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (h : off + bs.length ≤ xs.length) (hslice : (xs.drop off).take bs.length = bs) :
    spliceAt xs off bs = xs := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_spliceAt xs off bs h]
  by_cases hk1 : k < off
  · simp [hk1]
  · by_cases hk2 : k < off + bs.length
    · have hsub : k - off < bs.length := by omega
      have hget := congrArg (·[k - off]?) hslice
      rw [getElem?_drop_take] at hget
      simp only [hsub, ↓reduceIte, show off + (k - off) = k by omega] at hget
      simp [hk1, hk2, ← hget]
    · simp [hk1, hk2]

/-- **Projected `TupleSpec` Deinitialization with `Value.uninit` (`resolveFieldPath_deinit_uninit`)**:
writing `Value.uninit` at a resolved field path `projs` of a well-formed `TupleSpec` root value
`rootVal` agrees with Trusted's `deinitProjectedValue`, splices `List.replicate leafSpec.size .Uninit`
at `totalOff` in `rootSpec.encodeVal rootVal`, and subsequently writing any valid `newLeafVal` at
`projs` produces the exact same `newRootVal` as writing `newLeafVal` directly into `rootVal`. -/
theorem resolveFieldPath_deinit_uninit {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    {rootSpec leafSpec : TupleSpec} {projs : List ProjectionElem} {totalOff : Nat} {rootVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    ∃ deinitVal,
      writeFieldPath rootVal projs .uninit = some deinitVal ∧
      rootSpec.encodeVal deinitVal =
        spliceAt (rootSpec.encodeVal rootVal) totalOff (List.replicate leafSpec.size .Uninit) ∧
      (∀ locals, deinitProjectedValue locals rootVal projs = .ok deinitVal) ∧
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
        writeFieldPath rVal projs' .uninit = some dVal ∧
        rSpec.encodeVal dVal =
          spliceAt (rSpec.encodeVal rVal) tOff (leafSpec.encodeVal .uninit) ∧
        ∀ locals decls' layouts' curTyOpt,
          deinitProjectedValue locals rVal projs' decls' layouts' curTyOpt = .ok dVal := by
    intro projs'
    induction projs' with
    | nil =>
      intro rSpec tOff rVal hrWf _ hrRes
      simp [resolveFieldPath] at hrRes
      rcases hrRes with ⟨rfl, rfl⟩
      have hlen1 := TupleSpec.encodeVal_length rSpec rVal hrWf
      have hlen2 := TupleSpec.encodeVal_length rSpec .uninit hrWf
      refine ⟨.uninit, rfl, ?_, fun _ _ _ _ => rfl⟩
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
                      obtain ⟨newFv, hwrite, hnewFvEnc, hprojDeinit⟩ := ih subSpec restOff fv hslice.1 hfvOk hrest
                      have hidx_lt : idx < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
                      refine ⟨.aggregate 0 (vals.set idx newFv), ?_, ?_, ?_⟩
                      · simp [writeFieldPath, hfv, hwrite]
                      · simp only [TupleSpec.encodeVal]
                        rw [TupleSpec.encodeFields_set size align fields vals
                          (List.replicate size .Uninit) idx off subSpec newFv hrWf.2 (by simp) hrVal.1 hf,
                          hnewFvEnc, ← hslice.2.2.2.2]
                        have htotLen :
                            (TupleSpec.encodeFields fields vals (List.replicate size .Uninit)).length = size :=
                          TupleSpec.encodeFields_length size align fields vals
                            (List.replicate size .Uninit) hrWf.2 (by simp)
                        have hleafLen : (leafSpec'.encodeVal .uninit).length = leafSpec'.size :=
                          TupleSpec.encodeVal_length leafSpec' .uninit hleafWf
                        have hoffBound : off + subSpec.size ≤ size := hslice.2.1
                        exact spliceAt_nested
                          (TupleSpec.encodeFields fields vals (List.replicate size .Uninit))
                          off subSpec.size restOff (leafSpec'.encodeVal .uninit)
                          (by omega) (by omega)
                      · intro locals decls' layouts' curTyOpt
                        have hfv' : vals[idx] = fv :=
                          Option.some.inj (by rw [← hfv, List.getElem?_eq_getElem hidx_lt])
                        simp [deinitProjectedValue, Trusted.Sequence.get?, Trusted.Sequence.set?,
                          hidx_lt, hfv', hprojDeinit locals decls' layouts']
                    | succ _ => simp [TupleSpec.valOk] at hrVal
                  | _ => simp [TupleSpec.valOk] at hrVal
              · simp [heq] at hrRes
        | _ => simp [resolveFieldPath] at hrRes
  obtain ⟨deinitVal, hwUninit, hEncUninit, hDeinit⟩ := hEnc projs rootSpec totalOff rootVal hwf hval hres
  refine ⟨deinitVal, hwUninit, ?_, fun locals => hDeinit locals .nil emptyLayoutTable .none, fun newLeafVal hnew => ?_⟩
  · rw [hEncUninit, TupleSpec.encodeVal_uninit]
  · obtain ⟨newRootVal, hwNew, hnewOk, hnewEnc, _⟩ := resolveFieldPath_write hwf hval hres hnew
    have hwIdem := writeFieldPath_idem projs rootVal deinitVal .uninit newLeafVal hwUninit
    obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hwf hres
    have hlenRoot := TupleSpec.encodeVal_length rootSpec rootVal hwf
    have hlenUninit := TupleSpec.encodeVal_length leafSpec .uninit hleafWf
    have hlenNew := TupleSpec.encodeVal_length leafSpec newLeafVal hleafWf
    refine ⟨newRootVal, hwIdem.trans hwNew, hwNew, hnewOk, ?_⟩
    rw [hnewEnc, hEncUninit, spliceAt_same (rootSpec.encodeVal rootVal) totalOff
      (leafSpec.encodeVal .uninit) (leafSpec.encodeVal newLeafVal)
      (by omega) (by omega)]

/-- Trusted's `evalStmt` on a projected `TupleSpec` field `Deinit(_i.f1...fk)` overwrites the
projected field in local `i` with `Value.uninit` (`writeFieldPath rootVal (proj :: rest) .uninit`),
splicing `List.replicate leafSpec.size .Uninit` at `totalOff` in `TupleSpec.encodeVal`. -/
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
      some (totalOff, leafSpec))
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) :
    ∃ deinitVal,
      writeFieldPath rootVal (proj :: rest) .uninit = some deinitVal ∧
      (TupleSpec.tuple rootFields rootSize rootAlign).encodeVal deinitVal =
        spliceAt ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) totalOff
          (List.replicate leafSpec.size .Uninit) ∧
      evalStmt s ⟨.deinit ⟨i, proj :: rest⟩, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init deinitVal)))) := by
  obtain ⟨hwf, hval⟩ := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (hslots i d (.init rootVal) hd hs)
  have hdeinitTyped : ∀ (projs' : List ProjectionElem) (rSpec : TupleSpec) (tOff : Nat) (rVal : Value),
      rSpec.wf = true → rSpec.valOk rVal = true →
      resolveFieldPath layouts rSpec projs' = some (tOff, leafSpec) →
      ∀ (curTyOpt : Option Trusted.Rustc.V2026_06_01.MirAst.Ty),
        deinitProjectedValue s.frame.locals rVal projs' decls layouts curTyOpt =
          deinitProjectedValue s.frame.locals rVal projs' := by
    intro projs'
    induction projs' with
    | nil => intros _ _ rVal _ _ _ _; cases rVal <;> rfl
    | cons p tl ih =>
      intro rSpec tOff rVal hrWf hrVal hrRes curTyOpt
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
                cases hrest : resolveFieldPath layouts expectedSpec tl with
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
                      have hidx_lt : idx < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
                      have hfv' : vals[idx] = fv :=
                        Option.some.inj (by rw [← hfv, List.getElem?_eq_getElem hidx_lt])
                      have ihEq := ih subSpec restOff fv hslice.1 hfvOk hrest
                      cases curTyOpt <;>
                        simp [deinitProjectedValue, Trusted.Sequence.get?, hidx_lt, hfv', ihEq]
                    | succ _ => simp [TupleSpec.valOk] at hrVal
                  | _ => simp [TupleSpec.valOk] at hrVal
              · simp [heq] at hrRes
        | _ => simp [resolveFieldPath] at hrRes
  obtain ⟨deinitVal, hw, henc, hdeinit, _⟩ := resolveFieldPath_deinit_uninit hwf hval hres
  have hi_lt : i < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hs).1
  have hElem : s.frame.locals[i]'hi_lt = .init rootVal :=
    Option.some.inj ((List.getElem?_eq_getElem hi_lt).symm.trans hs)
  have hnu := placeTouchesUnion_false_of_tupleTypeOf decls ht ⟨i, proj :: rest⟩
  have hf := resolveFieldPath_allFields hres
  have hpd : projListHasDeref (proj :: rest) = false := by
    revert hf
    generalize proj :: rest = ps
    intro hf
    induction ps with
    | nil => rfl
    | cons p rs ih => cases p <;> simp_all [allFields, projListHasDeref]
  have hdp : deinitProjectedForLocal s.frame.locals decls layouts i rootVal (proj :: rest) =
      .ok deinitVal := by
    unfold deinitProjectedForLocal
    rw [hpd, hnu]
    dsimp only
    rw [hdeinitTyped (proj :: rest) (.tuple rootFields rootSize rootAlign) totalOff rootVal
      hwf hval hres]
    exact hdeinit s.frame.locals
  have hinv := invalidateConflictingBorrowsAtProj_of_ne s.memory.borrows i .none
    (resolveBorrowWriteLocalProj decls layouts s.frame.locals i (proj :: rest)) 0 0 hbor
    (Trusted.Sequence.length s.memory.callStack)
  refine ⟨deinitVal, hw, henc, ?_⟩
  cases proj with
  | field fIdx fTy =>
    cases hp : s.memory.activeProtectors with
    | nil =>
      simp [evalStmt, hdp, Trusted.Sequence.get?, Trusted.Sequence.set?,
        hi_lt, hElem, hinv, MirStepNode.step, advanceStmt]
      cases hm : s.memory; simp_all
    | cons p0 ps0 =>
      have hconf := hasProtectedWriteConflict_of_ne s.memory.borrows (p0 :: ps0) i .none
        (resolveBorrowWriteLocalProj decls layouts s.frame.locals i (.field fIdx fTy :: rest)) 0 0 hbor
        (Trusted.Sequence.length s.memory.callStack)
      simp [evalStmt, hdp, Trusted.Sequence.get?, Trusted.Sequence.set?,
        hi_lt, hElem, hinv, MirStepNode.step, advanceStmt]
      cases hm : s.memory; simp_all
  | _ => simp [allFields] at hf

private theorem scalar_wf_size_pos {it : Gen.IntType} (hwf : (TupleSpec.scalar it).wf = true) :
    0 < it.size.bytes := by
  simp only [TupleSpec.wf] at hwf
  have hgood := (goodAlignBytes_iff it.size.bytes).mp hwf
  rcases hgood with h | h | h | h | h <;> omega

/-- Writing `newLeafVal` at a scalar field path `ps'` at offset `off` into `deinitVal` (obtained by
writing `.uninit` at a scalar field path `ps` at the **same** offset `off`) produces the exact same
`writeProjectedValue` result as writing directly into `rootVal`. -/
theorem resolveFieldPath_same_off_writeProjectedValue
    {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    {rootSpec : TupleSpec} {ps ps' : List ProjectionElem} {off : Nat}
    {it₀ it : Gen.IntType} {rootVal deinitVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec ps = some (off, .scalar it₀))
    (hres' : resolveFieldPath layouts rootSpec ps' = some (off, .scalar it))
    (hw : writeFieldPath rootVal ps .uninit = some deinitVal) :
    ∀ newLeafVal,
      writeFieldPath deinitVal ps' newLeafVal = writeFieldPath rootVal ps' newLeafVal ∧
      ∀ locals,
        writeProjectedValue locals deinitVal ps' newLeafVal =
          writeProjectedValue locals rootVal ps' newLeafVal := by
  induction ps' generalizing ps rootSpec off rootVal deinitVal with
  | nil =>
    intro _
    exact ⟨rfl, fun _ => rfl⟩
  | cons p' rest' ih =>
    cases rootSpec with
    | scalar _ => cases p' <;> simp [resolveFieldPath] at hres'
    | tuple fields size align =>
      cases p' with
      | field idx₂ fTy₂ =>
        cases ps with
        | nil => simp [resolveFieldPath] at hres
        | cons p rest =>
          cases p with
          | field idx₁ fTy₁ =>
            simp only [resolveFieldPath, Option.bind_eq_bind] at hres hres'
            cases hf₁ : fields[idx₁]? with
            | none => simp [hf₁] at hres
            | some pair₁ =>
              obtain ⟨off₁, sub₁⟩ := pair₁
              simp only [hf₁, Option.bind_some] at hres
              cases hexp₁ : specOfRigidTy layouts fTy₁.kind fTy₁.layoutIdx with
              | none => simp [hexp₁] at hres
              | some exp₁ =>
                simp only [hexp₁, Option.bind_some] at hres
                by_cases heq₁ : sub₁ = exp₁
                · simp only [heq₁, ↓reduceIte] at hres
                  subst heq₁
                  cases hrest₁ : resolveFieldPath layouts sub₁ rest with
                  | none => simp [hrest₁] at hres
                  | some rpair₁ =>
                    obtain ⟨restOff₁, leaf₁⟩ := rpair₁
                    simp [hrest₁] at hres
                    rcases hres with ⟨hoff₁, rfl⟩
                    cases hf₂ : fields[idx₂]? with
                    | none => simp [hf₂] at hres'
                    | some pair₂ =>
                      obtain ⟨off₂, sub₂⟩ := pair₂
                      simp only [hf₂, Option.bind_some] at hres'
                      cases hexp₂ : specOfRigidTy layouts fTy₂.kind fTy₂.layoutIdx with
                      | none => simp [hexp₂] at hres'
                      | some exp₂ =>
                        simp only [hexp₂, Option.bind_some] at hres'
                        by_cases heq₂ : sub₂ = exp₂
                        · simp only [heq₂, ↓reduceIte] at hres'
                          subst heq₂
                          cases hrest₂ : resolveFieldPath layouts sub₂ rest' with
                          | none => simp [hrest₂] at hres'
                          | some rpair₂ =>
                            obtain ⟨restOff₂, leaf₂⟩ := rpair₂
                            simp [hrest₂] at hres'
                            rcases hres' with ⟨hoff₂, rfl⟩
                            simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
                            have hfwf₁ := TupleSpec.fieldsWf_getElem? hwf.2 hf₁
                            have hfwf₂ := TupleSpec.fieldsWf_getElem? hwf.2 hf₂
                            obtain ⟨hlwf₁, hb₁⟩ := resolveFieldPath_wf hfwf₁.1 hrest₁
                            obtain ⟨hlwf₂, hb₂⟩ := resolveFieldPath_wf hfwf₂.1 hrest₂
                            have hpos₁ := scalar_wf_size_pos hlwf₁
                            have hpos₂ := scalar_wf_size_pos hlwf₂
                            have hidxEq : idx₁ = idx₂ :=
                              Classical.byContradiction fun hne => by
                                have hdisj := TupleSpec.fieldsWf_disjoint hwf.2 hf₁ hf₂ hne
                                have hsz₁ : (TupleSpec.scalar it₀).size = it₀.size.bytes := rfl
                                have hsz₂ : (TupleSpec.scalar it).size = it.size.bytes := rfl
                                omega
                            subst hidxEq
                            rw [hf₁] at hf₂
                            simp only [Option.some.injEq, Prod.mk.injEq] at hf₂
                            rcases hf₂ with ⟨rfl, rfl⟩
                            have hroff : restOff₁ = restOff₂ := by omega
                            subst hroff
                            cases rootVal with
                            | aggregate vIdx vals =>
                              cases vIdx with
                              | zero =>
                                simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hval
                                obtain ⟨fv, hfv, hfvOk⟩ := TupleSpec.fieldsValOk_getElem? hval.2 hf₁
                                simp only [writeFieldPath, hfv] at hw
                                cases hwSub : writeFieldPath fv rest .uninit with
                                | none => simp [hwSub] at hw
                                | some deinitFv =>
                                  simp only [hwSub, Option.some.injEq] at hw
                                  subst hw
                                  intro newLeafVal
                                  have hlt : idx₁ < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
                                  obtain ⟨hwPathEq, hwProjEq⟩ := ih hfwf₁.1 hfvOk hrest₁ hrest₂ hwSub newLeafVal
                                  refine ⟨?_, fun locals => ?_⟩
                                  · simp only [writeFieldPath, List.getElem?_set_self hlt, hfv, hwPathEq]
                                    cases writeFieldPath fv rest' newLeafVal <;> simp [List.set_set]
                                  · simp only [writeProjectedValue, Trusted.Sequence.get?,
                                      List.getElem?_set_self hlt, hfv, hwProjEq locals]
                                    cases writeProjectedValue locals fv rest' newLeafVal <;>
                                      simp [Trusted.Sequence.set?, hlt, List.set_set]
                              | succ _ => simp [TupleSpec.valOk] at hval
                            | _ => simp [TupleSpec.valOk] at hval
                        · simp [heq₂] at hres'
                · simp [heq₁] at hres
          | _ => simp [resolveFieldPath] at hres
      | _ => simp [resolveFieldPath] at hres'

/-- Reading a byte-disjoint scalar field path `ps'` from `deinitVal` (obtained by writing `.uninit`
at field path `ps` of `rootVal`) produces the exact same `readProjectedValue` result as reading
directly from `rootVal`. -/
theorem resolveFieldPath_disjoint_readProjectedValue
    {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    {rootSpec leaf : TupleSpec} {ps ps' : List ProjectionElem} {off off' : Nat}
    {it' : Gen.IntType} {rootVal deinitVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec ps = some (off, leaf))
    (hres' : resolveFieldPath layouts rootSpec ps' = some (off', .scalar it'))
    (hdis : off' + it'.size.bytes ≤ off ∨ off + leaf.size ≤ off')
    (hw : writeFieldPath rootVal ps .uninit = some deinitVal) :
    ∀ locals,
      readProjectedValue locals deinitVal ps' =
        readProjectedValue locals rootVal ps' := by
  induction ps generalizing ps' rootSpec off off' rootVal deinitVal with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    obtain ⟨hlwf', hb'⟩ := resolveFieldPath_wf hwf hres'
    have hpos' := scalar_wf_size_pos hlwf'
    have hsz' : (TupleSpec.scalar it').size = it'.size.bytes := rfl
    omega
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ => cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx₁ fTy₁ =>
        cases ps' with
        | nil => simp [resolveFieldPath] at hres'
        | cons p' rest' =>
          cases p' with
          | field idx₂ fTy₂ =>
            simp only [resolveFieldPath, Option.bind_eq_bind] at hres hres'
            cases hf₁ : fields[idx₁]? with
            | none => simp [hf₁] at hres
            | some pair₁ =>
              obtain ⟨off₁, sub₁⟩ := pair₁
              simp only [hf₁, Option.bind_some] at hres
              cases hexp₁ : specOfRigidTy layouts fTy₁.kind fTy₁.layoutIdx with
              | none => simp [hexp₁] at hres
              | some exp₁ =>
                simp only [hexp₁, Option.bind_some] at hres
                by_cases heq₁ : sub₁ = exp₁
                · simp only [heq₁, ↓reduceIte] at hres
                  subst heq₁
                  cases hrest₁ : resolveFieldPath layouts sub₁ rest with
                  | none => simp [hrest₁] at hres
                  | some rpair₁ =>
                    obtain ⟨restOff₁, leaf₁⟩ := rpair₁
                    simp [hrest₁] at hres
                    rcases hres with ⟨rfl, rfl⟩
                    cases rootVal with
                    | aggregate vIdx vals =>
                      cases vIdx with
                      | zero =>
                        simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
                        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hval
                        obtain ⟨fv, hfv, hfvOk⟩ := TupleSpec.fieldsValOk_getElem? hval.2 hf₁
                        simp only [writeFieldPath, hfv] at hw
                        cases hwSub : writeFieldPath fv rest .uninit with
                        | none => simp [hwSub] at hw
                        | some deinitFv =>
                          simp only [hwSub, Option.some.injEq] at hw
                          subst hw
                          intro locals
                          by_cases hidx : idx₁ = idx₂
                          · subst hidx
                            simp only [hf₁, Option.bind_some] at hres'
                            cases hexp₂ : specOfRigidTy layouts fTy₂.kind fTy₂.layoutIdx with
                            | none => simp [hexp₂] at hres'
                            | some exp₂ =>
                              simp only [hexp₂, Option.bind_some] at hres'
                              by_cases heq₂ : sub₁ = exp₂
                              · simp only [heq₂, ↓reduceIte] at hres'
                                subst heq₂
                                cases hrest₂ : resolveFieldPath layouts sub₁ rest' with
                                | none => simp [hrest₂] at hres'
                                | some rpair₂ =>
                                  obtain ⟨restOff₂, leaf₂⟩ := rpair₂
                                  simp [hrest₂] at hres'
                                  rcases hres' with ⟨rfl, rfl⟩
                                  have hfwf₁ := TupleSpec.fieldsWf_getElem? hwf.2 hf₁
                                  have hlt : idx₁ < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
                                  have hdis' : restOff₂ + it'.size.bytes ≤ restOff₁ ∨
                                      restOff₁ + leaf₁.size ≤ restOff₂ := by omega
                                  simp [readProjectedValue, Trusted.Sequence.get?,
                                    List.getElem?_set_self hlt, hfv,
                                    ih hfwf₁.1 hfvOk hrest₁ hrest₂ hdis' hwSub locals]
                              · simp [heq₂] at hres'
                          · simp [readProjectedValue, Trusted.Sequence.get?,
                              List.getElem?_set_ne hidx]
                      | succ _ => simp [TupleSpec.valOk] at hval
                    | _ => simp [TupleSpec.valOk] at hval
                · simp [heq₁] at hres
          | _ => simp [resolveFieldPath] at hres'
      | _ => simp [resolveFieldPath] at hres

/-- Stage-1 Trusted's `evalStmt` on a projected `TupleSpec` scalar field `Retag(kind, _i.f1...fk)`
steps as a frame and memory no-op (`advanceStmt s s.frame.locals`) whenever `_i` holds a well-formed
`TupleSpec` value. -/
theorem evalStmt_retag_field {layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable}
    (s : MachineState) (decls : List LocalDecl) (kind : RetagKind) (i : Nat) (d : LocalDecl)
    (rootFields : List (Nat × TupleSpec)) (rootSize rootAlign totalOff : Nat)
    (it : Gen.IntType) (idx : Nat) (fieldTy : Ty) (rest : List ProjectionElem)
    (span : String) (rootVal : Value)
    (hd : decls[i]? = some d)
    (ht : tupleTypeOf layouts d.ty = some (rootFields, rootSize, rootAlign))
    (hslots : SlotsOk layouts decls s.frame.locals)
    (hs : s.frame.locals[i]? = some (.init rootVal))
    (hres : resolveFieldPath layouts (.tuple rootFields rootSize rootAlign)
      (.field idx fieldTy :: rest) = some (totalOff, .scalar it)) :
    evalStmt s ⟨.retag kind ⟨i, .field idx fieldTy :: rest⟩, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) := by
  obtain ⟨hwf, hval⟩ := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (hslots i d (.init rootVal) hd hs)
  obtain ⟨leafVal, _, hleafOk, _, hprojRead⟩ := resolveFieldPath_read hwf hval hres
  obtain ⟨leafTy, _, hprojTy, hleafSpec⟩ := resolveFieldPath_ty (specOfRigidTy_of_tupleTypeOf ht) hres
  have hit := intTypeOf_of_specOfRigidTy_scalar hleafSpec
  have hnd : ∀ tl, (.field idx fieldTy :: rest) ≠ .deref :: tl := by intro _ hc; cases hc
  have hnu := placeTouchesUnion_false_of_tupleTypeOf decls ht ⟨i, .field idx fieldTy :: rest⟩
  cases leafVal with
  | scalar sc =>
    have hop : evalOperand s.frame.locals (.copy ⟨i, .field idx fieldTy :: rest⟩)
        s.memory.borrows s.memory.globals layouts s.memory.callerLocals decls
        s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      rw [evalOperand_copy_nonDeref s.frame.locals ⟨i, .field idx fieldTy :: rest⟩ hnd
        s.memory.borrows s.memory.globals layouts s.memory.callerLocals decls hnu]
      simp [Trusted.Sequence.get?, hs, hprojRead s.frame.locals]
    have hplTy : placeTy decls layouts ⟨i, .field idx fieldTy :: rest⟩ = some leafTy := by
      simp [placeTy, Trusted.Sequence.get?, hd, hprojTy]
    rcases leafTy with ⟨lkind, llidx⟩
    cases lkind <;> simp [intTypeOf, intTyBytes] at hit <;> simp [evalStmt, hop, hplTy, MirStepNode.step]
  | _ => simp [TupleSpec.valOk] at hleafOk

end MiniRustSpec.Correspondence.DeinitBridge
