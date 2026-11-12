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

end MiniRustSpec.Correspondence.DeinitBridge
