/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.LayoutLM2_2

/-!
# `LM-2.2` Projection Chains, `StructMemPlaceRel`, State Relation & Mutable-Place Helpers

Foundational correspondence definitions and lemmas for `LM-2.2` (imported by
`SimLM2_2.lean`):

1. `IsRoundtripTy`, `ValidFieldProjChain`, `ValidZeroScalarChain`, and multi-step
   `Miri.Interpreter.project` / `annealProjectPlaceList` lemmas;
2. `ValidAggregateFieldPath`, `DisjointFieldPaths`, `StructMemPlaceRel` (covering
   both unpadded and padded aggregates via `valueLeafBytes` and
   `structSumFieldBytes`), and `UninitStructMemPlaceRel`;
3. `StructTypeEnv`, `ImmediateStructRel`, `LocalRelLM2_2`, `FrameRelLM2_2`,
   `StateRelLM2_2`, and `StepRelLM2_2`, carrying `StructMemPlaceRel` directly in
   the state relation (`LocalRelLM2_2.structInd`) with frame preservation across
   allocation pushes, disjoint allocation writes, and local deallocation;
4. State-independent `WellTypedLM2_2ProjectedRead` and
   `evalProjection_nested_field_read_simulation`;
5. Upstream `Miri.Interpreter.writePlaceImmediateNoValidate` (`forceAllocation`
   under `annealMutablePlaceHooks`) stepping lemmas and `AllocIdWatermark` /
   `AllocIdSupplyValid`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Total byte count of scalar leaves inside an Anneal `Value`. For a tuple or
struct whose leaves are its scalar fields, the layout size exceeds this count
exactly by the number of inter-field and trailing padding bytes
(`ValidStructLayout.sumFieldBytes_lt_iff_exists_padding`). -/
def valueLeafBytes : Value → Nat
  | .unit => 0
  | .scalar sc => sc.sizeBytes
  | .ptr _ _ => 8
  | .aggregate _ fs => valueLeafBytesList fs
where
  /-- Sum `valueLeafBytes` across an aggregate field list. -/
  valueLeafBytesList : List Value → Nat
    | [] => 0
    | v :: vs => valueLeafBytes v + valueLeafBytesList vs

/-! ## 1. Type Encoding Roundtrip & Nested Field Projection Chains -/

/-- Types `ty` whose encoded `Miri.MIR.TyId` round-trips through
`layoutOfEncodedTyId (encodeTyId ty) layouts = translateTy ty layouts`:
primitive scalars (`bool`, `char`, `int`, `uint`), non-empty tuples, and ADTs. -/
def IsRoundtripTy (ty : Ty) : Prop :=
  IsPrimScalarTy ty ∨
    (∃ t ts, ty.kind = .tuple (t :: ts)) ∨
    (∃ p a, ty.kind = .adt p a)

theorem IsRoundtripTy.layoutOfEncoded {ty : Ty} {layouts : LayoutTable}
    (h : IsRoundtripTy ty) :
    layoutOfEncodedTyId (encodeTyId ty) layouts = translateTy ty layouts := by
  rcases h with hprim | ⟨t, ts, hk⟩ | ⟨p, a, hk⟩
  · exact hprim.layoutOfEncoded
  · rcases ty with ⟨kind, layoutIdx⟩
    dsimp only at hk
    subst hk
    unfold encodeTyId layoutOfEncodedTyId translateTy LayoutIdx Miri.MIR.TyId at *
    dsimp only
    have hsub : 100 + layoutIdx - 100 = layoutIdx := by omega
    split <;> (try omega) <;> (try simp only [hsub]) <;> cases layouts.lookup layoutIdx <;> rfl
  · rcases ty with ⟨kind, layoutIdx⟩
    dsimp only at hk
    subst hk
    unfold encodeTyId layoutOfEncodedTyId translateTy LayoutIdx Miri.MIR.TyId at *
    dsimp only
    have hsub : 100 + layoutIdx - 100 = layoutIdx := by omega
    split <;> (try omega) <;> (try simp only [hsub]) <;> cases layouts.lookup layoutIdx <;> rfl

theorem size_add_of_no_overflow {a b : Miri.ABI.Size}
    (h : a.bytes.toNat + b.bytes.toNat < 2 ^ 64) :
    a.add b = .ok (Miri.ABI.Size.ofBytes (a.bytes + b.bytes)) ∧
    (a.bytes + b.bytes).toNat = a.bytes.toNat + b.bytes.toNat := by
  have hadd : (a.bytes + b.bytes).toNat = a.bytes.toNat + b.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using h)]
  have hnot_lt : ¬(a.bytes + b.bytes < a.bytes) := by
    rw [UInt64.lt_iff_toNat_lt]
    omega
  refine ⟨?_, hadd⟩
  unfold Miri.ABI.Size.add
  simp [hnot_lt]

/-- Well-formed non-empty chain of `.field` projections from `baseLay` to leaf
type `leafTy` with cumulative relative byte offset `totalOff`. -/
inductive ValidFieldProjChain (layouts : LayoutTable) :
    Miri.Interpreter.LocalLayout → List ProjectionElem → Ty → Miri.ABI.Size → Prop where
  | single (baseLay : Miri.Interpreter.LocalLayout) (idx : Nat) (fty : Ty)
      (off : Miri.ABI.Size) :
      IsRoundtripTy fty →
      baseLay.layout.fields.offset idx = .ok off →
      (translateTy fty layouts).layout.isSized = true →
      off.bytes.toNat + (translateTy fty layouts).layout.size.bytes.toNat ≤
        baseLay.layout.size.bytes.toNat →
      ValidFieldProjChain layouts baseLay [.field idx fty] fty off
  | cons (baseLay : Miri.Interpreter.LocalLayout) (idx : Nat) (midTy : Ty)
      (rest : List ProjectionElem) (leafTy : Ty) (off1 offRest : Miri.ABI.Size) :
      IsRoundtripTy midTy →
      baseLay.layout.fields.offset idx = .ok off1 →
      (translateTy midTy layouts).layout.isSized = true →
      off1.bytes.toNat + (translateTy midTy layouts).layout.size.bytes.toNat ≤
        baseLay.layout.size.bytes.toNat →
      ValidFieldProjChain layouts (translateTy midTy layouts) rest leafTy offRest →
      ValidFieldProjChain layouts baseLay (.field idx midTy :: rest) leafTy
        (Miri.ABI.Size.ofBytes (off1.bytes + offRest.bytes))

theorem ValidFieldProjChain.ne_nil
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (h : ValidFieldProjChain layouts baseLay projs leafTy totalOff) :
    projs ≠ [] := by
  cases h <;> nofun

theorem ValidFieldProjChain.not_deref_head
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {p0 : ProjectionElem} {ps : List ProjectionElem}
    {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (h : ValidFieldProjChain layouts baseLay (p0 :: ps) leafTy totalOff) :
    p0 ≠ .deref := by
  cases h <;> nofun

theorem ValidFieldProjChain.last_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (h : ValidFieldProjChain layouts baseLay projs leafTy totalOff) :
    ∃ idx, projs.getLast? = some (.field idx leafTy) := by
  induction h with
  | single _ idx _ _ _ _ _ _ =>
    exact ⟨idx, rfl⟩
  | cons _ _ _ rest _ _ _ _ _ _ _ hrest ih =>
    cases rest with
    | nil => exact False.elim (hrest.ne_nil rfl)
    | cons _ _ => exact ih

theorem ValidFieldProjChain.bounds
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (h : ValidFieldProjChain layouts baseLay projs leafTy totalOff) :
    totalOff.bytes.toNat + (translateTy leafTy layouts).layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat := by
  induction h with
  | single _ _ _ _ _ _ _ hbnd =>
    exact hbnd
  | cons baseLay _ _ _ _ off1 offRest _ _ _ hbnd1 _ ih =>
    have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
    have hsum_lt : off1.bytes.toNat + offRest.bytes.toNat < 2 ^ 64 := by omega
    have hadd_toNat : (off1.bytes + offRest.bytes).toNat =
        off1.bytes.toNat + offRest.bytes.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hsum_lt)]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [hadd_toNat]
    omega

/-- Single-step `Miri.Interpreter.projectField` evaluation on an `.indirect`
memory place with thin metadata under any resolved `annealFieldLayout`. -/
theorem projectField_indirect_of_fieldLayout
    {layouts : LayoutTable} {hintFieldTy : Option Miri.MIR.TyId}
    {baseLay fl : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {idx : Nat} {off : Miri.ABI.Size}
    (hfl : annealFieldLayout layouts hintFieldTy baseLay idx = .ok fl)
    (hoff : baseLay.layout.fields.offset idx = .ok off)
    (hsized : fl.layout.isSized = true)
    (hno_ovf : mp.ptr.offset.bytes.toNat + off.bytes.toNat < 2 ^ 64) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts hintFieldTy)
        ⟨.indirect mp, baseLay⟩ idx =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + off.bytes), mp.ptr.provenance⟩,
              .none, mp.misaligned⟩,
            fl⟩ := by
  obtain ⟨hadd, _⟩ := size_add_of_no_overflow hno_ovf
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx
  simp [hoff, hfl, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Single-step `Miri.Interpreter.projectField` evaluation on an `.indirect`
memory place with thin metadata. -/
theorem projectField_indirect_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {idx : Nat} {fty : Ty} {off : Miri.ABI.Size}
    (hrt : IsRoundtripTy fty)
    (hoff : baseLay.layout.fields.offset idx = .ok off)
    (hsized : (translateTy fty layouts).layout.isSized = true)
    (hno_ovf : mp.ptr.offset.bytes.toNat + off.bytes.toNat < 2 ^ 64) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.indirect mp, baseLay⟩ idx =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + off.bytes), mp.ptr.provenance⟩,
              .none, mp.misaligned⟩,
            translateTy fty layouts⟩ := by
  apply projectField_indirect_of_fieldLayout _ hoff hsized hno_ovf
  unfold annealFieldLayout
  simp [hrt.layoutOfEncoded]

/-- Multi-step `annealEvalProjection` along any `ValidFieldProjChain` on an
`.indirect` memory place. -/
theorem annealEvalProjection_of_validFieldProjChain
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (hchain : ValidFieldProjChain layouts baseLay projs leafTy totalOff)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hno_ovf : mp.ptr.offset.bytes.toNat + baseLay.layout.size.bytes.toNat < 2 ^ 64)
    (m : AnnealStepState) :
    annealEvalProjection layouts ⟨.indirect mp, baseLay⟩
        (projs.map translateProjectionElem) m =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + totalOff.bytes), mp.ptr.provenance⟩,
              .none, mp.misaligned⟩,
            translateTy leafTy layouts⟩ m := by
  induction hchain generalizing mp with
  | single baseLay idx fty off hrt hoff hsized hbnd =>
    have hstep := projectField_indirect_eq (mp := mp) hrt hoff hsized (by omega)
    dsimp only [List.map, translateProjectionElem, annealEvalProjection]
    with_unfolding_all
      simp only [Miri.Interpreter.project, hstep, Bind.bind, Pure.pure]
      rfl
  | cons baseLay idx midTy rest leafTy off1 offRest hrt hoff1 hsized1 hbnd1 hrest ih =>
    have hstep1 := projectField_indirect_eq (mp := mp) hrt hoff1 hsized1 (by omega)
    let mp1 : Miri.Interpreter.MemPlace AnnealProv :=
      ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + off1.bytes), mp.ptr.provenance⟩,
        .none, mp.misaligned⟩
    have hlt_u64 : mp.ptr.offset.bytes.toNat + off1.bytes.toNat < UInt64.size := by
      change mp.ptr.offset.bytes.toNat + off1.bytes.toNat < 18446744073709551616
      omega
    have hadd1 : (mp.ptr.offset.bytes + off1.bytes).toNat =
        mp.ptr.offset.bytes.toNat + off1.bytes.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt_u64]
    have hno_ovf1 : mp1.ptr.offset.bytes.toNat +
        (translateTy midTy layouts).layout.size.bytes.toNat < 2 ^ 64 := by
      dsimp [mp1, Miri.ABI.Size.ofBytes]
      rw [hadd1]
      omega
    have ih_mp1 := ih (mp := mp1) hno_ovf1
    have hassoc : mp.ptr.offset.bytes + off1.bytes + offRest.bytes =
        mp.ptr.offset.bytes + (off1.bytes + offRest.bytes) := UInt64.add_assoc _ _ _
    dsimp only [List.map, translateProjectionElem, annealEvalProjection]
    have hhead :
        annealEvalProjection layouts ⟨.indirect mp, baseLay⟩
          (translateProjectionElem (.field idx midTy) :: List.map translateProjectionElem rest) m =
        annealEvalProjection layouts ⟨.indirect mp1, translateTy midTy layouts⟩
          (List.map translateProjectionElem rest) m := by
      dsimp only [translateProjectionElem, annealEvalProjection]
      with_unfolding_all
        simp only [Miri.Interpreter.project, hstep1, Bind.bind, Pure.pure]
        rfl
    change annealEvalProjection layouts ⟨.indirect mp, baseLay⟩
        (translateProjectionElem (.field idx midTy) :: List.map translateProjectionElem rest) m = _
    rw [hhead, ih_mp1]
    dsimp [mp1, Miri.ABI.Size.ofBytes]
    rw [hassoc]

/-- Single-step `annealProjectFieldPlace` on a `.local` runtime place under any
resolved `annealFieldLayout`. -/
theorem annealProjectFieldPlace_local_of_fieldLayout
    {layouts : LayoutTable} {hintFieldTy : Option Miri.MIR.TyId}
    {baseLay fl : Miri.Interpreter.LocalLayout}
    {frameIdx : Nat} {localId : Miri.MIR.LocalId}
    {baseOffOpt : Option Miri.ABI.Size} {id0 : Miri.Interpreter.LocalsIdentity}
    {idx : Nat} {off : Miri.ABI.Size}
    (hfl : annealFieldLayout layouts hintFieldTy baseLay idx = .ok fl)
    (hoff : baseLay.layout.fields.offset idx = .ok off)
    (hsized : fl.layout.isSized = true)
    (hbnd : off.bytes.toNat + fl.layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat)
    (hno_ovf : (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat +
      baseLay.layout.size.bytes.toNat < 2 ^ 64) :
    annealProjectFieldPlace layouts hintFieldTy
        ⟨.local frameIdx localId baseOffOpt id0, baseLay⟩ idx =
      .ok ⟨.local frameIdx localId
            (some (Miri.ABI.Size.ofBytes ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes)))
            id0,
          fl⟩ := by
  have hpf := projectField_indirect_of_fieldLayout
    (mp := (⟨⟨baseOffOpt.getD Miri.ABI.Size.ZERO, none⟩, .none, none⟩ :
      Miri.Interpreter.MemPlace AnnealProv))
    hfl hoff hsized (by dsimp; omega)
  have hlt_u64 : (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off.bytes.toNat < UInt64.size := by
    change (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off.bytes.toNat < 18446744073709551616
    omega
  have hadd_off : ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes).toNat =
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt_u64]
  obtain ⟨hbound_add, hbound_toNat⟩ :=
    size_add_of_no_overflow
      (a := Miri.ABI.Size.ofBytes ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes))
      (b := fl.layout.size)
      (by dsimp [Miri.ABI.Size.ofBytes]; rw [hadd_off]; omega)
  obtain ⟨hend_add, hend_toNat⟩ :=
    size_add_of_no_overflow
      (a := baseOffOpt.getD Miri.ABI.Size.ZERO)
      (b := baseLay.layout.size) hno_ovf
  have hlt1 : decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes <
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes) = false := by
    rw [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt]
    omega
  have hlt2 : decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes +
      fl.layout.size.bytes >
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + baseLay.layout.size.bytes) = false := by
    change decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + baseLay.layout.size.bytes <
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes +
        fl.layout.size.bytes) = false
    rw [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes] at hbound_toNat
    rw [hbound_toNat, hadd_off, hend_toNat]
    omega
  have hcond : (decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes <
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes) ||
    decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes +
      fl.layout.size.bytes >
      (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + baseLay.layout.size.bytes)) = false := by
    rw [hlt1, hlt2]; rfl
  unfold annealProjectFieldPlace
  dsimp only
  rw [hpf]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hbound_add, hend_add]
  change (if (decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes <
        (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes) ||
      decide ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes +
        fl.layout.size.bytes >
        (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + baseLay.layout.size.bytes)) = true then
      Except.error (Miri.Interpreter.StepError.invalidProgram "projected local is out of bounds")
    else
      Except.ok (Miri.Interpreter.RuntimePlace.mk (.local frameIdx localId
        (some (Miri.ABI.Size.ofBytes ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes)))
        id0) fl)) = _
  rw [hcond]
  rfl

/-- Single-step `annealProjectFieldPlace` on a `.local` runtime place. -/
theorem annealProjectFieldPlace_local_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {frameIdx : Nat} {localId : Miri.MIR.LocalId}
    {baseOffOpt : Option Miri.ABI.Size} {id0 : Miri.Interpreter.LocalsIdentity}
    {idx : Nat} {fty : Ty} {off : Miri.ABI.Size}
    (hrt : IsRoundtripTy fty)
    (hoff : baseLay.layout.fields.offset idx = .ok off)
    (hsized : (translateTy fty layouts).layout.isSized = true)
    (hbnd : off.bytes.toNat + (translateTy fty layouts).layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat)
    (hno_ovf : (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat +
      baseLay.layout.size.bytes.toNat < 2 ^ 64) :
    annealProjectFieldPlace layouts (some (encodeTyId fty))
        ⟨.local frameIdx localId baseOffOpt id0, baseLay⟩ idx =
      .ok ⟨.local frameIdx localId
            (some (Miri.ABI.Size.ofBytes ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off.bytes)))
            id0,
          translateTy fty layouts⟩ := by
  apply annealProjectFieldPlace_local_of_fieldLayout _ hoff hsized hbnd hno_ovf
  unfold annealFieldLayout
  simp [hrt.layoutOfEncoded]

/-- Multi-step `annealProjectPlaceList` along any `ValidFieldProjChain` on a
`.local` runtime place. -/
theorem annealProjectPlaceList_of_validFieldProjChain
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (hchain : ValidFieldProjChain layouts baseLay projs leafTy totalOff)
    {frameIdx : Nat} {localId : Miri.MIR.LocalId}
    {baseOffOpt : Option Miri.ABI.Size} {id0 : Miri.Interpreter.LocalsIdentity}
    (hno_ovf : (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat +
      baseLay.layout.size.bytes.toNat < 2 ^ 64) :
    annealProjectPlaceList layouts
        ⟨.local frameIdx localId baseOffOpt id0, baseLay⟩
        (projs.map translateProjectionElem) =
      .ok ⟨.local frameIdx localId
            (some (Miri.ABI.Size.ofBytes
              ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + totalOff.bytes)))
            id0,
          translateTy leafTy layouts⟩ := by
  induction hchain generalizing baseOffOpt with
  | single baseLay idx fty off hrt hoff hsized hbnd =>
    have hstep := annealProjectFieldPlace_local_eq (frameIdx := frameIdx) (localId := localId)
      (baseOffOpt := baseOffOpt) (id0 := id0) hrt hoff hsized hbnd hno_ovf
    dsimp only [List.map, translateProjectionElem, annealProjectPlaceList]
    rw [hstep]
    rfl
  | cons baseLay idx midTy rest leafTy off1 offRest hrt hoff1 hsized1 hbnd1 hrest ih =>
    have hstep1 := annealProjectFieldPlace_local_eq (frameIdx := frameIdx) (localId := localId)
      (baseOffOpt := baseOffOpt) (id0 := id0) hrt hoff1 hsized1 hbnd1 hno_ovf
    let offOpt1 := some (Miri.ABI.Size.ofBytes
      ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off1.bytes))
    have hlt_u64 : (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off1.bytes.toNat < UInt64.size := by
      change (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off1.bytes.toNat < 18446744073709551616
      omega
    have hadd1 : ((baseOffOpt.getD Miri.ABI.Size.ZERO).bytes + off1.bytes).toNat =
        (baseOffOpt.getD Miri.ABI.Size.ZERO).bytes.toNat + off1.bytes.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt_u64]
    have hno_ovf1 : (offOpt1.getD Miri.ABI.Size.ZERO).bytes.toNat +
        (translateTy midTy layouts).layout.size.bytes.toNat < 2 ^ 64 := by
      dsimp [offOpt1, Miri.ABI.Size.ofBytes]
      rw [hadd1]
      omega
    have ih1 := ih (baseOffOpt := offOpt1) hno_ovf1
    dsimp only [List.map, translateProjectionElem, annealProjectPlaceList]
    rw [hstep1]
    dsimp only [bind, Except.bind]
    rw [ih1]
    dsimp [offOpt1, Miri.ABI.Size.ofBytes]
    rw [UInt64.add_assoc]

theorem IsPrimScalarTy.layout_props {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    IsRoundtripTy ty ∧
    (translateTy ty layouts).layout.isSized = true ∧
    (translateTy ty layouts).layout.isUninhabited = false ∧
    (translateTy ty layouts).layout.isZst = false ∧
    (match (translateTy ty layouts).layout.backendRepr,
           (translateTy ty layouts).layout.variants,
           (translateTy ty layouts).layout.fields with
     | .Memory, .Single _, .Arbitrary offsets _ => offsets.isEmpty
     | _, _, _ => false) = false ∧
    ∃ abiSc, (translateTy ty layouts).layout.backendRepr = .Scalar abiSc := by
  refine ⟨Or.inl h, ?_⟩
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;>
    (simp [translateTy, scalarLayoutData, IntTy.byteWidth, UintTy.byteWidth,
      Miri.ABI.LayoutData.isSized, Miri.ABI.LayoutData.isUninhabited,
      Miri.ABI.LayoutData.isZst, hk]; try decide)

theorem projectField_immediate_uninit_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {idx : Nat} {fty : Ty} {off : Miri.ABI.Size}
    (hrt : IsRoundtripTy fty)
    (hoff : baseLay.layout.fields.offset idx = .ok off)
    (hsized : (translateTy fty layouts).layout.isSized = true)
    (hbnd : off.bytes.toNat + (translateTy fty layouts).layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate .uninit, baseLay⟩ idx =
      .ok ⟨.immediate .uninit, translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := off) (b := (translateTy fty layouts).layout.size) (by omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (off.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (off.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [hadd_toNat]
    omega
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem annealEvalProjection_uninit_of_validFieldProjChain
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (hchain : ValidFieldProjChain layouts baseLay projs leafTy totalOff)
    (m : AnnealStepState) :
    annealEvalProjection layouts ⟨.immediate .uninit, baseLay⟩
        (projs.map translateProjectionElem) m =
      .ok ⟨.immediate .uninit, translateTy leafTy layouts⟩ m := by
  induction hchain with
  | single baseLay idx fty off hrt hoff hsized hbnd =>
    have hstep := projectField_immediate_uninit_eq hrt hoff hsized hbnd
    dsimp only [List.map, translateProjectionElem, annealEvalProjection]
    with_unfolding_all
      simp only [Miri.Interpreter.project, hstep, Bind.bind, Pure.pure]
      rfl
  | cons baseLay idx midTy rest leafTy off1 offRest hrt hoff1 hsized1 hbnd1 _ ih =>
    have hstep1 := projectField_immediate_uninit_eq hrt hoff1 hsized1 hbnd1
    have hhead :
        annealEvalProjection layouts ⟨.immediate .uninit, baseLay⟩
          (translateProjectionElem (.field idx midTy) :: List.map translateProjectionElem rest) m =
        annealEvalProjection layouts ⟨.immediate .uninit, translateTy midTy layouts⟩
          (List.map translateProjectionElem rest) m := by
      dsimp only [translateProjectionElem, annealEvalProjection]
      with_unfolding_all
        simp only [Miri.Interpreter.project, hstep1, Bind.bind, Pure.pure]
        rfl
    change annealEvalProjection layouts ⟨.immediate .uninit, baseLay⟩
        (translateProjectionElem (.field idx midTy) :: List.map translateProjectionElem rest) m = _
    rw [hhead, ih]

theorem projectField_immediate_scalar_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {s : Miri.Memory.Scalar AnnealProv}
    {idx : Nat} {fty : Ty}
    (hprim : IsPrimScalarTy fty)
    (hoff : baseLay.layout.fields.offset idx = .ok Miri.ABI.Size.ZERO)
    (hsz_eq : (translateTy fty layouts).layout.size = baseLay.layout.size) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate (.scalar s), baseLay⟩ idx =
      .ok ⟨.immediate (.scalar s), translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hrt, hsized, huninhab, hzst, _, abiSc, hrepr_f⟩ := hprim.layout_props (layouts := layouts)
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := Miri.ABI.Size.ZERO)
      (b := (translateTy fty layouts).layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; rw [hsz_eq]; omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hadd_toNat ⊢
    rw [hadd_toNat, hsz_eq]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = true :=
    beq_iff_eq.mpr hsz_eq
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, huninhab, hzst, hrepr_f, hbeq_sz,
    Except.mapError, bind, Except.bind, pure, Except.pure]

theorem projectField_immediate_scalarPair_zero_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {fty : Ty}
    (hprim : IsPrimScalarTy fty)
    (hrepr : baseLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hoff : baseLay.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO)
    (hsz_ne : (translateTy fty layouts).layout.size ≠ baseLay.layout.size)
    (hbnd : (translateTy fty layouts).layout.size.bytes.toNat ≤ baseLay.layout.size.bytes.toNat) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate (.scalarPair s0 s1), baseLay⟩ 0 =
      .ok ⟨.immediate (.scalar s0), translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hrt, hsized, huninhab, hzst, _, abiSc, hrepr_f⟩ := hprim.layout_props (layouts := layouts)
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := Miri.ABI.Size.ZERO)
      (b := (translateTy fty layouts).layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hadd_toNat ⊢
    rw [hadd_toNat]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = false :=
    beq_false_of_ne hsz_ne
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, huninhab, hzst, hrepr_f, hbeq_sz, hrepr,
    Except.mapError, bind, Except.bind, pure, Except.pure]

theorem projectField_immediate_scalarPair_one_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {fty : Ty}
    (hprim : IsPrimScalarTy fty)
    (hrepr : baseLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hoff : baseLay.layout.fields.offset 1 = .ok bOff)
    (hbOff_ne : bOff ≠ Miri.ABI.Size.ZERO)
    (hsz_ne : (translateTy fty layouts).layout.size ≠ baseLay.layout.size)
    (hbnd : bOff.bytes.toNat + (translateTy fty layouts).layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate (.scalarPair s0 s1), baseLay⟩ 1 =
      .ok ⟨.immediate (.scalar s1), translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hrt, hsized, huninhab, hzst, _, abiSc, hrepr_f⟩ := hprim.layout_props (layouts := layouts)
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := bOff)
      (b := (translateTy fty layouts).layout.size) (by omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (bOff.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (bOff.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes] at hadd_toNat ⊢
    rw [hadd_toNat]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = false :=
    beq_false_of_ne hsz_ne
  have hbeq_zero : (bOff == Miri.ABI.Size.ZERO) = false :=
    beq_false_of_ne hbOff_ne
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, huninhab, hzst, hrepr_f, hbeq_sz, hrepr, hbeq_zero,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Layout predicate ensuring `Miri.Interpreter.projectionImmediateOffset` does not
short-circuit to `.uninit` via `forget` (`isUninhabited || isZst || empty Memory`). -/
def IsNonForgetLayout (l : Miri.ABI.LayoutData) : Prop :=
  l.isSized = true ∧
  l.isUninhabited = false ∧
  l.isZst = false ∧
  ∀ memOrd, l.fields ≠ .Arbitrary #[] memOrd

theorem IsPrimScalarTy.isNonForget {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    IsNonForgetLayout (translateTy ty layouts).layout := by
  obtain ⟨_, hs, hu, hz, _, _⟩ := h.layout_props (layouts := layouts)
  refine ⟨hs, hu, hz, ?_⟩
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;>
    simp [translateTy, scalarLayoutData, hk]

theorem projectField_immediate_same_size_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {imm : Miri.Interpreter.Immediate AnnealProv}
    {idx : Nat} {fty : Ty}
    (himm_init : imm ≠ .uninit)
    (hrt : IsRoundtripTy fty)
    (hnf : IsNonForgetLayout (translateTy fty layouts).layout)
    (hoff : baseLay.layout.fields.offset idx = .ok Miri.ABI.Size.ZERO)
    (hsz_eq : (translateTy fty layouts).layout.size = baseLay.layout.size) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate imm, baseLay⟩ idx =
      .ok ⟨.immediate imm, translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hsized, huninhab, hzst, hm⟩ := hnf
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := Miri.ABI.Size.ZERO)
      (b := (translateTy fty layouts).layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; rw [hsz_eq]; omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hadd_toNat ⊢
    rw [hadd_toNat, hsz_eq]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = true :=
    beq_iff_eq.mpr hsz_eq
  cases imm with
  | uninit => exact False.elim (himm_init rfl)
  | scalar s =>
    unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
      annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
    simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
      hadd, hnot_gt, huninhab, hzst, hbeq_sz,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    split <;> split at * <;> split at * <;> simp_all
  | scalarPair s0 s1 =>
    unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
      annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
    simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
      hadd, hnot_gt, huninhab, hzst, hbeq_sz,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    split <;> split at * <;> split at * <;> simp_all

theorem projectField_immediate_scalarPair_zero_nonForget_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {fty : Ty}
    (hrt : IsRoundtripTy fty)
    (hnf : IsNonForgetLayout (translateTy fty layouts).layout)
    (hrepr : baseLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hoff : baseLay.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO)
    (hsz_ne : (translateTy fty layouts).layout.size ≠ baseLay.layout.size)
    (hbnd : (translateTy fty layouts).layout.size.bytes.toNat ≤ baseLay.layout.size.bytes.toNat) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate (.scalarPair s0 s1), baseLay⟩ 0 =
      .ok ⟨.immediate (.scalar s0), translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hsized, huninhab, hzst, hm⟩ := hnf
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := Miri.ABI.Size.ZERO)
      (b := (translateTy fty layouts).layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hadd_toNat ⊢
    rw [hadd_toNat]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = false :=
    beq_false_of_ne hsz_ne
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, huninhab, hzst, hbeq_sz, hrepr,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  split <;> split at * <;> split at * <;> simp_all

theorem projectField_immediate_scalarPair_one_nonForget_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {fty : Ty}
    (hrt : IsRoundtripTy fty)
    (hnf : IsNonForgetLayout (translateTy fty layouts).layout)
    (hrepr : baseLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hoff : baseLay.layout.fields.offset 1 = .ok bOff)
    (hbOff_ne : bOff ≠ Miri.ABI.Size.ZERO)
    (hsz_ne : (translateTy fty layouts).layout.size ≠ baseLay.layout.size)
    (hbnd : bOff.bytes.toNat + (translateTy fty layouts).layout.size.bytes.toNat ≤
      baseLay.layout.size.bytes.toNat) :
    Miri.Interpreter.projectField
        (annealProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate (.scalarPair s0 s1), baseLay⟩ 1 =
      .ok ⟨.immediate (.scalar s1), translateTy fty layouts⟩ := by
  have hlt_u64 := baseLay.layout.size.bytes.toNat_lt
  obtain ⟨hsized, huninhab, hzst, hm⟩ := hnf
  obtain ⟨hadd, hadd_toNat⟩ :=
    size_add_of_no_overflow (a := bOff)
      (b := (translateTy fty layouts).layout.size) (by omega)
  have hnot_gt : ¬(Miri.ABI.Size.ofBytes
      (bOff.bytes + (translateTy fty layouts).layout.size.bytes)).bytes >
      baseLay.layout.size.bytes := by
    change ¬ baseLay.layout.size.bytes <
      (Miri.ABI.Size.ofBytes (bOff.bytes + (translateTy fty layouts).layout.size.bytes)).bytes
    rw [UInt64.lt_iff_toNat_lt]
    dsimp [Miri.ABI.Size.ofBytes] at hadd_toNat ⊢
    rw [hadd_toNat]
    omega
  have hbeq_sz : ((translateTy fty layouts).layout.size == baseLay.layout.size) = false :=
    beq_false_of_ne hsz_ne
  have hbeq_zero : (bOff == Miri.ABI.Size.ZERO) = false :=
    beq_false_of_ne hbOff_ne
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    annealProjectionCx annealFieldLayout Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hrt.layoutOfEncoded, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, hnot_gt, huninhab, hzst, hbeq_sz, hrepr, hbeq_zero,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  split <;> split at * <;> split at * <;> simp_all

/-- Arbitrary-depth chain of zero-offset `.field 0 _` newtype/wrapper projections
ending at a primitive scalar leaf type `leafTy` of equal byte size. -/
inductive ValidZeroScalarChain (layouts : LayoutTable) :
    Miri.Interpreter.LocalLayout → List ProjectionElem → Ty → Prop where
  | single (baseLay : Miri.Interpreter.LocalLayout) (leafTy : Ty) :
      IsPrimScalarTy leafTy →
      baseLay.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO →
      (translateTy leafTy layouts).layout.size = baseLay.layout.size →
      ValidZeroScalarChain layouts baseLay [.field 0 leafTy] leafTy
  | cons (baseLay : Miri.Interpreter.LocalLayout) (midTy : Ty)
      (rest : List ProjectionElem) (leafTy : Ty) :
      IsRoundtripTy midTy →
      IsNonForgetLayout (translateTy midTy layouts).layout →
      baseLay.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO →
      (translateTy midTy layouts).layout.size = baseLay.layout.size →
      ValidZeroScalarChain layouts (translateTy midTy layouts) rest leafTy →
      ValidZeroScalarChain layouts baseLay (.field 0 midTy :: rest) leafTy

theorem ValidZeroScalarChain.toValidFieldProjChain
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty}
    (h : ValidZeroScalarChain layouts baseLay projs leafTy) :
    ValidFieldProjChain layouts baseLay projs leafTy Miri.ABI.Size.ZERO := by
  induction h with
  | single baseLay leafTy hprim hoff hsz =>
    obtain ⟨hrt, hsized, _⟩ := hprim.layout_props (layouts := layouts)
    exact .single baseLay 0 leafTy Miri.ABI.Size.ZERO hrt hoff hsized
      (by dsimp [Miri.ABI.Size.ZERO]; rw [hsz]; omega)
  | cons baseLay midTy rest leafTy hrt hnf hoff hsz _ ih =>
    have hzero : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + Miri.ABI.Size.ZERO.bytes) =
        Miri.ABI.Size.ZERO := rfl
    rw [← hzero]
    exact .cons baseLay 0 midTy rest leafTy Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO
      hrt hoff hnf.1 (by dsimp [Miri.ABI.Size.ZERO]; rw [hsz]; omega) ih

theorem ValidZeroScalarChain.leaf_prim_and_size
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty}
    (h : ValidZeroScalarChain layouts baseLay projs leafTy) :
    IsPrimScalarTy leafTy ∧
    (translateTy leafTy layouts).layout.size = baseLay.layout.size := by
  induction h with
  | single _ _ hprim _ hsz => exact ⟨hprim, hsz⟩
  | cons _ _ _ _ _ _ _ hsz1 _ ih => exact ⟨ih.1, ih.2.trans hsz1⟩

theorem ValidZeroScalarChain.annealEvalProjection_scalar
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty}
    (h : ValidZeroScalarChain layouts baseLay projs leafTy)
    (s : Miri.Memory.Scalar AnnealProv) (m : AnnealStepState) :
    annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
        (projs.map translateProjectionElem) m =
      .ok ⟨.immediate (.scalar s), translateTy leafTy layouts⟩ m := by
  induction h with
  | single baseLay leafTy hprim hoff hsz =>
    have hpf := projectField_immediate_scalar_eq (layouts := layouts)
      (baseLay := baseLay) (s := s) hprim hoff hsz
    dsimp only [List.map, translateProjectionElem, annealEvalProjection]
    with_unfolding_all
      simp only [Miri.Interpreter.project, hpf, Bind.bind, Pure.pure]
      rfl
  | cons baseLay midTy rest leafTy hrt hnf hoff hsz _ ih =>
    have hpf := projectField_immediate_same_size_eq (layouts := layouts)
      (baseLay := baseLay) (imm := .scalar s) (by nofun) hrt hnf hoff hsz
    have hhead :
        annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
          (translateProjectionElem (.field 0 midTy) :: List.map translateProjectionElem rest) m =
        annealEvalProjection layouts ⟨.immediate (.scalar s), translateTy midTy layouts⟩
          (List.map translateProjectionElem rest) m := by
      dsimp only [translateProjectionElem, annealEvalProjection]
      with_unfolding_all
        simp only [Miri.Interpreter.project, hpf, Bind.bind, Pure.pure]
        rfl
    change annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
        (translateProjectionElem (.field 0 midTy) :: List.map translateProjectionElem rest) m = _
    rw [hhead, ih]

theorem ValidZeroScalarChain.all_field_zero
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty}
    (h : ValidZeroScalarChain layouts baseLay projs leafTy) :
    ∀ p ∈ projs, ∃ fty, p = .field 0 fty := by
  induction h with
  | single _ leafTy _ _ _ =>
    intro p hp
    simp only [List.mem_singleton] at hp
    exact ⟨leafTy, hp⟩
  | cons _ midTy _ _ _ _ _ _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨midTy, rfl⟩
    · exact ih p hmem

theorem ValidZeroScalarChain.evalProjection_prefix_scalar
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {q : ProjectionElem}
    {subIdx : Nat} {subTy leafTy : Ty}
    (hne : projs ≠ [])
    (hlast : projs.getLast? = some (.field subIdx subTy))
    (h : ValidZeroScalarChain layouts baseLay (projs ++ [q]) leafTy)
    (s : Miri.Memory.Scalar AnnealProv) (m : AnnealStepState) :
    annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
        (projs.map translateProjectionElem) m =
      .ok ⟨.immediate (.scalar s), translateTy subTy layouts⟩ m := by
  induction projs generalizing baseLay with
  | nil => exact False.elim (hne rfl)
  | cons p0 ps ih =>
    cases ps with
    | nil =>
      dsimp [List.append] at h
      cases h with
      | cons _ midTy _ _ hrt hnf hoff hsz _ =>
        simp only [List.getLast?_singleton, Option.some.injEq,
          ProjectionElem.field.injEq] at hlast
        rcases hlast with ⟨_, rfl⟩
        have hpf := projectField_immediate_same_size_eq (layouts := layouts)
          (baseLay := baseLay) (imm := .scalar s) (by nofun) hrt hnf hoff hsz
        dsimp only [List.map, translateProjectionElem, annealEvalProjection]
        with_unfolding_all
          simp only [Miri.Interpreter.project, hpf, Bind.bind, Pure.pure]
          rfl
    | cons p1 ps' =>
      dsimp [List.append] at h
      cases h with
      | cons _ midTy _ _ hrt hnf hoff hsz hrest =>
        have hpf := projectField_immediate_same_size_eq (layouts := layouts)
          (baseLay := baseLay) (imm := .scalar s) (by nofun) hrt hnf hoff hsz
        have hhead :
            annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
              (translateProjectionElem (.field 0 midTy) ::
                List.map translateProjectionElem (p1 :: ps')) m =
            annealEvalProjection layouts ⟨.immediate (.scalar s), translateTy midTy layouts⟩
              (List.map translateProjectionElem (p1 :: ps')) m := by
          dsimp only [translateProjectionElem, annealEvalProjection]
          with_unfolding_all
            simp only [Miri.Interpreter.project, hpf, Bind.bind, Pure.pure]
            rfl
        have hlast' : (p1 :: ps').getLast? = some (.field subIdx subTy) := by
          simpa using hlast
        change annealEvalProjection layouts ⟨.immediate (.scalar s), baseLay⟩
            (translateProjectionElem (.field 0 midTy) ::
              List.map translateProjectionElem (p1 :: ps')) m = _
        rw [hhead]
        exact ih (by nofun) hlast' hrest

/-- An Anneal `Value` storing scalar `sc` along a zero-offset `.field 0` chain
`projs`: bare `.scalar sc` at `[]`, and a nested 1-field `Value.aggregate 0 [subVal]`
wrapper tree produced by `Rvalue.aggregate` at `.field 0 fty :: rest`. -/
inductive ZeroScalarWrappedVal (sc : MirAst.ScalarInt) :
    Value → List ProjectionElem → Prop where
  | bare :
      ZeroScalarWrappedVal sc (.scalar sc) []
  | wrap_cons (fty : Ty) (rest : List ProjectionElem) (subVal : Value) :
      ZeroScalarWrappedVal sc subVal rest →
      ZeroScalarWrappedVal sc (.aggregate 0 [subVal]) (.field 0 fty :: rest)

theorem ZeroScalarWrappedVal.readProjectedValue_prefix_wrap
    {sc : MirAst.ScalarInt} {v : Value}
    {projs : List ProjectionElem} {mid₀ : Ty}
    (hne : projs ≠ [])
    (h : ZeroScalarWrappedVal sc v (projs ++ [.field 0 mid₀]))
    (locals : List LocalSlot) :
    readProjectedValue locals v projs = .ok (.aggregate 0 [.scalar sc]) := by
  induction projs generalizing v with
  | nil => exact False.elim (hne rfl)
  | cons p0 ps ih =>
    cases ps with
    | nil =>
      dsimp [List.append] at h
      cases h with
      | wrap_cons fty _ subVal hsub =>
        cases hsub with
        | wrap_cons _ _ leafVal hbare =>
          cases hbare
          rfl
    | cons p1 ps' =>
      dsimp [List.append] at h
      cases h with
      | wrap_cons fty _ subVal hsub =>
        exact ih (by nofun) hsub

theorem ZeroScalarWrappedVal.valueLeafBytes_eq
    {sc : MirAst.ScalarInt} {v : Value} {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) :
    valueLeafBytes v = sc.sizeBytes := by
  induction h with
  | bare => rfl
  | wrap_cons _ _ _ _ ih =>
    simp [valueLeafBytes, valueLeafBytes.valueLeafBytesList, ih]

theorem ZeroScalarWrappedVal.readProjectedValue_eq
    {sc : MirAst.ScalarInt} {v : Value} {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) (locals : List LocalSlot) :
    readProjectedValue locals v projs = .ok (.scalar sc) := by
  induction h with
  | bare => rfl
  | wrap_cons _ _ _ _ ih => exact ih

theorem ZeroScalarWrappedVal.writeProjectedValue_eq
    {sc : MirAst.ScalarInt} {v : Value} {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) (sc' : MirAst.ScalarInt) :
    ∃ v',
      ZeroScalarWrappedVal sc' v' projs ∧
      (∀ locals, writeProjectedValue locals v projs (.scalar sc') = .ok v') ∧
      (projs = [] → v' = .scalar sc') ∧
      (v = .scalar sc → v' = .scalar sc') := by
  induction h with
  | bare =>
    exact ⟨.scalar sc', .bare, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | wrap_cons fty rest subVal _ ih =>
    obtain ⟨subVal', hsub', hw_sub, _, _⟩ := ih
    refine ⟨.aggregate 0 [subVal'], .wrap_cons fty rest subVal' hsub', ?_, ?_, ?_⟩
    · intro locals
      simp [writeProjectedValue, get?, set?, hw_sub locals]
    · intro hnil; cases hnil
    · intro hsc; cases hsc

theorem ZeroScalarWrappedVal.nil_inv
    {sc : MirAst.ScalarInt} {v : Value}
    (h : ZeroScalarWrappedVal sc v []) :
    v = .scalar sc := by
  cases h with
  | bare => rfl

/-- Local allocation specialization for `AnnealMachine`. -/
abbrev AnnealLocalAlloc :=
  Miri.Memory.LocalAllocation
    AnnealProv
    (Option Miri.TreeBorrows.BorrowTree)
    Miri.Memory.MiriMemoryKind

theorem annealReadIndirectImmediate_scalar_ok
    {layouts : LayoutTable} {fty : Ty}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {msc : Miri.Memory.ScalarInt}
    {m : AnnealStepState}
    (hprim : IsPrimScalarTy fty)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (hread : localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange off (translateTy fty layouts).layout.size) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc)) :
    annealReadIndirectImmediate mp (translateTy fty layouts) m =
      .ok ⟨.scalar (.fromScalarInt msc), translateTy fty layouts⟩ m := by
  obtain ⟨_, _, _, _, _, abiSc, hrepr⟩ := hprim.layout_props (layouts := layouts)
  have hnz : ((translateTy fty layouts).layout.size == Miri.ABI.Size.ZERO) = false :=
    beq_false_of_ne (hprim.size_ne_zero (layouts := layouts))
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at hread
  with_unfolding_all
    unfold annealReadIndirectImmediate
    have hf : (translateTy fty layouts).layout.fields = Miri.ABI.FieldsShape.Primitive := IsPrimScalarTy.fields_eq_primitive hprim
    simp only [hf]
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hread]

theorem annealReadIndirectImmediate_scalar_uninit_ub
    {layouts : LayoutTable} {fty : Ty}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {badRange : Miri.Memory.AllocRange}
    {m : AnnealStepState}
    (hprim : IsPrimScalarTy fty)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (huninit : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange off (translateTy fty layouts).layout.size) =
      .ok (.error badRange)) :
    annealReadIndirectImmediate mp (translateTy fty layouts) m =
      .error (.undefinedBehavior "read of uninitialized memory field") m := by
  obtain ⟨_, _, _, _, _, abiSc, hrepr⟩ := hprim.layout_props (layouts := layouts)
  have hnz : ((translateTy fty layouts).layout.size == Miri.ABI.Size.ZERO) = false :=
    beq_false_of_ne (hprim.size_ne_zero (layouts := layouts))
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at huninit
  have hread_err : alloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange off (translateTy fty layouts).layout.size) false =
      .error (.invalidUninitBytes
        (some ⟨Miri.Memory.allocRange off (translateTy fty layouts).layout.size, badRange⟩)) := by
    unfold Miri.Memory.Allocation.initializationMask at huninit
    unfold Miri.Memory.Allocation.readScalar
    simp [huninit, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  with_unfolding_all
    unfold annealReadIndirectImmediate
    have hf : (translateTy fty layouts).layout.fields = Miri.ABI.FieldsShape.Primitive := IsPrimScalarTy.fields_eq_primitive hprim
    simp only [hf]
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hread_err]

theorem annealReadIndirectImmediate_scalarPair_ok
    {lay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff szA szB : Miri.ABI.Size}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {msc0 msc1 : Miri.Memory.ScalarInt}
    {m : AnnealStepState}
    (hnz_lay : lay.layout.size ≠ Miri.ABI.Size.ZERO)
    (hnot_array : ∀ s c, lay.layout.fields ≠ Miri.ABI.FieldsShape.Array s c)
    (hrepr : lay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hszA : a.size annealRuntimeDataLayout = .ok szA)
    (hszB : b.size annealRuntimeDataLayout = .ok szB)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (hread0 : localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange off szA) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc0))
    (hread1 : localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (off.bytes + bOff.bytes)) szB) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc1)) :
    annealReadIndirectImmediate mp lay m =
      .ok ⟨.scalarPair (.fromScalarInt msc0) (.fromScalarInt msc1), lay⟩ m := by
  have hnz : (lay.layout.size == Miri.ABI.Size.ZERO) = false := beq_false_of_ne hnz_lay
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at hread0 hread1
  have hszA' : (a.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO = szA := by
    rw [hszA]; rfl
  have hszB' : (b.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO = szB := by
    rw [hszB]; rfl
  with_unfolding_all
    unfold annealReadIndirectImmediate
    cases hf : lay.layout.fields
    case Array s c => exact False.elim (hnot_array s c hf)
    all_goals
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hszA', hszB', hread0, hread1]

theorem annealReadIndirectImmediate_scalarPair_uninit_ub
    {lay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff szA : Miri.ABI.Size}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {badRange : Miri.Memory.AllocRange}
    {m : AnnealStepState}
    (hnz_lay : lay.layout.size ≠ Miri.ABI.Size.ZERO)
    (hnot_array : ∀ s c, lay.layout.fields ≠ Miri.ABI.FieldsShape.Array s c)
    (hrepr : lay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hszA : a.size annealRuntimeDataLayout = .ok szA)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (huninit : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange off szA) = .ok (.error badRange)) :
    annealReadIndirectImmediate mp lay m =
      .error (.undefinedBehavior "read of uninitialized scalarPair field 0") m := by
  have hnz : (lay.layout.size == Miri.ABI.Size.ZERO) = false := beq_false_of_ne hnz_lay
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]
    dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at huninit
  have hszA' : (a.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO = szA := by
    rw [hszA]; rfl
  have hread_err : alloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange off szA) false =
      .error (.invalidUninitBytes (some ⟨Miri.Memory.allocRange off szA, badRange⟩)) := by
    unfold Miri.Memory.Allocation.initializationMask at huninit
    unfold Miri.Memory.Allocation.readScalar
    simp [huninit, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  with_unfolding_all
    unfold annealReadIndirectImmediate
    cases hf : lay.layout.fields
    case Array s c => exact False.elim (hnot_array s c hf)
    all_goals
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure, EStateM.pure,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hszA', hread_err]

theorem annealReadIndirectImmediate_scalarRepr_ok
    {lay : Miri.Interpreter.LocalLayout} {a : Miri.ABI.Scalar}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {msc : Miri.Memory.ScalarInt}
    {m : AnnealStepState}
    (hnz_lay : lay.layout.size ≠ Miri.ABI.Size.ZERO)
    (hnot_array : ∀ s c, lay.layout.fields ≠ Miri.ABI.FieldsShape.Array s c)
    (hrepr : lay.layout.backendRepr = .Scalar a)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (hread : localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange off lay.layout.size) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc)) :
    annealReadIndirectImmediate mp lay m =
      .ok ⟨.scalar (.fromScalarInt msc), lay⟩ m := by
  have hnz : (lay.layout.size == Miri.ABI.Size.ZERO) = false := beq_false_of_ne hnz_lay
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at hread
  with_unfolding_all
    unfold annealReadIndirectImmediate
    cases hf : lay.layout.fields
    case Array s c => exact False.elim (hnot_array s c hf)
    all_goals
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hread]

theorem annealReadIndirectImmediate_scalarRepr_uninit_ub
    {lay : Miri.Interpreter.LocalLayout} {a : Miri.ABI.Scalar}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {off : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc} {badRange : Miri.Memory.AllocRange}
    {m : AnnealStepState}
    (hnz_lay : lay.layout.size ≠ Miri.ABI.Size.ZERO)
    (hnot_array : ∀ s c, lay.layout.fields ≠ Miri.ABI.FieldsShape.Array s c)
    (hrepr : lay.layout.backendRepr = .Scalar a)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + off.bytes))
    (hlive : m.machine.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc))
    (huninit : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange off lay.layout.size) = .ok (.error badRange)) :
    annealReadIndirectImmediate mp lay m =
      .error (.undefinedBehavior "read of uninitialized memory field") m := by
  have hnz : (lay.layout.size == Miri.ABI.Size.ZERO) = false := beq_false_of_ne hnz_lay
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = off := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr off.bytes, UInt64.add_sub_cancel]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at huninit
  have hread_err : alloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange off lay.layout.size) false =
      .error (.invalidUninitBytes
        (some ⟨Miri.Memory.allocRange off lay.layout.size, badRange⟩)) := by
    unfold Miri.Memory.Allocation.initializationMask at huninit
    unfold Miri.Memory.Allocation.readScalar
    simp [huninit, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  with_unfolding_all
    unfold annealReadIndirectImmediate
    cases hf : lay.layout.fields
    case Array s c => exact False.elim (hnot_array s c hf)
    all_goals
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure, EStateM.pure,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hlive, hnz, Bool.false_eq_true, ↓reduceIte, hrepr, hread_err]

theorem annealEvalOperand_copy_local_live
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hres, hgop]

/-- Build either `Operand.move p` (`isMove = true`) or `Operand.copy p` (`isMove = false`). -/
def mkPlaceOperand (isMove : Bool) (p : Place) : Operand :=
  if isMove then .move p else .copy p

theorem annealEvalOperand_projected_live
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {isMove : Bool} {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    {p : Miri.MIR.ProjectionElem} {ps : List Miri.MIR.ProjectionElem}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts)
    (hnot_single_pair :
      ps ≠ [] ∨ ∀ s0 s1, opVal ≠ .immediate (.scalarPair s0 s1)) :
    annealEvalOperand body.localDecls body.layouts
        (if isMove then .Move ⟨idx, (p :: ps).toArray⟩ else .Copy ⟨idx, (p :: ps).toArray⟩)
        known m =
      annealEvalProjection body.layouts ⟨opVal, translateTy decl.ty body.layouts⟩ (p :: ps)
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  cases isMove <;>
  · with_unfolding_all
      unfold annealEvalOperand
      simp only [Bool.false_eq_true, ↓reduceIte,
        get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
        Option.isNone_some, hres, hgop]
      cases p with
      | Field fidx fty =>
        cases ps with
        | nil =>
          rcases hnot_single_pair with hne_nil | hnot_pair
          · exact False.elim (hne_nil rfl)
          · cases opVal with
            | indirect _ => rfl
            | immediate imm =>
              cases imm with
              | uninit | scalar _ => rfl
              | scalarPair s0 s1 => exact False.elim (hnot_pair s0 s1 rfl)
        | cons _ _ => rfl
      | Deref | PhantomDeref | Index _ | ConstantIndex _ _ _ | Subslice _ _ _ | Downcast _ _
      | OpaqueCast _ | UnwrapUnsafeBinder _ => rfl

theorem annealEvalOperand_projected_scalarPair_single
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {isMove : Bool} {idx : Nat} {decl : LocalDecl}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    {fidx : Nat} {fty : Miri.MIR.TyId}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live (.immediate (.scalarPair s0 s1)), lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts)
    (hfidx : fidx = 0 ∨ fidx = 1) :
    annealEvalOperand body.localDecls body.layouts
        (if isMove then .Move ⟨idx, #[.Field fidx fty]⟩ else .Copy ⟨idx, #[.Field fidx fty]⟩)
        known m =
      .ok ⟨.immediate (.scalar (if fidx == 0 then s0 else s1)),
            ⟨fty, (translateTy decl.ty body.layouts).layout⟩⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  rcases hfidx with rfl | rfl <;> cases isMove <;>
  · with_unfolding_all
      unfold annealEvalOperand
      simp only [Bool.false_eq_true, ↓reduceIte,
        get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
        Option.isNone_some, hres, hgop]
      rfl

theorem annealEvalOperand_projected_dead
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {isMove : Bool} {idx : Nat} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    {projs : Array Miri.MIR.ProjectionElem}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts
        (if isMove then .Move ⟨idx, projs⟩ else .Copy ⟨idx, projs⟩) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  cases isMove <;>
  · with_unfolding_all
      unfold annealEvalOperand
      simp only [Bool.false_eq_true, ↓reduceIte,
        get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
        Option.isNone_some, hres, hgop]
      rfl

/-! ## 2. Aggregate Field Paths, Live Allocation Entries & `StructMemPlaceRel` -/

mutual
  /-- Every leaf inside `Value` is a positive-width scalar and every aggregate
  node is a non-empty variant-`0` aggregate, ensuring `valueLeafBytes` bounds
  tree arities without zero-byte `.unit` padding leaves. -/
  def NoZeroByteLeaves : Value → Prop
    | .scalar sc => 0 < sc.sizeBytes
    | .aggregate 0 (hd :: tl) => NoZeroByteLeaves hd ∧ NoZeroByteLeavesList tl
    | _ => False

  def NoZeroByteLeavesList : List Value → Prop
    | [] => True
    | x :: xs => NoZeroByteLeaves x ∧ NoZeroByteLeavesList xs
end

theorem NoZeroByteLeavesList.set_of_mem {vs : List Value} {idx : Nat} {newV : Value}
    (hlist : NoZeroByteLeavesList vs) (hn : NoZeroByteLeaves newV) :
    NoZeroByteLeavesList (vs.set idx newV) := by
  induction vs generalizing idx with
  | nil => exact True.intro
  | cons hd tl ih =>
    rcases hlist with ⟨hhd, htl⟩
    cases idx with
    | zero => exact ⟨hn, htl⟩
    | succ n => exact ⟨hhd, ih htl⟩

theorem NoZeroByteLeaves.of_set_nonempty {vs : List Value} {idx : Nat} {oldV newV : Value}
    (hget : get? vs idx = some oldV)
    (hroot : NoZeroByteLeaves (.aggregate 0 vs))
    (hn : NoZeroByteLeaves newV) :
    NoZeroByteLeaves (.aggregate 0 (vs.set idx newV)) := by
  cases vs with
  | nil => rw [get?_eq_getElem?] at hget; cases hget
  | cons hd tl =>
    rcases hroot with ⟨hhd, htl⟩
    cases idx with
    | zero => exact ⟨hn, htl⟩
    | succ n => exact ⟨hhd, htl.set_of_mem hn⟩

theorem ZeroScalarWrappedVal.noZeroByteLeaves {sc : MirAst.ScalarInt} {v : Value}
    {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) (hpos : 0 < sc.sizeBytes) :
    NoZeroByteLeaves v := by
  induction h with
  | bare => exact hpos
  | wrap_cons _ _ _ _ ih => exact ⟨ih, True.intro⟩

theorem valueLeafBytesList_set_eq {vs : List Value} {idx : Nat} {oldV newV : Value}
    (hget : get? vs idx = some oldV)
    (heq : valueLeafBytes newV = valueLeafBytes oldV) :
    valueLeafBytes.valueLeafBytesList (vs.set idx newV) =
      valueLeafBytes.valueLeafBytesList vs := by
  induction vs generalizing idx with
  | nil =>
    rw [get?_eq_getElem?] at hget
    cases hget
  | cons hd tl ih =>
    cases idx with
    | zero =>
      rw [get?_eq_getElem?] at hget
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, valueLeafBytes.valueLeafBytesList, heq]
    | succ n =>
      rw [get?_eq_getElem?, List.getElem?_cons_succ, ← get?_eq_getElem?] at hget
      simp [List.set, valueLeafBytes.valueLeafBytesList, ih hget]

/-- Well-formed chain of `.field` projections inside an Anneal `Value.aggregate 0 fields`,
ensuring that every intermediate node along the path is a variant-`0` aggregate
with an in-bounds field index, that any intermediate aggregate whose MIR type
`fty` has `.ScalarPair` backend representation has field length at most `2`, and
that any intermediate aggregate with `.Scalar` backend representation has exact
field length `1` (while `.Memory` sub-structs may have arbitrary arity). -/
inductive ValidAggregateFieldPath (layouts : LayoutTable) :
    Value → List ProjectionElem → Prop where
  | single (fields : List Value) (idx : Nat) (fty : Ty) (oldVal : Value) :
      get? fields idx = some oldVal →
      ValidAggregateFieldPath layouts (.aggregate 0 fields) [.field idx fty]
  | cons (fields : List Value) (idx : Nat) (fty : Ty) (rest : List ProjectionElem)
      (subVal : Value) :
      get? fields idx = some subVal →
      (∀ sf, subVal = .aggregate 0 sf →
        (∀ a b bOff,
          (translateTy fty layouts).layout.backendRepr =
            .ScalarPair (a := a) (b := b) (bOffset := bOff) →
          sf.length ≤ 2) ∧
        (∀ a, (translateTy fty layouts).layout.backendRepr = .Scalar a → sf.length = 1)) →
      ValidAggregateFieldPath layouts subVal rest →
      ValidAggregateFieldPath layouts (.aggregate 0 fields) (.field idx fty :: rest)

/-- Syntactic disjointness of two `.field` projection paths: they diverge at
some `.field` index along their common prefix. -/
inductive DisjointFieldPaths : List ProjectionElem → List ProjectionElem → Prop where
  | diff_head {idx1 idx2 : Nat} {ty1 ty2 : Ty} {rest1 rest2 : List ProjectionElem} :
      idx1 ≠ idx2 →
      DisjointFieldPaths (.field idx1 ty1 :: rest1) (.field idx2 ty2 :: rest2)
  | same_head {idx : Nat} {ty1 ty2 : Ty} {rest1 rest2 : List ProjectionElem} :
      DisjointFieldPaths rest1 rest2 →
      DisjointFieldPaths (.field idx ty1 :: rest1) (.field idx ty2 :: rest2)

theorem DisjointFieldPaths.symm {p q : List ProjectionElem}
    (h : DisjointFieldPaths p q) : DisjointFieldPaths q p := by
  induction h with
  | diff_head hne => exact .diff_head (Ne.symm hne)
  | same_head _ ih => exact .same_head ih

theorem ValidAggregateFieldPath.nonempty_agg
    {layouts : LayoutTable} {rootVal : Value} {projs : List ProjectionElem}
    (h : ValidAggregateFieldPath layouts rootVal projs) :
    ∃ hd tl, rootVal = .aggregate 0 (hd :: tl) := by
  cases h with
  | single fields _ _ _ hget =>
    cases fields with
    | nil => rw [get?_eq_getElem?] at hget; cases hget
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  | cons fields _ _ _ _ hget _ _ =>
    cases fields with
    | nil => rw [get?_eq_getElem?] at hget; cases hget
    | cons hd tl => exact ⟨hd, tl, rfl⟩

theorem ValidAggregateFieldPath.readProjectedValue_indep
    {layouts : LayoutTable} {rootVal : Value} {projs : List ProjectionElem}
    (h : ValidAggregateFieldPath layouts rootVal projs)
    (locals : List LocalSlot) :
    readProjectedValue locals rootVal projs = readProjectedValue [] rootVal projs := by
  induction h with
  | single fields idx fty oldVal hget =>
    simp [readProjectedValue, hget]
  | cons fields idx fty rest subVal hget _ _ ih =>
    simp [readProjectedValue, hget, ih]

theorem ValidAggregateFieldPath.writeProjectedValue_agg_length_eq
    {layouts : LayoutTable} {rootVal newVal rootVal' : Value} {projs : List ProjectionElem}
    (h : ValidAggregateFieldPath layouts rootVal projs)
    (hw : writeProjectedValue [] rootVal projs newVal = .ok rootVal') :
    ∀ sf sf', rootVal = .aggregate 0 sf → rootVal' = .aggregate 0 sf' → sf'.length = sf.length := by
  cases h with
  | single fields idx fty oldVal hget =>
    intro sf sf' h1 h2
    injection h1 with _ hsf; subst hsf
    dsimp [writeProjectedValue] at hw
    rw [hget] at hw; dsimp only at hw
    have hlt : idx < fields.length := by
      rw [get?_eq_getElem?] at hget
      exact (List.getElem?_eq_some_iff.mp hget).1
    have hset : set? fields idx newVal = some (fields.set idx newVal) := by
      simp [set?, hlt]
    rw [hset] at hw
    injection hw with hr; subst hr
    injection h2 with _ hsf'; subst hsf'
    exact List.length_set
  | cons fields idx fty rest subVal hget _ _ =>
    intro sf sf' h1 h2
    injection h1 with _ hsf; subst hsf
    dsimp [writeProjectedValue] at hw
    rw [hget] at hw; dsimp only at hw
    cases hw_s : writeProjectedValue [] subVal rest newVal with
    | ub | unsupported => rw [hw_s] at hw; cases hw
    | ok subVal' =>
      rw [hw_s] at hw; dsimp only at hw
      have hlt : idx < fields.length := by
        rw [get?_eq_getElem?] at hget
        exact (List.getElem?_eq_some_iff.mp hget).1
      have hset : set? fields idx subVal' = some (fields.set idx subVal') := by
        simp [set?, hlt]
      rw [hset] at hw
      injection hw with hr; subst hr
      injection h2 with _ hsf'; subst hsf'
      exact List.length_set

theorem ValidAggregateFieldPath.writeProjectedValue_spec
    {layouts : LayoutTable} {rootVal : Value} {projs : List ProjectionElem}
    (h : ValidAggregateFieldPath layouts rootVal projs)
    (newVal : Value) :
    ∃ oldVal rootVal',
      readProjectedValue [] rootVal projs = .ok oldVal ∧
      (∀ locals, writeProjectedValue locals rootVal projs newVal = .ok rootVal') ∧
      ValidAggregateFieldPath layouts rootVal' projs ∧
      (valueLeafBytes newVal = valueLeafBytes oldVal →
        valueLeafBytes rootVal' = valueLeafBytes rootVal) ∧
      (∀ locals, readProjectedValue locals rootVal' projs = .ok newVal) ∧
      (∀ rest,
        readProjectedValue [] rootVal' (projs ++ rest) = readProjectedValue [] newVal rest ∧
        ((∀ sf_old sf_new, oldVal = .aggregate 0 sf_old → newVal = .aggregate 0 sf_new →
            sf_new.length = sf_old.length) →
          ValidAggregateFieldPath layouts rootVal (projs ++ rest) →
          ValidAggregateFieldPath layouts newVal rest →
          ValidAggregateFieldPath layouts rootVal' (projs ++ rest))) ∧
      (∀ q, DisjointFieldPaths projs q →
        (∀ locals, readProjectedValue locals rootVal' q = readProjectedValue locals rootVal q) ∧
        (ValidAggregateFieldPath layouts rootVal q → ValidAggregateFieldPath layouts rootVal' q)) := by
  induction h with
  | single fields idx fty oldVal hget =>
    have hlt : idx < fields.length := by
      rw [get?_eq_getElem?] at hget
      exact (List.getElem?_eq_some_iff.mp hget).1
    have hset : set? fields idx newVal = some (fields.set idx newVal) := by
      simp [set?, hlt]
    have hget_new : get? (fields.set idx newVal) idx = some newVal := by
      simp [get?, List.getElem?_set_self hlt]
    have hpath' : ValidAggregateFieldPath layouts (.aggregate 0 (fields.set idx newVal)) [.field idx fty] :=
      .single (fields.set idx newVal) idx fty newVal hget_new
    refine ⟨oldVal, .aggregate 0 (fields.set idx newVal), ?_, ?_, hpath', ?_, ?_, ?_, ?_⟩
    · simp [readProjectedValue, hget]
    · intro locals
      dsimp [writeProjectedValue]
      rw [hget]
      dsimp only
      rw [hset]
    · intro hbytes
      simp [valueLeafBytes, valueLeafBytesList_set_eq hget hbytes]
    · intro locals
      dsimp [readProjectedValue]
      rw [hget_new]
    · intro rest
      refine ⟨?_, ?_⟩
      · dsimp [List.append, readProjectedValue]
        rw [hget_new]
      · intro hnew_len hold_app hrest
        dsimp [List.append] at hold_app ⊢
        cases hold_app with
        | single _ _ _ _ _ => cases hrest
        | cons _ _ _ _ sub0 hget0 hsub0_len hsub0 =>
          rw [hget] at hget0
          injection hget0 with hsub0_eq; subst hsub0_eq
          refine .cons (fields.set idx newVal) idx fty rest newVal hget_new ?_ hrest
          intro sf_new hsf_new
          obtain ⟨hd_o, tl_o, hagg_o⟩ := hsub0.nonempty_agg
          rw [hnew_len (hd_o :: tl_o) sf_new hagg_o hsf_new]
          exact hsub0_len (hd_o :: tl_o) hagg_o
    · intro q hdisj
      cases hdisj with
      | diff_head hne =>
        rename_i idx2 ty2 rest2
        have hget_other : get? (fields.set idx newVal) idx2 = get? fields idx2 := by
          simp [get?, List.getElem?_set_ne hne]
        refine ⟨?_, ?_⟩
        · intro locals
          dsimp [readProjectedValue]
          rw [hget_other]
        · intro hq
          cases hq with
          | single _ _ _ old2 hget2 =>
            rw [← hget_other] at hget2
            exact .single _ _ _ _ hget2
          | cons _ _ _ _ sub2 hget2 hsub2_len hsub2 =>
            rw [← hget_other] at hget2
            exact .cons _ _ _ _ _ hget2 hsub2_len hsub2
      | same_head hdisj_rest =>
        cases hdisj_rest
  | cons fields idx fty rest subVal hget hsub_len hsub ih =>
    obtain ⟨oldVal, subVal', hread_old, hw_sub, hpath_sub', hbytes_sub, hread_sub,
      happend_sub, hdisj_sub⟩ := ih
    have hsub'_len : ∀ sf, subVal' = .aggregate 0 sf →
        (∀ a b bOff,
          (translateTy fty layouts).layout.backendRepr =
            .ScalarPair (a := a) (b := b) (bOffset := bOff) →
          sf.length ≤ 2) ∧
        (∀ a, (translateTy fty layouts).layout.backendRepr = .Scalar a → sf.length = 1) := by
      intro sf' hsf'
      obtain ⟨hd, tl, hagg⟩ := hsub.nonempty_agg
      rw [hsub.writeProjectedValue_agg_length_eq (hw_sub []) (hd :: tl) sf' hagg hsf']
      exact hsub_len (hd :: tl) hagg
    have hlt : idx < fields.length := by
      rw [get?_eq_getElem?] at hget
      exact (List.getElem?_eq_some_iff.mp hget).1
    have hset : set? fields idx subVal' = some (fields.set idx subVal') := by
      simp [set?, hlt]
    have hget_new : get? (fields.set idx subVal') idx = some subVal' := by
      simp [get?, List.getElem?_set_self hlt]
    have hpath' : ValidAggregateFieldPath layouts (.aggregate 0 (fields.set idx subVal'))
        (.field idx fty :: rest) :=
      .cons (fields.set idx subVal') idx fty rest subVal' hget_new hsub'_len hpath_sub'
    refine ⟨oldVal, .aggregate 0 (fields.set idx subVal'), ?_, ?_, hpath', ?_, ?_, ?_, ?_⟩
    · dsimp [readProjectedValue]
      rw [hget]
      exact hread_old
    · intro locals
      dsimp [writeProjectedValue]
      rw [hget]
      dsimp only
      rw [hw_sub locals]
      dsimp only
      rw [hset]
    · intro hbytes
      simp [valueLeafBytes, valueLeafBytesList_set_eq hget (hbytes_sub hbytes)]
    · intro locals
      dsimp [readProjectedValue]
      rw [hget_new]
      exact hread_sub locals
    · intro tail
      obtain ⟨hr_tail, hp_tail⟩ := happend_sub tail
      refine ⟨?_, ?_⟩
      · dsimp [List.append, readProjectedValue]
        rw [hget_new]
        exact hr_tail
      · intro hnew_len hold_app htail
        cases rest with
        | nil => cases hsub
        | cons r0 rs =>
          dsimp [List.append] at hold_app ⊢
          cases hold_app with
          | cons _ _ _ _ sub0 hget0 _ hsub0_app =>
            rw [hget] at hget0
            injection hget0 with hsub0_eq; subst hsub0_eq
            exact .cons (fields.set idx subVal') idx fty ((r0 :: rs) ++ tail) subVal'
              hget_new hsub'_len (hp_tail hnew_len hsub0_app htail)
    · intro q hdisj
      cases hdisj with
      | diff_head hne =>
        rename_i idx2 ty2 rest2
        have hget_other : get? (fields.set idx subVal') idx2 = get? fields idx2 := by
          simp [get?, List.getElem?_set_ne hne]
        refine ⟨?_, ?_⟩
        · intro locals
          dsimp [readProjectedValue]
          rw [hget_other]
        · intro hq
          cases hq with
          | single _ _ _ old2 hget2 =>
            rw [← hget_other] at hget2
            exact .single _ _ _ _ hget2
          | cons _ _ _ _ sub2 hget2 hsub2_len hsub2 =>
            rw [← hget_other] at hget2
            exact .cons _ _ _ _ _ hget2 hsub2_len hsub2
      | same_head hdisj_rest =>
        rename_i ty2 rest2
        obtain ⟨hread_q, hpath_q⟩ := hdisj_sub rest2 hdisj_rest
        refine ⟨?_, ?_⟩
        · intro locals
          dsimp [readProjectedValue]
          rw [hget_new, hget]
          exact hread_q locals
        · intro hq
          cases hq with
          | single _ _ _ _ _ =>
            cases hdisj_rest
          | cons _ _ _ _ sub2 hget2 hsub2_len hsub2 =>
            rw [hget] at hget2
            injection hget2 with hsub_eq
            subst hsub_eq
            have hsub2'_len : ∀ sf, subVal' = .aggregate 0 sf →
                (∀ a b bOff,
                  (translateTy ty2 layouts).layout.backendRepr =
                    .ScalarPair (a := a) (b := b) (bOffset := bOff) →
                  sf.length ≤ 2) ∧
                (∀ a, (translateTy ty2 layouts).layout.backendRepr = .Scalar a → sf.length = 1) := by
              intro sf' hsf'
              obtain ⟨hd, tl, hagg⟩ := hsub.nonempty_agg
              rw [hsub.writeProjectedValue_agg_length_eq (hw_sub []) (hd :: tl) sf' hagg hsf']
              exact hsub2_len (hd :: tl) hagg
            exact .cons _ _ _ _ _ hget_new hsub2'_len (hpath_q hsub2)

theorem ValidAggregateFieldPath.prefix_of_append {layouts : LayoutTable} :
    ∀ {projs rest : List ProjectionElem} {rootVal : Value},
      projs ≠ [] →
      rest ≠ [] →
      ValidAggregateFieldPath layouts rootVal (projs ++ rest) →
      ∃ subVal subIdx subTy,
        projs.getLast? = some (.field subIdx subTy) ∧
        ValidAggregateFieldPath layouts rootVal projs ∧
        readProjectedValue [] rootVal projs = .ok subVal ∧
        (∀ sf, subVal = .aggregate 0 sf →
          (∀ a b bOff,
            (translateTy subTy layouts).layout.backendRepr =
              .ScalarPair (a := a) (b := b) (bOffset := bOff) →
            sf.length ≤ 2) ∧
          (∀ a, (translateTy subTy layouts).layout.backendRepr = .Scalar a → sf.length = 1)) ∧
        ValidAggregateFieldPath layouts subVal rest ∧
        readProjectedValue [] rootVal (projs ++ rest) = readProjectedValue [] subVal rest
  | [], _, _, hne, _, _ => False.elim (hne rfl)
  | [_], _ :: _, _, _, _, h => by
    dsimp [List.append] at h
    cases h with
    | cons fields idx fty _ subVal hget hsub_len hsub =>
      refine ⟨subVal, idx, fty, rfl, .single fields idx fty subVal hget, ?_, hsub_len, hsub, ?_⟩
      · simp [readProjectedValue, hget]
      · simp [readProjectedValue, hget]
  | _ :: p1 :: ps, q :: qs, _, _, hrest_ne, h => by
    dsimp [List.append] at h
    cases h with
    | cons fields idx fty _ subVal0 hget0 hsub0_len hsub0 =>
      obtain ⟨subVal, subIdx, subTy, hlast, hp_pre, hr_pre, hsub_len, hp_rest, hr_rest⟩ :=
        ValidAggregateFieldPath.prefix_of_append
          (projs := p1 :: ps) (rest := q :: qs) (by nofun) hrest_ne hsub0
      refine ⟨subVal, subIdx, subTy, hlast,
        .cons fields idx fty (p1 :: ps) subVal0 hget0 hsub0_len hp_pre,
        ?_, hsub_len, hp_rest, ?_⟩
      · dsimp [readProjectedValue]; rw [hget0]; exact hr_pre
      · dsimp [List.append, readProjectedValue]; rw [hget0]; exact hr_rest

theorem ValidAggregateFieldPath.read_substruct_scalarPair
    {layouts : LayoutTable} {rootVal : Value} {projs : List ProjectionElem}
    {subIdx : Nat} {subTy mid₀ mid₁ : Ty}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {sc₀ sc₁ : MirAst.ScalarInt}
    (hprojs_ne : projs ≠ [])
    (hlast : projs.getLast? = some (.field subIdx subTy))
    (hrepr : (translateTy subTy layouts).layout.backendRepr =
      .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hp0 : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 0 mid₀]))
    (hr0 : readProjectedValue [] rootVal (projs ++ [.field 0 mid₀]) = .ok (.scalar sc₀))
    (hp1 : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 1 mid₁]))
    (hr1 : readProjectedValue [] rootVal (projs ++ [.field 1 mid₁]) = .ok (.scalar sc₁)) :
    ValidAggregateFieldPath layouts rootVal projs ∧
    (∀ locals, readProjectedValue locals rootVal projs =
      .ok (.aggregate 0 [.scalar sc₀, .scalar sc₁])) := by
  obtain ⟨subVal0, subIdx', subTy', hlast', hvpath_p, hr_p0, hsub_len, hp_sub0, hr_eq0⟩ :=
    ValidAggregateFieldPath.prefix_of_append hprojs_ne (by nofun) hp0
  obtain ⟨subVal1, _, _, _, _, hr_p1, _, hp_sub1, hr_eq1⟩ :=
    ValidAggregateFieldPath.prefix_of_append hprojs_ne (by nofun) hp1
  rw [hlast] at hlast'
  injection hlast' with hfeq
  injection hfeq with _ hty_eq
  subst hty_eq
  rw [hr_p0] at hr_p1
  injection hr_p1 with hsub_eq; subst hsub_eq
  rw [hr0] at hr_eq0
  rw [hr1] at hr_eq1
  cases hp_sub0 with
  | cons _ _ _ _ _ _ _ hnil => cases hnil
  | single sf0 _ _ old0 hget0 =>
    cases hp_sub1 with
    | cons _ _ _ _ _ _ _ hnil => cases hnil
    | single sf1 _ _ old1 hget1 =>
      have hlen_le := (hsub_len sf0 rfl).1 a b bOff hrepr
      dsimp [readProjectedValue] at hr_eq0 hr_eq1
      rw [hget0] at hr_eq0
      rw [hget1] at hr_eq1
      cases sf0 with
      | nil => rw [get?_eq_getElem?] at hget0; cases hget0
      | cons u0 tl0 =>
        rw [get?_eq_getElem?, List.getElem?_cons_zero, Option.some.injEq] at hget0; subst hget0
        injection hr_eq0.symm with hu0; subst hu0
        cases tl0 with
        | nil => rw [get?_eq_getElem?] at hget1; cases hget1
        | cons u1 tl1 =>
          rw [get?_eq_getElem?, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hget1; subst hget1
          injection hr_eq1.symm with hu1; subst hu1
          cases tl1 with
          | cons _ _ => simp at hlen_le
          | nil =>
            exact ⟨hvpath_p, fun locals => (hvpath_p.readProjectedValue_indep locals).trans hr_p0⟩

theorem ValidAggregateFieldPath.read_substruct_scalarWrap
    {layouts : LayoutTable} {rootVal : Value} {projs : List ProjectionElem}
    {subIdx : Nat} {subTy mid₀ : Ty} {a : Miri.ABI.Scalar}
    {sc₀ : MirAst.ScalarInt}
    (hprojs_ne : projs ≠ [])
    (hlast : projs.getLast? = some (.field subIdx subTy))
    (hrepr : (translateTy subTy layouts).layout.backendRepr = .Scalar a)
    (hp0 : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 0 mid₀]))
    (hr0 : readProjectedValue [] rootVal (projs ++ [.field 0 mid₀]) = .ok (.scalar sc₀)) :
    ValidAggregateFieldPath layouts rootVal projs ∧
    (∀ locals, readProjectedValue locals rootVal projs =
      .ok (.aggregate 0 [.scalar sc₀])) := by
  obtain ⟨subVal0, subIdx', subTy', hlast', hvpath_p, hr_p0, hsub_len, hp_sub0, hr_eq0⟩ :=
    ValidAggregateFieldPath.prefix_of_append hprojs_ne (by nofun) hp0
  rw [hlast] at hlast'
  injection hlast' with hfeq
  injection hfeq with _ hty_eq
  subst hty_eq
  rw [hr0] at hr_eq0
  cases hp_sub0 with
  | cons _ _ _ _ _ _ _ hnil => cases hnil
  | single sf0 _ _ old0 hget0 =>
    have hlen_eq := (hsub_len sf0 rfl).2 a hrepr
    dsimp [readProjectedValue] at hr_eq0
    rw [hget0] at hr_eq0
    cases sf0 with
    | nil => rw [get?_eq_getElem?] at hget0; cases hget0
    | cons u0 tl0 =>
      rw [get?_eq_getElem?, List.getElem?_cons_zero, Option.some.injEq] at hget0; subst hget0
      injection hr_eq0.symm with hu0; subst hu0
      cases tl0 with
      | cons _ _ => simp at hlen_eq
      | nil =>
        exact ⟨hvpath_p, fun locals => (hvpath_p.readProjectedValue_indep locals).trans hr_p0⟩

/-- `(id, la)` is the first entry for `id` in `live`, so both `find?` (used by
`annealReadIndirectImmediate`) and `findIdx?` (used by `annealWriteIndirectImmediate`)
resolve to `(id, la)`. -/
def LiveAllocEntry (live : Array (Miri.Memory.AllocId × AnnealLocalAlloc))
    (id : Miri.Memory.AllocId) (la : AnnealLocalAlloc) : Prop :=
  live.find? (fun (k, _) => k == id) = some (id, la) ∧
  ∃ idx, ∃ (hidx : idx < live.size),
    live.findIdx? (fun (k, _) => k == id) = some idx ∧
    live[idx]'hidx = (id, la)

namespace LiveAllocEntry

private theorem array_findIdx?_eq_toList {α : Type} (xs : Array α) (p : α → Bool) :
    xs.findIdx? p = xs.toList.findIdx? p := by
  rcases xs with ⟨l⟩
  exact List.findIdx?_toArray p l

theorem mem_toList {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} {la : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la) :
    (id, la) ∈ live.toList := by
  obtain ⟨_, idx, hidx, _, hget⟩ := h
  rw [← hget]
  exact Array.getElem_mem_toList hidx

theorem any_true {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} {la : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la) :
    live.any (fun entry => entry.1 == id) = true := by
  obtain ⟨_, idx, hidx, _, hget⟩ := h
  rw [Array.any_eq_true]
  exact ⟨idx, hidx, by rw [hget]; simp⟩

theorem of_push_fresh_self {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} (la : AnnealLocalAlloc)
    (hfresh : live.any (fun entry => entry.1 == id) = false) :
    LiveAllocEntry (live.push (id, la)) id la := by
  have hfidx := findIdx?_push_fresh live id la hfresh
  have hfind_none : live.find? (fun (k, _) => k == id) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
    have hfalse := (Array.any_eq_false.mp hfresh) i hi
    rcases x with ⟨k, v⟩
    rw [hxi] at hfalse
    simpa using hfalse
  refine ⟨?_, live.size, by simp, hfidx, by simp⟩
  rw [Array.find?_push, hfind_none]
  simp

theorem of_push_other {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} {la : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la)
    (entry : Miri.Memory.AllocId × AnnealLocalAlloc) :
    LiveAllocEntry (live.push entry) id la := by
  obtain ⟨hfind, idx, hidx, hfidx, hget⟩ := h
  refine ⟨?_, idx, by simp; omega, ?_, ?_⟩
  · rw [Array.find?_push, hfind]; rfl
  · rw [Array.findIdx?_push, hfidx]; rfl
  · rw [Array.getElem_push_lt hidx]; exact hget

private theorem list_find_set_self {l : List (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} {la la' : AnnealLocalAlloc} {idx : Nat}
    (hfind : l.find? (fun (k, _) => k == id) = some (id, la))
    (hfidx : l.findIdx? (fun (k, _) => k == id) = some idx) :
    (l.set idx (id, la')).find? (fun (k, _) => k == id) = some (id, la') ∧
    (l.set idx (id, la')).findIdx? (fun (k, _) => k == id) = some idx := by
  induction l generalizing idx with
  | nil => cases hfidx
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk : (k == id) = true
    · simp only [List.findIdx?_cons, hk, ↓reduceIte, Option.some.injEq] at hfidx
      subst hfidx
      simp [List.set, List.findIdx?_cons]
    · have hk_f : (k == id) = false := Bool.eq_false_iff.mpr hk
      simp only [List.find?, hk_f] at hfind
      simp only [List.findIdx?_cons, hk_f, Bool.false_eq_true, ↓reduceIte,
        Option.map_eq_some_iff] at hfidx
      obtain ⟨idx', hidx', rfl⟩ := hfidx
      obtain ⟨hf', hfi'⟩ := ih hfind hidx'
      simp [List.set, List.findIdx?_cons, hk_f, hf', hfi']

theorem of_set!_self {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id : Miri.Memory.AllocId} {la : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la)
    {idx : Nat} (hidx : idx < live.size)
    (hfidx : live.findIdx? (fun (k, _) => k == id) = some idx)
    (la' : AnnealLocalAlloc) :
    LiveAllocEntry (live.set! idx (id, la')) id la' := by
  obtain ⟨hfind, _⟩ := h
  rw [Array.set!_eq_setIfInBounds]
  have hfind_l : live.toList.find? (fun (k, _) => k == id) = some (id, la) := by
    rwa [← Array.find?_toList] at hfind
  have hfidx_l : live.toList.findIdx? (fun (k, _) => k == id) = some idx := by
    rwa [array_findIdx?_eq_toList] at hfidx
  obtain ⟨hf', hfi'⟩ := list_find_set_self hfind_l hfidx_l
  have htoList : (live.setIfInBounds idx (id, la')).toList = live.toList.set idx (id, la') := by
    simp [Array.toList_setIfInBounds]
  refine ⟨?_, idx, by simp [hidx], ?_, ?_⟩
  · rw [← Array.find?_toList, htoList]; exact hf'
  · rw [array_findIdx?_eq_toList, htoList]; exact hfi'
  · simp

private theorem list_find_set_ne {l : List (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id updId : Miri.Memory.AllocId} {la oldLa newLa : AnnealLocalAlloc}
    {idx u : Nat} (hne : updId ≠ id)
    (hu : l[u]? = some (updId, oldLa))
    (hfind : l.find? (fun (k, _) => k == id) = some (id, la))
    (hfidx : l.findIdx? (fun (k, _) => k == id) = some idx) :
    (l.set u (updId, newLa)).find? (fun (k, _) => k == id) = some (id, la) ∧
    (l.set u (updId, newLa)).findIdx? (fun (k, _) => k == id) = some idx ∧
    u ≠ idx := by
  induction l generalizing idx u with
  | nil => cases hu
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    cases u with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hu
      rcases hu with ⟨rfl, rfl⟩
      have hne_b : (k == id) = false := beq_false_of_ne hne
      simp only [List.find?, hne_b] at hfind
      simp only [List.findIdx?_cons, hne_b, Bool.false_eq_true, ↓reduceIte,
        Option.map_eq_some_iff] at hfidx
      obtain ⟨idx', hidx', rfl⟩ := hfidx
      simp [List.set, List.findIdx?_cons, hne_b, hfind, hidx']
    | succ u' =>
      simp only [List.getElem?_cons_succ] at hu
      by_cases hk : (k == id) = true
      · simp only [List.find?, hk, Option.some.injEq, Prod.mk.injEq] at hfind
        simp only [List.findIdx?_cons, hk, ↓reduceIte, Option.some.injEq] at hfidx
        subst hfidx
        rcases hfind with ⟨rfl, rfl⟩
        simp [List.set, List.findIdx?_cons]
      · have hk_f : (k == id) = false := Bool.eq_false_iff.mpr hk
        simp only [List.find?, hk_f] at hfind
        simp only [List.findIdx?_cons, hk_f, Bool.false_eq_true, ↓reduceIte,
          Option.map_eq_some_iff] at hfidx
        obtain ⟨idx', hidx', rfl⟩ := hfidx
        obtain ⟨hf', hfi', hne_u⟩ := ih hu hfind hidx'
        refine ⟨?_, ?_, by omega⟩
        · simp [List.set, hk_f, hf']
        · simp [List.set, List.findIdx?_cons, hk_f, hfi']

theorem of_set!_ne {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id updId : Miri.Memory.AllocId} {la oldLa : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la)
    {u : Nat} (hu_lt : u < live.size)
    (hu_eq : live[u]'hu_lt = (updId, oldLa))
    (hne : updId ≠ id)
    (newLa : AnnealLocalAlloc) :
    LiveAllocEntry (live.set! u (updId, newLa)) id la := by
  obtain ⟨hfind, idx, hidx, hfidx, hget⟩ := h
  rw [Array.set!_eq_setIfInBounds]
  have hu_l : live.toList[u]? = some (updId, oldLa) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hu_lt, hu_eq]
  have hfind_l : live.toList.find? (fun (k, _) => k == id) = some (id, la) := by
    rwa [← Array.find?_toList] at hfind
  have hfidx_l : live.toList.findIdx? (fun (k, _) => k == id) = some idx := by
    rwa [array_findIdx?_eq_toList] at hfidx
  obtain ⟨hf', hfi', hne_idx⟩ := list_find_set_ne hne hu_l hfind_l hfidx_l
  have htoList : (live.setIfInBounds u (updId, newLa)).toList = live.toList.set u (updId, newLa) := by
    simp [Array.toList_setIfInBounds]
  refine ⟨?_, idx, by simp [hidx], ?_, ?_⟩
  · rw [← Array.find?_toList, htoList]; exact hf'
  · rw [array_findIdx?_eq_toList, htoList]; exact hfi'
  · simp [hne_idx, hidx, hget]

private theorem list_find_filter_ne {l : List (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id deadId : Miri.Memory.AllocId} {la : AnnealLocalAlloc} {idx : Nat}
    (hne : id ≠ deadId)
    (hfidx : l.findIdx? (fun (k, _) => k == id) = some idx)
    (hget : l[idx]? = some (id, la)) :
    let l' := l.filter (fun entry => entry.1 != deadId)
    l'.find? (fun (k, _) => k == id) = some (id, la) ∧
    ∃ idx', l'.findIdx? (fun (k, _) => k == id) = some idx' ∧
      l'[idx']? = some (id, la) := by
  induction l generalizing idx with
  | nil => cases hfidx
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk : (k == id) = true
    · simp only [List.findIdx?_cons, hk] at hfidx
      injection hfidx with hzero
      subst hzero
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      rcases hget with ⟨rfl, rfl⟩
      have hne_b : (k != deadId) = true := bne_iff_ne.mpr hne
      dsimp only [List.filter]
      rw [hne_b]
      exact ⟨by simp [List.find?], 0, by simp [List.findIdx?_cons], rfl⟩
    · have hk_f : (k == id) = false := Bool.eq_false_iff.mpr hk
      simp only [List.findIdx?_cons, hk_f, Bool.false_eq_true, ↓reduceIte,
        Option.map_eq_some_iff] at hfidx
      obtain ⟨idx', hidx', rfl⟩ := hfidx
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨hf', idx'', hfi'', hg''⟩ := ih hidx' hget
      dsimp only [List.filter]
      cases hkeep : (k != deadId)
      · exact ⟨hf', idx'', hfi'', hg''⟩
      · refine ⟨?_, idx'' + 1, ?_, hg''⟩
        · simp only [List.find?, hk_f]; exact hf'
        · simp only [List.findIdx?_cons, hk_f, hfi'']; rfl

theorem of_filter_ne {live : Array (Miri.Memory.AllocId × AnnealLocalAlloc)}
    {id deadId : Miri.Memory.AllocId} {la : AnnealLocalAlloc}
    (h : LiveAllocEntry live id la)
    (hne : id ≠ deadId) :
    LiveAllocEntry (live.filter (fun entry => entry.1 != deadId)) id la := by
  obtain ⟨_, idx, hidx, hfidx, hget⟩ := h
  have hfidx_l : live.toList.findIdx? (fun (k, _) => k == id) = some idx := by
    rwa [array_findIdx?_eq_toList] at hfidx
  have hget_l : live.toList[idx]? = some (id, la) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hidx, hget]
  obtain ⟨hf', idx', hfi', hg'⟩ := list_find_filter_ne hne hfidx_l hget_l
  let live' := live.filter (fun entry => entry.1 != deadId)
  have htoList : live'.toList = live.toList.filter (fun entry => entry.1 != deadId) :=
    Array.toList_filter
  have hg_arr : live'[idx']? = some (id, la) := by
    rw [← Array.getElem?_toList, htoList]; exact hg'
  obtain ⟨hidx', hget'⟩ := Array.getElem?_eq_some_iff.mp hg_arr
  refine ⟨?_, idx', hidx', ?_, hget'⟩
  · rw [← Array.find?_toList, htoList]; exact hf'
  · rw [array_findIdx?_eq_toList, htoList]; exact hfi'

end LiveAllocEntry

/-- Machine state after replacing the live allocation at index `idx` with `alloc'`. -/
def updateAllocMachine (mach : AnnealMachine) (idx : Nat)
    (allocId : Miri.Memory.AllocId)
    (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealMachine :=
  { mach with
    memory := { mach.memory with live := mach.memory.live.set! idx (allocId, ⟨kind, alloc'⟩) } }

/-- Field-granular memory-place correspondence for a non-empty aggregate value
`rootVal = .aggregate 0 (hd :: tl)` (both **unpadded** and **padded** tuples/structs)
stored in a live mutable `Miri.Memory.Allocation` at relative offset `0`.

* Each leaf `i < fields.length` has non-empty projection path `paths[i]`,
  `ValidAggregateFieldPath rootVal paths[i] (.scalar sc_i)`, initialized byte
  range in `word` (`InitMaskWordRel`), and `readScalar` returning `msc_i`.
* Every padding byte `p` (`isStructPaddingByte fields layout.size p`) remains
  uninitialized (`initializationMask.get p = .ok false`).
* There is no 64-byte single-`MaskBlock` cap: multi-block allocations of any size
  `< 2 ^ 32` (4 GiB) are supported via `InitMaskWordRel` (`blockIdx = b / 64`,
  `bitIdx = b % 64`). The `< 2 ^ 32` bound comes from
  `annealStackBaseAddr id = id <<< 32`, which spaces stack allocations by
  `2 ^ 32` bytes (4 GiB) so allocations `< 2 ^ 32` bytes never wrap 64-bit
  addresses or overlap while `id < 2 ^ 32`.
* `leafBytes_eq : valueLeafBytes rootVal = structSumFieldBytes fields` ties the
  value to the leaf descriptors. An unpadded aggregate (every byte belongs to a
  leaf) therefore has its whole byte range initialized and projects to the base
  `MemPlaceRel mach ty layouts (some rootVal) mp` (`StructMemPlaceRel.toMemPlaceRel`).
  A padded aggregate keeps its padding bytes uninitialized, so it has no base
  `LocalRel.indirect` counterpart and is tracked only by `LocalRelLM2_2.structInd`;
  the shared base relation (`Relation.lean`) is left unchanged by `LM-2.2`. -/

inductive StructMemPlaceRel
    (mach : AnnealMachine)
    (ty : Ty)
    (layouts : LayoutTable)
    (fields : List StructFieldDesc)
    (paths : List (List ProjectionElem))
    (rootVal : Value)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (words : Array UInt64)
      (valid_layout : ValidStructLayout (translateTy ty layouts).layout fields)
      (paths_len : paths.length = fields.length)
      (rootVal_agg : (∃ hd tl, rootVal = .aggregate 0 (hd :: tl)) ∧ NoZeroByteLeaves rootVal)
      (leafBytes_eq : valueLeafBytes rootVal = structSumFieldBytes fields)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_entry : LiveAllocEntry mach.memory.live allocId localAlloc)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow :
        baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
      (mut_alloc : localAlloc.allocation.mutability = .Mut)
      (aligned_ptr :
        mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
      (byteSize_eq :
        localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
      (alloc_len_eq :
        localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
      (prov_empty :
        localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (mask_rel :
        InitMaskWordRel localAlloc.allocation.initializationMask
          localAlloc.allocation.byteSize words)
      (word_bits_init :
        ∀ i (hi : i < fields.length) b,
          (fields[i]'hi).offset.bytes.toNat ≤ b →
          b < (fields[i]'hi).offset.bytes.toNat +
            (fields[i]'hi).fieldLayout.size.bytes.toNat →
          maskBlocksGetBit words b = true)
      (fields_rel :
        ∀ (i : Nat) (hi : i < fields.length),
          let f := fields[i]'hi
          let path := paths[i]'(by rw [paths_len]; exact hi)
          path ≠ [] ∧
          f.fieldLayout = (translateTy f.ty layouts).layout ∧
          IsPrimScalarTy f.ty ∧
          ValidAggregateFieldPath layouts rootVal path ∧
          ∃ sc msc,
            readProjectedValue [] rootVal path = .ok (.scalar sc) ∧
            ScalarRel sc msc ∧
            f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
            (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
            (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
            localAlloc.allocation.initializationMask.isRangeInitialized
              (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
            localAlloc.allocation.readScalar
              annealTargetDataLayout
              (Miri.Memory.allocRange f.offset f.fieldLayout.size)
              false = .ok (.fromScalarInt msc))
      (padding_uninit :
        ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
          localAlloc.allocation.initializationMask.get
            (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) :
      StructMemPlaceRel mach ty layouts fields paths rootVal mp

namespace StructMemPlaceRel

/-- An **unpadded** `StructMemPlaceRel` (every byte of the aggregate lies in a
leaf field: `size ≤ structSumFieldBytes fields`) has its whole byte range
initialized and projects to the base `MemPlaceRel mach ty layouts (some rootVal) mp`
used by `LocalRel.indirect`. -/
theorem toMemPlaceRel {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (not_array : ∀ ek c, ty.kind ≠ RigidTy.array ek c)
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    (hunpad : (translateTy ty layouts).layout.size.bytes.toNat ≤ structSumFieldBytes fields) :
    MemPlaceRel mach ty layouts (some rootVal) mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, valid_layout, paths_len,
    ⟨⟨hd, tl, hrv⟩, _⟩, leafBytes_eq, ptr_prov, no_misalign, thin_meta, live_entry,
    base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, word_bits_init, fields_rel, padding_uninit⟩
  have hmask_lay : InitMaskWordRel localAlloc.allocation.initializationMask
      (translateTy ty layouts).layout.size words := by
    rw [← byteSize_eq]; exact mask_rel
  refine .mk allocId tag baseAddr Miri.ABI.Size.ZERO localAlloc
    ptr_prov no_misalign thin_meta live_entry.mem_toList base_lookup
    (by dsimp [Miri.ABI.Size.ZERO]; omega)
    (by rw [ptr_addr_eq]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero])
    mut_alloc aligned_ptr
    (by rw [byteSize_eq]; dsimp [Miri.ABI.Size.ZERO]; omega)
    ?_ ?_ ?_ ?_
  · intro hopt; cases hopt
  · intro v _ hnz
    have hpos : 0 < (translateTy ty layouts).layout.size.bytes.toNat := by
      cases hsz : (translateTy ty layouts).layout.size with
      | mk b =>
        cases hb : b.toNat with
        | zero =>
          have hb0 : b = 0 := UInt64.toNat_inj.mp (by simpa using hb)
          subst hb0
          exact absurd hsz hnz
        | succ n => omega
    apply initMaskWordRel_isRangeInitialized hmask_lay hpos
      (by dsimp [Miri.ABI.Size.ZERO]; omega)
    intro b _ hb_hi
    dsimp [Miri.ABI.Size.ZERO] at hb_hi
    rw [Nat.zero_add] at hb_hi
    obtain ⟨i, hi, hlo, hhi⟩ :=
      valid_layout.byte_mem_field_of_size_le_sumFieldBytes hunpad hb_hi
    exact word_bits_init i hi b hlo hhi
  · intro sc hopt
    rw [hrv] at hopt
    cases hopt
  · intro ek c elems hk hopt
    exact absurd hk (not_array ek c)

theorem of_stackAlloc_other {mach : AnnealMachine} {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp) :
    StructMemPlaceRel (stackAllocMachine mach mem' newId alloc) ty layouts fields paths rootVal mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, valid_layout, paths_len,
    rootVal_agg, leafBytes_eq, ptr_prov, no_misalign, thin_meta, live_entry,
    base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, word_bits_init, fields_rel, padding_uninit⟩
  obtain ⟨hlive_eq, _⟩ := reserveAllocId_ok_live hres
  obtain ⟨_, _, hbase_all⟩ := stackAllocMachine_live_base alloc hres
  have hmem := live_entry.mem_toList
  have hlive' : LiveAllocEntry (stackAllocMachine mach mem' newId alloc).memory.live
      allocId localAlloc := by
    dsimp [stackAllocMachine]
    rw [hlive_eq]
    exact live_entry.of_push_other _
  exact .mk allocId tag baseAddr localAlloc words valid_layout paths_len rootVal_agg leafBytes_eq
    ptr_prov no_misalign thin_meta hlive'
    ((hbase_all allocId localAlloc hmem).trans base_lookup)
    ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_rel word_bits_init fields_rel padding_uninit

theorem of_updateAlloc_ne {mach : AnnealMachine} {u : Nat}
    {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    StructMemPlaceRel (updateAllocMachine mach u updId kind alloc') ty layouts fields paths rootVal mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, valid_layout, paths_len,
    rootVal_agg, leafBytes_eq, ptr_prov, no_misalign, thin_meta, live_entry,
    base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, word_bits_init, fields_rel, padding_uninit⟩
  have hne_id : updId ≠ allocId := by
    intro heq; apply hne; rw [ptr_prov, heq]; rfl
  exact .mk allocId tag baseAddr localAlloc words valid_layout paths_len rootVal_agg leafBytes_eq
    ptr_prov no_misalign thin_meta (live_entry.of_set!_ne hu_lt hu_eq hne_id ⟨kind, alloc'⟩)
    base_lookup ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_rel word_bits_init fields_rel padding_uninit

theorem of_dealloc {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    (hdisj : ∀ mp0, v = .live (.indirect mp0) →
      mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    StructMemPlaceRel { mach with memory := deallocLocalMemory mach.memory v }
      ty layouts fields paths rootVal mp := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp0 =>
      have hd := hdisj mp0 rfl
      cases hid : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) = mach.memory := by
          simp [deallocLocalMemory, hid]
        rw [hmem]; exact h
      | some deadId =>
        rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, valid_layout, paths_len,
          rootVal_agg, leafBytes_eq, ptr_prov, no_misalign, thin_meta, live_entry,
          base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
          byteSize_eq, alloc_len_eq, prov_empty, mask_rel, word_bits_init, fields_rel, padding_uninit⟩
        have hne : allocId ≠ deadId := by
          intro heq; apply hd; rw [hid, ptr_prov, heq]; rfl
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            { mach.memory with live := mach.memory.live.filter (fun entry => entry.1 != deadId) } := by
          simp [deallocLocalMemory, hid]
        rw [hmem]
        exact .mk allocId tag baseAddr localAlloc words valid_layout paths_len rootVal_agg leafBytes_eq
          ptr_prov no_misalign thin_meta (live_entry.of_filter_ne hne)
          base_lookup ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
          prov_empty mask_rel word_bits_init fields_rel padding_uninit



theorem byteSize_eq {mach ty layouts fields paths rootVal mp}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64) (localAlloc : AnnealLocalAlloc),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      mach.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc) ∧
      localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, _, _, _, _, _, ptr_prov, _, _, live_entry, _, _, _, _, _, byteSize_eq, _⟩
  exact ⟨allocId, tag, baseAddr, localAlloc, ptr_prov, live_entry.left, byteSize_eq⟩

end StructMemPlaceRel


/-- Memory-place correspondence for an **uninitialized** indirect aggregate local
(`.uninit` in Anneal, `.indirect mp` backed by a freshly allocated uninitialized
`Miri.Memory.Allocation` in `lean-miri`). -/
inductive UninitStructMemPlaceRel
    (mach : AnnealMachine)
    (ty : Ty)
    (layouts : LayoutTable)
    (fields : List StructFieldDesc)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (valid_layout : ValidStructLayout (translateTy ty layouts).layout fields)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_entry : LiveAllocEntry mach.memory.live allocId localAlloc)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow :
        baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
      (mut_alloc : localAlloc.allocation.mutability = .Mut)
      (aligned_ptr :
        mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
      (byteSize_eq :
        localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
      (alloc_len_eq :
        localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
      (prov_empty :
        localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (mask_uninit :
        localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new (translateTy ty layouts).layout.size false) :
      UninitStructMemPlaceRel mach ty layouts fields mp

namespace UninitStructMemPlaceRel

theorem toMemPlaceRel {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitStructMemPlaceRel mach ty layouts fields mp) :
    MemPlaceRel mach ty layouts none mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, _, ptr_prov, no_misalign,
    thin_meta, live_entry, base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc,
    aligned_ptr, byteSize_eq, _, _, mask_uninit⟩
  refine .mk allocId tag baseAddr Miri.ABI.Size.ZERO localAlloc
    ptr_prov no_misalign thin_meta live_entry.mem_toList base_lookup
    (by dsimp [Miri.ABI.Size.ZERO]; omega)
    (by rw [ptr_addr_eq]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero])
    mut_alloc aligned_ptr
    (by rw [byteSize_eq]; dsimp [Miri.ABI.Size.ZERO]; omega)
    ?_ (fun _ hv => nomatch hv) (fun _ hsc => nomatch hsc) (fun _ _ _ _ hopt => nomatch hopt)
  intro _ _
  rw [mask_uninit]
  have hlt_u64 := (translateTy ty layouts).layout.size.bytes.toNat_lt
  have hend := lm22_allocRange_end (start := Miri.ABI.Size.ZERO)
    (sz := (translateTy ty layouts).layout.size)
    (by dsimp [Miri.ABI.Size.ZERO]; omega)
  have hfin : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes +
      (translateTy ty layouts).layout.size.bytes) =
      (translateTy ty layouts).layout.size := by
    dsimp [Miri.ABI.Size.ZERO]
    rw [UInt64.zero_add]
    cases (translateTy ty layouts).layout.size; rfl
  rw [hfin] at hend
  rw [Miri.Memory.InitMask.lazy_uninitialized_query _ _ _ hend (UInt64.le_refl _)]
  nofun

theorem of_stackAlloc_other {mach : AnnealMachine} {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : UninitStructMemPlaceRel mach ty layouts fields mp) :
    UninitStructMemPlaceRel (stackAllocMachine mach mem' newId alloc) ty layouts fields mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, valid_layout, ptr_prov, no_misalign,
    thin_meta, live_entry, base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc,
    aligned_ptr, byteSize_eq, alloc_len_eq, prov_empty, mask_uninit⟩
  obtain ⟨hlive_eq, _⟩ := reserveAllocId_ok_live hres
  obtain ⟨_, _, hbase_all⟩ := stackAllocMachine_live_base alloc hres
  have hmem := live_entry.mem_toList
  have hlive' : LiveAllocEntry (stackAllocMachine mach mem' newId alloc).memory.live
      allocId localAlloc := by
    dsimp [stackAllocMachine]
    rw [hlive_eq]
    exact live_entry.of_push_other _
  exact .mk allocId tag baseAddr localAlloc valid_layout ptr_prov no_misalign thin_meta
    hlive' ((hbase_all allocId localAlloc hmem).trans base_lookup)
    ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_uninit

theorem of_updateAlloc_ne {mach : AnnealMachine} {u : Nat}
    {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitStructMemPlaceRel mach ty layouts fields mp)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    UninitStructMemPlaceRel (updateAllocMachine mach u updId kind alloc') ty layouts fields mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, valid_layout, ptr_prov, no_misalign,
    thin_meta, live_entry, base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc,
    aligned_ptr, byteSize_eq, alloc_len_eq, prov_empty, mask_uninit⟩
  have hne_id : updId ≠ allocId := by
    intro heq; apply hne; rw [ptr_prov, heq]; rfl
  exact .mk allocId tag baseAddr localAlloc valid_layout ptr_prov no_misalign thin_meta
    (live_entry.of_set!_ne hu_lt hu_eq hne_id ⟨kind, alloc'⟩) base_lookup
    ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_uninit

theorem of_dealloc {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitStructMemPlaceRel mach ty layouts fields mp)
    (hdisj : ∀ mp0, v = .live (.indirect mp0) →
      mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    UninitStructMemPlaceRel { mach with memory := deallocLocalMemory mach.memory v }
      ty layouts fields mp := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp0 =>
      have hd := hdisj mp0 rfl
      cases hid : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) = mach.memory := by
          simp [deallocLocalMemory, hid]
        rw [hmem]; exact h
      | some deadId =>
        rcases h with ⟨allocId, tag, baseAddr, localAlloc, valid_layout, ptr_prov, no_misalign,
          thin_meta, live_entry, base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc,
          aligned_ptr, byteSize_eq, alloc_len_eq, prov_empty, mask_uninit⟩
        have hne : allocId ≠ deadId := by
          intro heq; apply hd; rw [hid, ptr_prov, heq]; rfl
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            { mach.memory with live := mach.memory.live.filter (fun entry => entry.1 != deadId) } := by
          simp [deallocLocalMemory, hid]
        rw [hmem]
        exact .mk allocId tag baseAddr localAlloc valid_layout ptr_prov no_misalign thin_meta
          (live_entry.of_filter_ne hne) base_lookup ptr_addr_eq addr_no_overflow mut_alloc
          aligned_ptr byteSize_eq alloc_len_eq prov_empty mask_uninit

end UninitStructMemPlaceRel

/-! ## 3. Static `StructTypeEnv`, `ImmediateStructRel`, and `StateRelLM2_2` -/

/-- Static environment mapping each product/tuple/struct `Ty` in `LM-2.2` to its
leaf descriptor list `fields : List StructFieldDesc` and matching leaf projection
paths `paths : List (List ProjectionElem)` (`none` for scalar/base types). -/
abbrev StructTypeEnv :=
  Ty → Option (List StructFieldDesc × List (List ProjectionElem))

/-- Empty `StructTypeEnv` under which `StateRelLM2_2` coincides with `StateRel`. -/
def emptyStructTypeEnv : StructTypeEnv := fun _ => none

/-- Optional chain of zero-offset `.field 0 _` wrapper projections from `midTy`
to primitive scalar `leafTy`: either `z = []` with `midTy = leafTy` (flat scalar
field), or `z` is a non-empty `ValidZeroScalarChain` through an `IsNonForgetLayout`
wrapper `midTy`. -/
def ValidOptZeroScalarChain (layouts : LayoutTable)
    (midTy : Ty) (z : List ProjectionElem) (leafTy : Ty) : Prop :=
  (z = [] ∧ midTy = leafTy) ∨
    (IsNonForgetLayout (translateTy midTy layouts).layout ∧
      ValidZeroScalarChain layouts (translateTy midTy layouts) z leafTy)

namespace ValidOptZeroScalarChain

theorem size_eq {layouts : LayoutTable} {midTy : Ty}
    {z : List ProjectionElem} {leafTy : Ty}
    (h : ValidOptZeroScalarChain layouts midTy z leafTy) :
    (translateTy leafTy layouts).layout.size = (translateTy midTy layouts).layout.size := by
  rcases h with ⟨_, rfl⟩ | ⟨_, hz⟩
  · rfl
  · exact hz.leaf_prim_and_size.2

theorem isNonForget {layouts : LayoutTable} {midTy : Ty}
    {z : List ProjectionElem} {leafTy : Ty}
    (hprim : IsPrimScalarTy leafTy)
    (h : ValidOptZeroScalarChain layouts midTy z leafTy) :
    IsNonForgetLayout (translateTy midTy layouts).layout := by
  rcases h with ⟨_, rfl⟩ | ⟨hnf, _⟩
  · exact hprim.isNonForget
  · exact hnf

theorem all_field_zero {layouts : LayoutTable} {midTy : Ty}
    {z : List ProjectionElem} {leafTy : Ty}
    (h : ValidOptZeroScalarChain layouts midTy z leafTy) :
    ∀ p ∈ z, ∃ fty, p = .field 0 fty := by
  rcases h with ⟨rfl, _⟩ | ⟨_, hz⟩
  · intro _ hm; cases hm
  · exact hz.all_field_zero

end ValidOptZeroScalarChain

/-- Immediate representation relation for `.Scalar` 1-field wrappers and
`.ScalarPair` 2-scalar tuples/structs, carrying `ValidStructLayout` and all leaf
scalar `sizeBytes` / `bool` / `char` invariants directly inside the state relation
so statement/projection typing predicates remain 100% syntactic. -/
inductive ImmediateStructRel
    (ty : Ty) (layouts : LayoutTable) :
    List StructFieldDesc → List (List ProjectionElem) →
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  /-- Single-scalar wrapper aggregate (`AbiRepr.Scalar`, `fields = [f₀]`, `paths = [p₀]`). -/
  | scalarWrapper (f₀ : StructFieldDesc) (p₀ : List ProjectionElem)
      (a : Miri.ABI.Scalar) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
      (v : Value) :
      ValidStructLayout (translateTy ty layouts).layout [f₀] →
      (translateTy ty layouts).layout.backendRepr = .Scalar a →
      p₀ ≠ [] →
      ValidZeroScalarChain layouts (translateTy ty layouts) p₀ f₀.ty →
      f₀.offset = Miri.ABI.Size.ZERO →
      f₀.fieldLayout = (translateTy f₀.ty layouts).layout →
      IsPrimScalarTy f₀.ty →
      ZeroScalarWrappedVal sc v p₀ →
      ScalarRel sc msc →
      f₀.fieldLayout.size = translateSizeBytes sc.sizeBytes →
      (f₀.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (f₀.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      ImmediateStructRel ty layouts [f₀] [p₀] v (.scalar (.fromScalarInt msc))
  /-- Two-scalar `ScalarPair` tuple/struct (`AbiRepr.ScalarPair`, `fields = [f₀, f₁]`,
  `paths = [.field 0 mid₀ :: z₀, .field 1 mid₁ :: z₁]`), covering both flat 2-field
  tuples/ADTs (`z₀ = [], z₁ = []`) and 2-field aggregates with wrapped scalar leaves. -/
  | scalarPair (f₀ f₁ : StructFieldDesc) (mid₀ mid₁ : Ty)
      (z₀ z₁ : List ProjectionElem)
      (a b : Miri.ABI.Scalar) (bOff : Miri.ABI.Size)
      (sc₀ sc₁ : MirAst.ScalarInt) (msc₀ msc₁ : Miri.Memory.ScalarInt)
      (v₀ v₁ : Value) :
      ValidStructLayout (translateTy ty layouts).layout [f₀, f₁] →
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 32 →
      ((∃ ts, ty.kind = .tuple ts) ∨ (∃ p adtArgs, ty.kind = .adt p adtArgs)) →
      (∀ t₁, ty.kind = .tuple [t₁, .bool] → f₁.ty.kind = .bool) →
      (translateTy ty layouts).layout.backendRepr =
        .ScalarPair (a := a) (b := b) (bOffset := bOff) →
      a.size annealRuntimeDataLayout = .ok f₀.fieldLayout.size →
      b.size annealRuntimeDataLayout = .ok f₁.fieldLayout.size →
      (translateTy ty layouts).layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO →
      (translateTy ty layouts).layout.fields.offset 1 = .ok bOff →
      f₀.offset = Miri.ABI.Size.ZERO →
      f₁.offset = bOff →
      f₀.fieldLayout = (translateTy f₀.ty layouts).layout →
      f₁.fieldLayout = (translateTy f₁.ty layouts).layout →
      IsRoundtripTy mid₀ →
      IsRoundtripTy mid₁ →
      IsPrimScalarTy f₀.ty →
      IsPrimScalarTy f₁.ty →
      ValidOptZeroScalarChain layouts mid₀ z₀ f₀.ty →
      ValidOptZeroScalarChain layouts mid₁ z₁ f₁.ty →
      ZeroScalarWrappedVal sc₀ v₀ z₀ →
      ZeroScalarWrappedVal sc₁ v₁ z₁ →
      ScalarRel sc₀ msc₀ →
      ScalarRel sc₁ msc₁ →
      f₀.fieldLayout.size = translateSizeBytes sc₀.sizeBytes →
      f₁.fieldLayout.size = translateSizeBytes sc₁.sizeBytes →
      (f₀.ty.kind = .bool → sc₀.sizeBytes = 1 ∧ (sc₀.bits = 0 ∨ sc₀.bits = 1)) →
      (f₀.ty.kind = .char → sc₀.sizeBytes = 4 ∧ isValidCharCode sc₀.bits = true) →
      (f₁.ty.kind = .bool → sc₁.sizeBytes = 1 ∧ (sc₁.bits = 0 ∨ sc₁.bits = 1)) →
      (f₁.ty.kind = .char → sc₁.sizeBytes = 4 ∧ isValidCharCode sc₁.bits = true) →
      ImmediateStructRel ty layouts [f₀, f₁]
        [.field 0 mid₀ :: z₀, .field 1 mid₁ :: z₁]
        (.aggregate 0 [v₀, v₁])
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))

namespace ImmediateStructRel

theorem size_lt_4gib {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : ImmediateStructRel ty layouts fields paths v imm) :
    (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 32 := by
  cases h with
  | scalarWrapper f₀ p₀ _ sc msc _ _ _ _ hchain _ hfl₀ _ _ hrel hsz₀ _ _ =>
    have hsz := hchain.leaf_prim_and_size.2
    rw [← hsz, ← hfl₀, hsz₀]
    rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; decide)
  | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsz4g
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact hsz4g

theorem toImmediateRel_of_flat {ty : Ty} {layouts : LayoutTable}
    {f₀ f₁ : StructFieldDesc} {mid₀ mid₁ : Ty}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : ImmediateStructRel ty layouts [f₀, f₁]
      [[.field 0 mid₀], [.field 1 mid₁]] v imm) :
    ImmediateRel ty layouts v imm := by
  cases h with
  | scalarPair _ _ _ _ _ _ _ _ _ sc₀ sc₁ msc₀ msc₁ v₀ v₁
      _ _ hagg htup_bool _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw₀ hw₁ hrel₀ hrel₁ _ _ _ _ hbool₁ _ =>
    rw [hw₀.nil_inv, hw₁.nil_inv]
    exact .scalarPair sc₀ sc₁ msc₀ msc₁ hrel₀ hrel₁ hagg (fun t₁ ht => hbool₁ (htup_bool t₁ ht))

end ImmediateStructRel

/-- Monotone `AllocId` watermark guaranteeing at least `budget` deterministic
stack allocations without ID exhaustion, duplicate-ID collision, or 64-bit
base-address overflow (`annealStackBaseAddr id + size < 2 ^ 64`). -/
structure AllocIdWatermark (budget : Nat) (mem : AnnealMemory) : Prop where
  next_pos : 0 < mem.nextAllocId.toNat
  next_budget : mem.nextAllocId.toNat + budget < 2 ^ 32
  not_exhausted : mem.idSupplyExhausted = false
  no_source_world : mem.sourceAllocIdWorldActive = false
  issued_lt :
    ∀ id : Miri.Memory.AllocId,
      mem.hasIssuedId id = true → id.value.toNat < mem.nextAllocId.toNat
  live_lt :
    ∀ e ∈ mem.live.toList, e.1.value.toNat < mem.nextAllocId.toNat
  dead_lt :
    ∀ d ∈ mem.dead.toList, d.allocId.value.toNat < mem.nextAllocId.toNat
  global_lt :
    ∀ id : Miri.Memory.AllocId,
      mem.hasGlobalId id = true → id.value.toNat < mem.nextAllocId.toNat

/-- `AllocId` supply invariant parameterized by remaining allocation budget `k`:
`k = 0` holds unconditionally (so `StateRel` embeds into `StateRelLM2_2 ... 0`
with zero extra hypotheses), while `k + 1` carries `AllocIdWatermark (k + 1) mem`
so each `forceAllocation` step transitions `k + 1 → k` across multi-statement
compositions. -/
def AllocIdSupplyValid (budget : Nat) (mem : AnnealMemory) : Prop :=
  budget = 0 ∨ AllocIdWatermark budget mem

namespace AllocIdWatermark

theorem empty (budget : Nat) (h : 1 + budget < 2 ^ 32) :
    AllocIdWatermark budget Miri.Memory.MemoryState.empty := by
  refine ⟨by decide, h, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro id hid
    with_unfolding_all
      simp [Miri.Memory.MemoryState.empty, Miri.Memory.MemoryState.hasIssuedId,
        Miri.Memory.KeyedArray.empty, Miri.Memory.KeyedArray.contains] at hid
  · intro e he; simp [Miri.Memory.MemoryState.empty] at he
  · intro d hd; simp [Miri.Memory.MemoryState.empty] at hd
  · intro id hid
    with_unfolding_all
      simp [Miri.Memory.MemoryState.empty, Miri.Memory.MemoryState.hasGlobalId,
        Miri.Memory.KeyedArray.empty, Miri.Memory.KeyedArray.contains] at hid

theorem mono {b₁ b₂ : Nat} {mem : AnnealMemory}
    (hle : b₁ ≤ b₂) (h : AllocIdWatermark b₂ mem) :
    AllocIdWatermark b₁ mem :=
  { h with next_budget := by have := h.next_budget; omega }

theorem reserve_step {k : Nat} {mem : AnnealMemory}
    (h : AllocIdWatermark (k + 1) mem) :
    ∃ (mem' : AnnealMemory) (id : Miri.Memory.AllocId),
      mem.reserveAllocId = (mem', .ok id) ∧
      id.value = mem.nextAllocId ∧
      mem'.live = mem.live ∧
      mem.live.any (fun entry => entry.1 == id) = false ∧
      (∀ alloc, AllocIdWatermark k
        { mem' with live := mem'.live.push (id, ⟨.stack, alloc⟩) }) ∧
      (∀ sz : Nat, sz < 2 ^ 32 →
        (annealStackBaseAddr id).toNat + sz < 2 ^ 64) := by
  have hpos := h.next_pos
  have hbnd := h.next_budget
  have hnz : mem.nextAllocId ≠ 0 := by
    intro hz; rw [hz] at hpos; simp at hpos
  let id : Miri.Memory.AllocId := ⟨mem.nextAllocId, hnz⟩
  have hof : Miri.Memory.AllocId.ofUInt64 mem.nextAllocId = some id := by
    simp [Miri.Memory.AllocId.ofUInt64, hnz, id]
  have hissued_f : mem.hasIssuedId id = false := by
    cases hb : mem.hasIssuedId id
    · rfl
    · exact absurd (h.issued_lt id hb) (Nat.lt_irrefl _)
  have hlive_f : mem.live.any (fun entry => entry.1 == id) = false := by
    rw [Array.any_eq_false]
    intro i hi htrue
    have hmem : mem.live[i] ∈ mem.live.toList := Array.getElem_mem_toList hi
    have hlt := h.live_lt _ hmem
    have heq : (mem.live[i]).1 = id := beq_iff_eq.mp htrue
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hdead_f : mem.dead.any (fun entry => entry.allocId == id) = false := by
    rw [Array.any_eq_false]
    intro i hi htrue
    have hmem : mem.dead[i] ∈ mem.dead.toList := Array.getElem_mem_toList hi
    have hlt := h.dead_lt _ hmem
    have heq : (mem.dead[i]).allocId = id := beq_iff_eq.mp htrue
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hglob_f : mem.hasGlobalId id = false := by
    cases hb : mem.hasGlobalId id
    · rfl
    · exact absurd (h.global_lt id hb) (Nat.lt_irrefl _)
  have hcont_f :
      (mem.hasIssuedId id || mem.live.any (fun entry => entry.1 == id) ||
        mem.dead.any (fun entry => entry.allocId == id) || mem.hasGlobalId id) = false := by
    rw [hissued_f, hlive_f, hdead_f, hglob_f]; rfl
  have hnext_nat : (mem.nextAllocId + 1).toNat = mem.nextAllocId.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
    change mem.nextAllocId.toNat + 1 < 2 ^ 64
    omega
  have hissued_push : ∀ {t : Miri.Memory.KeyedArray UInt64 Miri.Memory.AllocId
        (fun (x : Miri.Memory.AllocId) => x.value)} (q : Miri.Memory.AllocId),
      (t.push id).contains q.value = true →
      t.contains q.value = true ∨ q.value = id.value := by
    intro t q hq
    rw [Miri.Memory.KeyedArray.contains_rows] at hq
    have hpush_arr : (t.push id).toArray = t.toArray.push id := rfl
    rw [hpush_arr, Array.map_push] at hq
    rcases Array.mem_push.mp (Array.contains_iff_mem.mp hq) with hmem_old | heq
    · left
      rw [Miri.Memory.KeyedArray.contains_rows]
      exact Array.contains_iff_mem.mpr hmem_old
    · right
      exact heq
  cases hres : mem.reserveAllocId with
  | mk mem' out =>
    have hstep : mem.reserveAllocId = (mem', out) := hres
    unfold Miri.Memory.MemoryState.reserveAllocId at hstep
    simp only [Id.run, h.not_exhausted, h.no_source_world, Bool.false_and,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte, hof] at hstep
    split at hstep
    · rename_i htrue
      have hc : (mem.hasIssuedId id || mem.live.any (fun entry => entry.1 == id) ||
          mem.dead.any (fun entry => entry.allocId == id) || mem.hasGlobalId id) = true := htrue
      rw [hcont_f] at hc
      cases hc
    · injection hstep with hmem_eq hout_eq
      subst hout_eq
      refine ⟨mem', id, rfl, rfl, by rw [← hmem_eq], hlive_f, ?_, ?_⟩
      · intro alloc
        rw [← hmem_eq]
        refine ⟨by dsimp; rw [hnext_nat]; omega, by dsimp; rw [hnext_nat]; omega,
          by dsimp, by dsimp, ?_, ?_, ?_, ?_⟩
        · intro q hq
          dsimp at hq ⊢
          rw [hnext_nat]
          unfold Miri.Memory.MemoryState.hasIssuedId at hq
          rcases hissued_push q hq with h1 | h2
          · have h1' : mem.hasIssuedId q = true := h1
            have := h.issued_lt q h1'; omega
          · rw [h2]; dsimp [id]; omega
        · intro e he
          dsimp at he ⊢
          rw [hnext_nat]
          rw [Array.toList_push, List.mem_append] at he
          rcases he with he_old | he_new
          · have := h.live_lt e he_old; omega
          · simp only [List.mem_singleton] at he_new
            subst he_new; dsimp [id]; omega
        · intro d hd
          dsimp at hd ⊢
          rw [hnext_nat]; have := h.dead_lt d hd; omega
        · intro q hq
          dsimp at hq ⊢
          rw [hnext_nat]; have := h.global_lt q hq; omega
      · intro sz hsz
        have hid_lt : id.value.toNat < 2 ^ 32 := by dsimp [id]; omega
        have hbase_eq : (annealStackBaseAddr id).toNat = id.value.toNat * 2 ^ 32 := by
          unfold annealStackBaseAddr
          rw [UInt64.toNat_shiftLeft]
          have h32 : (32 : UInt64).toNat % 64 = 32 := by decide
          rw [h32, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
          change id.value.toNat * 2 ^ 32 < 2 ^ 64
          omega
        rw [hbase_eq]
        have hle : id.value.toNat ≤ 2 ^ 32 - 1 := by omega
        calc id.value.toNat * 2 ^ 32 + sz
          _ < (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 32 := by
              exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 32) hle) hsz
          _ = 2 ^ 64 := by decide

theorem of_updateAlloc {b : Nat} {mem : AnnealMemory}
    {u : Nat} {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hu_lt : u < mem.live.size)
    (hu_eq : mem.live[u]'hu_lt = (updId, oldLa))
    (h : AllocIdWatermark b mem) :
    AllocIdWatermark b { mem with live := mem.live.set! u (updId, ⟨kind, alloc'⟩) } := by
  refine { h with live_lt := ?_ }
  intro e he
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at he
  rcases List.mem_or_eq_of_mem_set he with he_old | rfl
  · exact h.live_lt e he_old
  · have hmem : (updId, oldLa) ∈ mem.live.toList := by
      rw [← hu_eq]; exact Array.getElem_mem_toList hu_lt
    exact h.live_lt (updId, oldLa) hmem

theorem of_dealloc {b : Nat} {mem : AnnealMemory}
    (v : Miri.Interpreter.LocalValue AnnealProv)
    (h : AllocIdWatermark b mem) :
    AllocIdWatermark b (deallocLocalMemory mem v) := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp =>
      dsimp [deallocLocalMemory]
      cases mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => exact h
      | some deadId =>
        refine { h with live_lt := ?_ }
        intro e he
        rw [Array.toList_filter, List.mem_filter] at he
        exact h.live_lt e he.1

end AllocIdWatermark

namespace AllocIdSupplyValid

theorem mono {b₁ b₂ : Nat} {mem : AnnealMemory}
    (hle : b₁ ≤ b₂) (h : AllocIdSupplyValid b₂ mem) :
    AllocIdSupplyValid b₁ mem := by
  rcases h with rfl | hw
  · exact Or.inl (Nat.eq_zero_of_le_zero hle)
  · exact Or.inr (hw.mono hle)

theorem of_succ {k : Nat} {mem : AnnealMemory}
    (h : AllocIdSupplyValid (k + 1) mem) :
    AllocIdWatermark (k + 1) mem := by
  rcases h with h0 | hw
  · cases h0
  · exact hw

theorem of_updateAlloc {b : Nat} {mem : AnnealMemory}
    {u : Nat} {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hu_lt : u < mem.live.size)
    (hu_eq : mem.live[u]'hu_lt = (updId, oldLa))
    (h : AllocIdSupplyValid b mem) :
    AllocIdSupplyValid b { mem with live := mem.live.set! u (updId, ⟨kind, alloc'⟩) } := by
  rcases h with rfl | hw
  · exact Or.inl rfl
  · exact Or.inr (hw.of_updateAlloc hu_lt hu_eq)

theorem of_dealloc {b : Nat} {mem : AnnealMemory}
    (v : Miri.Interpreter.LocalValue AnnealProv)
    (h : AllocIdSupplyValid b mem) :
    AllocIdSupplyValid b (deallocLocalMemory mem v) := by
  rcases h with rfl | hw
  · exact Or.inl rfl
  · exact Or.inr (hw.of_dealloc v)

end AllocIdSupplyValid

/-- Local storage correspondence for `LM-2.2`, parameterized by static
`StructTypeEnv`:
* When `env decl.ty = none`, delegates directly to `LocalRel mach decl layouts slot mls`.
* When `env decl.ty = some (fields, paths)`, tracks dead, uninitialized
  (`.immediate .uninit` or `.indirect mp` via `UninitStructMemPlaceRel`),
  immediate (`.Scalar` wrapper or `.ScalarPair` via `ImmediateStructRel`), and
  memory-backed (`StructMemPlaceRel`, covering `.Memory` structs as well as
  address-taken / forced-to-memory `.Scalar` and `.ScalarPair` structs across
  both unpadded and padded layouts). -/
inductive LocalRelLM2_2
    (env : StructTypeEnv)
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  | base (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      env decl.ty = none →
      LocalRel mach decl layouts slot mls →
      LocalRelLM2_2 env mach decl layouts slot mls
  | structDead (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (fields, paths) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      LocalRelLM2_2 env mach decl layouts .dead ⟨.dead, cachedLayout⟩
  | structUninitImm (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (fields, paths) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      LocalRelLM2_2 env mach decl layouts .uninit ⟨.live (.immediate .uninit), cachedLayout⟩
  | structUninitInd (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (fields, paths) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      UninitStructMemPlaceRel mach decl.ty layouts fields mp →
      LocalRelLM2_2 env mach decl layouts .uninit ⟨.live (.indirect mp), cachedLayout⟩
  | structImm (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (v : Value) (imm : Miri.Interpreter.Immediate AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (fields, paths) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      ImmediateStructRel decl.ty layouts fields paths v imm →
      LocalRelLM2_2 env mach decl layouts (.init v) ⟨.live (.immediate imm), cachedLayout⟩
  | structInd (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (v : Value) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (fields, paths) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      StructMemPlaceRel mach decl.ty layouts fields paths v mp →
      LocalRelLM2_2 env mach decl layouts (.init v) ⟨.live (.indirect mp), cachedLayout⟩

namespace LocalRelLM2_2

theorem cachedLayout_eq {env : StructTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts := by
  cases h with
  | base _ _ _ hb => exact hb.cachedLayout_eq
  | structDead _ _ _ _ hc => exact hc
  | structUninitImm _ _ _ _ hc => exact hc
  | structUninitInd _ _ _ _ _ hc _ => exact hc
  | structImm _ _ _ _ _ _ hc _ => exact hc
  | structInd _ _ _ _ _ _ hc _ => exact hc

theorem layout_eq {env : StructTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts :=
  fun l hl => h.cachedLayout_eq l (Option.mem_def.mpr hl)

theorem cache_layout {env : StructTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls) :
    LocalRelLM2_2 env mach decl layouts slot
      { mls with layout := some (translateTy decl.ty layouts) } := by
  have hc : ∀ l ∈ (some (translateTy decl.ty layouts)),
      l = translateTy decl.ty layouts :=
    fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm
  cases h with
  | base _ _ henv hb =>
    refine .base _ _ henv ?_
    cases hb with
    | dead _ _ => exact .dead _ hc
    | immediate _ i _ _ hv => exact .immediate slot i _ hc hv
    | indirect _ mp _ _ hne hmp => exact .indirect slot mp _ hc hne hmp
  | structDead f p _ henv _ => exact .structDead f p _ henv hc
  | structUninitImm f p _ henv _ => exact .structUninitImm f p _ henv hc
  | structUninitInd f p mp _ henv _ hmp => exact .structUninitInd f p mp _ henv hc hmp
  | structImm f p v imm _ henv _ himm => exact .structImm f p v imm _ henv hc himm
  | structInd f p v mp _ henv _ hmp => exact .structInd f p v mp _ henv hc hmp

theorem allocLive {env : StructTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | base _ _ _ hb => exact hb.allocLive
  | structDead _ _ _ _ _ => intro mp hv; cases hv
  | structUninitImm _ _ _ _ _ => intro mp hv; cases hv
  | structUninitInd _ _ mp _ _ _ hmp =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    rcases hmp with ⟨allocId, _, _, _, _, hprov, _, _, hlive, _, _, _, _, _, _, _, _, _⟩
    exact ⟨allocId, by rw [hprov]; rfl, hlive.any_true⟩
  | structImm _ _ _ _ _ _ _ _ => intro mp hv; cases hv
  | structInd _ _ _ mp _ _ _ hmp =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    rcases hmp with ⟨allocId, _, _, _, _, _, _, _, _, hprov, _, _, hlive, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact ⟨allocId, by rw [hprov]; rfl, hlive.any_true⟩

theorem of_stackAlloc_other {env : StructTypeEnv} {mach : AnnealMachine}
    {mem' : AnnealMemory} {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : LocalRelLM2_2 env mach decl layouts slot mls) :
    LocalRelLM2_2 env (stackAllocMachine mach mem' newId alloc) decl layouts slot mls := by
  obtain ⟨hlive, _, hbase⟩ := stackAllocMachine_live_base alloc hres
  cases h with
  | base _ _ henv hb => exact .base slot mls henv (hb.of_live_base hlive hbase)
  | structDead f p c henv hc => exact .structDead f p c henv hc
  | structUninitImm f p c henv hc => exact .structUninitImm f p c henv hc
  | structUninitInd f p mp c henv hc hmp =>
    exact .structUninitInd f p mp c henv hc (hmp.of_stackAlloc_other hres)
  | structImm f p v imm c henv hc himm => exact .structImm f p v imm c henv hc himm
  | structInd f p v mp c henv hc hmp =>
    exact .structInd f p v mp c henv hc (hmp.of_stackAlloc_other hres)

theorem of_updateAlloc_ne {env : StructTypeEnv} {mach : AnnealMachine}
    {u : Nat} {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ mp', mls.value = .live (.indirect mp') →
      mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    LocalRelLM2_2 env (updateAllocMachine mach u updId kind alloc') decl layouts slot mls := by
  cases h with
  | base _ _ henv hb =>
    refine .base slot mls henv ?_
    cases hb with
    | dead c hc => exact .dead c hc
    | immediate _ i c hc hv => exact .immediate slot i c hc hv
    | indirect _ mp c hc hne hmp =>
      refine .indirect slot mp c hc hne ?_
      cases hmp with
      | mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem hbase hovf hptr
          hmut halign hbnd huninit hval hsc harr =>
        have hne_id : updId ≠ allocId := by
          intro heq
          apply hdisj mp rfl
          rw [hprov, heq]; rfl
        have hmem' : (allocId, la) ∈
            (updateAllocMachine mach u updId kind alloc').memory.live.toList := by
          dsimp [updateAllocMachine]
          rw [Array.toList_setIfInBounds]
          obtain ⟨j, hj, hget_j⟩ := List.mem_iff_getElem.mp hmem
          have hju : j ≠ u := by
            intro rfl
            simp only [Array.getElem_toList] at hget_j
            rw [hu_eq] at hget_j
            injection hget_j with hid_eq
            exact hne_id hid_eq
          have hj_set : j < (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩)).length := by
            rw [List.length_set]; exact hj
          have hget_set : (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩))[j]'hj_set =
              (allocId, la) := by
            rw [List.getElem_set_ne (Ne.symm hju)]; exact hget_j
          rw [← hget_set]
          exact List.getElem_mem hj_set
        exact .mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem' hbase hovf hptr hmut halign hbnd huninit hval hsc harr
  | structDead f p c henv hc => exact .structDead f p c henv hc
  | structUninitImm f p c henv hc => exact .structUninitImm f p c henv hc
  | structUninitInd f p mp c henv hc hmp =>
    exact .structUninitInd f p mp c henv hc (hmp.of_updateAlloc_ne hu_lt hu_eq (hdisj mp rfl))
  | structImm f p v imm c henv hc himm => exact .structImm f p v imm c henv hc himm
  | structInd f p v mp c henv hc hmp =>
    exact .structInd f p v mp c henv hc (hmp.of_updateAlloc_ne hu_lt hu_eq (hdisj mp rfl))

theorem of_dealloc {env : StructTypeEnv} {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_2 env mach decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRelLM2_2 env { mach with memory := deallocLocalMemory mach.memory v }
      decl layouts slot mls := by
  cases h with
  | base _ _ henv hb => exact .base slot mls henv (hb.of_dealloc hdisj)
  | structDead f p c henv hc => exact .structDead f p c henv hc
  | structUninitImm f p c henv hc => exact .structUninitImm f p c henv hc
  | structUninitInd f p mp c henv hc hmp =>
    exact .structUninitInd f p mp c henv hc (hmp.of_dealloc fun mp0 hv => hdisj mp0 mp hv rfl)
  | structImm f p val imm c henv hc himm => exact .structImm f p val imm c henv hc himm
  | structInd f p val mp c henv hc hmp =>
    exact .structInd f p val mp c henv hc (hmp.of_dealloc fun mp0 hv => hdisj mp0 mp hv rfl)

end LocalRelLM2_2

/-- Stack-frame correspondence under `StructTypeEnv`. -/
structure FrameRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      LocalRelLM2_2 env mach decl body.layouts slot mls

namespace FrameRelLM2_2

theorem lookup_local {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2 body env mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (hlt_mf : idx < mf.locals.size),
      idx < af.locals.length ∧
      get? af.locals idx = some slot ∧
      mf.locals[idx]? = some mls ∧
      mf.locals[idx]'hlt_mf = mls ∧
      LocalRelLM2_2 env mach decl body.layouts slot mls := by
  have hlt_decl : idx < body.localDecls.length := by
    dsimp [get?] at hdecl
    exact (List.getElem?_eq_some_iff.mp hdecl).1
  have hlt_af : idx < af.locals.length := by rw [h.af_locals_len]; exact hlt_decl
  have hlt_mf : idx < mf.locals.size := by rw [h.mf_locals_size]; exact hlt_decl
  have hslot : get? af.locals idx = some (af.locals[idx]'hlt_af) :=
    List.getElem?_eq_getElem hlt_af
  have hmls : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  exact ⟨af.locals[idx]'hlt_af, mf.locals[idx]'hlt_mf, hlt_mf, hlt_af,
    hslot, hmls, rfl, h.locals_rel idx decl _ _ hdecl hslot hmls⟩

theorem cache_local_layout {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2 body env mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM2_2 body env mach af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, by simp [cacheFrameLocalLayout, h.mf_locals_size], ?_⟩
  intro i d sl ml hd hs hm
  by_cases hi : i = idx
  · subst hi
    rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
    have hm_set : (cacheFrameLocalLayout mf i hlt (translateTy decl.ty body.layouts)).locals[i]? =
        some { mf.locals[i]'hlt with layout := some (translateTy decl.ty body.layouts) } := by
      simp [cacheFrameLocalLayout]
    rw [hm_set] at hm; injection hm with hml; subst hml
    have hmls0 : mf.locals[i]? = some (mf.locals[i]'hlt) := Array.getElem?_eq_getElem hlt
    exact (h.locals_rel i decl sl _ hdecl hs hmls0).cache_layout
  · have hm_ne : (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)).locals[i]? =
        mf.locals[i]? := by
      simp [cacheFrameLocalLayout, Array.getElem?_set_ne _ (Ne.symm hi)]
    rw [hm_ne] at hm
    exact h.locals_rel i d sl ml hd hs hm

theorem update_local {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2 body env mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot)
    (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRelLM2_2 env mach decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_2 body env mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } := by
  refine ⟨h.body_eq, h.location_eq, by simp [h.af_locals_len], by simp [h.mf_locals_size], ?_⟩
  intro i d sl ml hd hs hm
  by_cases hi : i = idx
  · subst hi
    rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
    have hlt_af : i < af.locals.length := by
      rw [h.af_locals_len]; rw [← h.mf_locals_size]; exact hlt_mf
    dsimp [get?] at hs
    rw [List.getElem?_set_self hlt_af] at hs
    injection hs with hsl; subst hsl
    rw [Array.getElem?_set_self hlt_mf] at hm
    injection hm with hml; subst hml
    exact hnew
  · dsimp [get?] at hs
    rw [List.getElem?_set_ne (Ne.symm hi)] at hs
    rw [Array.getElem?_set_ne _ (Ne.symm hi)] at hm
    exact h.locals_rel i d sl ml hd hs hm

theorem step_pc {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2 body env mach af mf) :
    FrameRelLM2_2 body env mach
      { af with stmtIdx := af.stmtIdx + 1 }
      { mf with location := .mir ⟨af.blockIdx, af.stmtIdx + 1⟩ } :=
  ⟨h.body_eq, rfl, h.af_locals_len, h.mf_locals_size, h.locals_rel⟩

end FrameRelLM2_2

/-- Static (state-independent) abstract local tracking for `LM-2.2` statement
chains:
* `initLocals`: locals statically known not to be `.uninit` (either `.dead`,
  which deterministically triggers UB on both sides, or `.init _`, which holds a
  valid aggregate/scalar value), used for projected field writes `_dst.f = op`.
* `immLocals`: locals statically known not to be `.live (.indirect _)` (either
  `.dead` or `.live (.immediate _)`), used for unprojected `Use` assignments
  `_dst = Use(op)` so `WellTypedLM2_2Stmt` never quantifies over `m` or `s`. -/
structure LM2_2StaticEnv where
  initLocals : List Local := []
  immLocals : List Local := []
  deriving DecidableEq, Repr

/-- Whole-machine simulation relation for `LM-2.2`, parameterized by:
* `env : StructTypeEnv` (static struct/tuple layout environment),
* `stEnv : LM2_2StaticEnv` (static `initLocals` and `immLocals` sets so
  `WellTypedLM2_2Stmt` remains 100% syntactic without inspecting `s` or `m`),
* `allocBudget : Nat` (remaining `AllocIdSupplyValid` allocation budget). -/
inductive StateRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (allocBudget : Nat)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM2_2 body env m.machine s.frame topFrame)
      (initLocals_valid :
        ∀ idx ∈ stEnv.initLocals, get? s.frame.locals idx ≠ some .uninit)
      (immLocals_valid :
        ∀ idx ∈ stEnv.immLocals, ∀ mp lay,
          topFrame.locals[idx]? ≠ some ⟨.live (.indirect mp), lay⟩)
      (allocSupply_valid : AllocIdSupplyValid allocBudget m.machine.memory)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_2 body env stEnv allocBudget s m

/-- Outcome correspondence for one `LM-2.2` step (`MirStepNode` ↔ `StepResult`),
advancing static `stEnv'` and `allocBudget'`. -/
inductive StepRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv' : LM2_2StaticEnv)
    (allocBudget' : Nat)
    (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_2 body env stEnv' allocBudget' s' m' →
      StepRelLM2_2 body env stEnv' allocBudget' m (.step s') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_2 body env stEnv' allocBudget' m (.fail .ub)
        (m', .error (.undefinedBehavior msg))

namespace StepRelLM2_2

theorem step_iff {body : CapturedMir} {env : StructTypeEnv}
    {stEnv' : LM2_2StaticEnv} {allocBudget' : Nat} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_2 body env stEnv' allocBudget' m aRes mRes) :
    (∃ s', aRes = .step s' ∧
        StateRelLM2_2 body env stEnv' allocBudget' s' mRes.1) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[]) := by
  cases h with
  | step s' m' hrel =>
    rcases hrel with ⟨tf, hf, hrc, hrp, hfr, hinit, himm, halloc, hcal, hst, hbor, hprot, hcaller, hdisj⟩
    constructor
    · intro _
      refine ⟨rfl, ?_⟩
      rw [hf]; intro hemp; have := congrArg Array.size hemp; contradiction
    · intro _
      exact ⟨s', rfl, .mk tf hf hrc hrp hfr hinit himm halloc hcal hst hbor hprot hcaller hdisj⟩
  | ub _ _ =>
    constructor
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

theorem ub_iff {body : CapturedMir} {env : StructTypeEnv}
    {stEnv' : LM2_2StaticEnv} {allocBudget' : Nat} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_2 body env stEnv' allocBudget' m aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) := by
  cases h with
  | step _ _ _ =>
    exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ub _ msg =>
    exact ⟨fun _ => ⟨msg, rfl⟩, fun _ => rfl⟩

end StepRelLM2_2

/-- Every base `StateRel body s m` embeds unconditionally into
`StateRelLM2_2 body emptyStructTypeEnv {} 0 s m`. -/
theorem StateRel.toLM2_2 {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) :
    StateRelLM2_2 body emptyStructTypeEnv {} 0 s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  refine .mk tf hf hrc hrp
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => .base sl ml rfl (hfr.locals_rel i d sl ml hd hs hm)⟩
    (fun _ hmem => by cases hmem)
    (fun _ hmem => by cases hmem)
    (Or.inl rfl)
    hcal hst hbor hprot hcaller hdisj

/-- Every `StateRelLM2_2` projects back to base `StateRel body s m` when
* every initialized immediate struct local is a flat 2-scalar tuple/ADT that the
  base `ImmediateRel` accepts (`hflat`), and
* every initialized memory-backed struct local is **unpadded** (`hunpad`), so its
  whole byte range is initialized as base `LocalRel.indirect` requires
  (`StructMemPlaceRel.toMemPlaceRel`).
A live memory-backed struct with uninitialized padding has no base counterpart:
the shared `Relation.lean` is not modified by `LM-2.2`, so such states are
related only by `StateRelLM2_2`. -/
theorem StateRelLM2_2.toStateRel_of_flat_imm
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_2 body env stEnv allocBudget s m)
    (henv_valid : ∀ ty fs ps, env ty = some (fs, ps) → ∀ ek c, ty.kind ≠ RigidTy.array ek c)
    (hflat : ∀ (i : Nat) (decl : LocalDecl) (v : Value)
      (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      env decl.ty ≠ none →
      get? s.frame.locals i = some (.init v) →
      (∃ tf, m.stack.frames = #[tf] ∧ tf.locals[i]? = some ⟨.live (.immediate imm), lay⟩) →
      ImmediateRel decl.ty body.layouts v imm)
    (hunpad : ∀ (i : Nat) (decl : LocalDecl) (v : Value)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout)
      (fields : List StructFieldDesc) (paths : List (List ProjectionElem)),
      get? body.localDecls i = some decl →
      env decl.ty = some (fields, paths) →
      get? s.frame.locals i = some (.init v) →
      (∃ tf, m.stack.frames = #[tf] ∧ tf.locals[i]? = some ⟨.live (.indirect mp), lay⟩) →
      (translateTy decl.ty body.layouts).layout.size.bytes.toNat ≤ structSumFieldBytes fields) :
    StateRel body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, _, _, _, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  refine .mk tf hf hrc hrp
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size, ?_⟩
    hcal hst hbor hprot hcaller hdisj
  intro i decl slot mls hdecl hslot hmls
  cases hfr.locals_rel i decl slot mls hdecl hslot hmls with
  | base _ _ _ hb => exact hb
  | structDead _ _ c _ hc => exact .dead c hc
  | structUninitImm _ _ c _ hc => exact .immediate .uninit .uninit c hc (Or.inl ⟨rfl, rfl⟩)
  | structUninitInd _ _ mp c _ hc hmp =>
    exact .indirect .uninit mp c hc (by nofun) hmp.toMemPlaceRel
  | structImm f p v imm c henv hc _ =>
    exact .immediate (.init v) imm c hc
      (Or.inr ⟨v, rfl, hflat i decl v imm c hdecl (by rw [henv]; nofun) hslot ⟨tf, hf, hmls⟩⟩)
  | structInd fs ps v mp c henv hc hmp =>
    exact .indirect (.init v) mp c hc (by nofun)
      (hmp.toMemPlaceRel (henv_valid _ _ _ henv) (hunpad i decl v mp c fs ps hdecl henv hslot ⟨tf, hf, hmls⟩))


/-! ## 4. State-Independent Projected Read Simulation (`WellTypedLM2_2ProjectedRead`) -/

theorem MemoryAllocDisjoint_cacheFrameLocalLayout
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MemoryAllocDisjoint topFrame)
    {idx : Nat} (hlt : idx < topFrame.locals.size)
    (lay : Miri.Interpreter.LocalLayout) :
    MemoryAllocDisjoint (cacheFrameLocalLayout topFrame idx hlt lay) := by
  apply MemoryAllocDisjoint.mono_layout hdisj
  intro k
  by_cases hk : k = idx
  · subst hk
    refine ⟨some lay, ?_⟩
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt, Array.getElem?_eq_getElem hlt]
    rfl
  · refine ⟨(topFrame.locals[k]?).bind (fun x => x.layout), ?_⟩
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ (Ne.symm hk)]
    cases topFrame.locals[k]? <;> rfl

/-- Syntactic (state-independent) typing predicate for a single or nested
`.field` projection read (`_idx.f1...fn`, either `.copy` or `.move`) to a
primitive scalar leaf type `leafTy`. Depends **only** on `body`, `env`, `idx`,
`projs`, and `leafTy` — never on `MachineState` or `AnnealStepState`. -/
inductive WellTypedLM2_2ProjectedRead
    (body : CapturedMir)
    (env : StructTypeEnv)
    (idx : Local)
    (projs : List ProjectionElem)
    (leafTy : Ty) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k : Nat)
      (hk_f : k < fields.length)
      (hk_p : k < paths.length) :
      get? body.localDecls idx = some decl →
      env decl.ty = some (fields, paths) →
      paths[k]'hk_p = projs →
      (fields[k]'hk_f).ty = leafTy →
      IsPrimScalarTy leafTy →
      ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts)
        projs leafTy (fields[k]'hk_f).offset →
      WellTypedLM2_2ProjectedRead body env idx projs leafTy

/-- Simulation outcome relation for a projected scalar leaf read (`evalOperand`
on `.copy ⟨idx, projs⟩` or `.move ⟨idx, projs⟩` vs.
`annealEvalOperand >>= annealReadImmediate`). -/
inductive ProjectedReadSimRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState)
    (leafTy : Ty) :
    OperandEvalResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  | ok (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
      (outLay : Miri.Interpreter.LocalLayout)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
      FrameRelLM2_2 body env m.machine af topFrame' →
      ImmediateRel leafTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) →
      topFrame'.localsIdentity = topFrame.localsIdentity →
      topFrame'.returnContinuation = topFrame.returnContinuation →
      topFrame'.returnPlace = topFrame.returnPlace →
      (∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value) →
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') →
      ProjectedReadSimRelLM2_2 body env af topFrame m leafTy
        (.ok (.scalar sc) af.locals)
        (.ok ⟨.scalar (.fromScalarInt msc), outLay⟩
          { m with stack := ⟨#[topFrame']⟩ })
  | ub (msg : String) (m' : AnnealStepState) :
      ProjectedReadSimRelLM2_2 body env af topFrame m leafTy
        .ub (.error (.undefinedBehavior msg) m')

private theorem translateSizeBytes_pos {n : Nat}
    (h : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) :
    0 < (translateSizeBytes n).bytes.toNat := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem annealEvalProjection_optZeroChain
    {layouts : LayoutTable} {midTy : Ty} {z : List ProjectionElem} {leafTy : Ty}
    (hz : ValidOptZeroScalarChain layouts midTy z leafTy)
    (s : Miri.Memory.Scalar AnnealProv) (st : AnnealStepState) :
    annealEvalProjection layouts ⟨.immediate (.scalar s), translateTy midTy layouts⟩
        (z.map translateProjectionElem) st =
      .ok ⟨.immediate (.scalar s), translateTy leafTy layouts⟩ st := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨_, hchain⟩
  · rfl
  · exact hchain.annealEvalProjection_scalar s st

/-- Per-local core lemma for `evalProjection_nested_field_read_simulation`,
requiring `LocalRelLM2_2` only at the read local `idx` (so multi-field
`writeAggregate` loops can evaluate projected operands on `idx ≠ dstIdx` while
`dstIdx` is mid-construction). -/
theorem evalProjection_nested_field_read_at_local
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local} {decl : LocalDecl}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < topFrame.locals.size)
    (hslot : get? af.locals idx = some slot)
    (hmls_eq : topFrame.locals[idx]'hlt_mf = mls)
    (hloc : LocalRelLM2_2 env m.machine decl body.layouts slot mls)
    (hwt : WellTypedLM2_2ProjectedRead body env idx projs leafTy)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ sc msc outLay,
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), outLay⟩
          { m with
            stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt_mf
              (translateTy decl.ty body.layouts)]⟩ } ∧
      ImmediateRel leafTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) ∨
    (∃ msg m',
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil = .ub ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') := by
  cases hwt with
  | mk decl' fields paths k hk_f hk_p hdecl' henv hpath_k hty_k hprim_leaf hchain =>
    have hdecl_eq : decl' = decl := Option.some.inj (hdecl'.symm.trans hdecl)
    cases hdecl_eq
    have hcache := hloc.layout_eq
    let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
    have hp_ne : projs ≠ [] := hchain.ne_nil
    obtain ⟨p0, ps, hp_cons⟩ : ∃ p0 ps, projs = p0 :: ps := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons p0 ps => exact ⟨p0, ps, rfl⟩
    subst hp_cons
    have hp0_nd : p0 ≠ .deref := hchain.not_deref_head
    have htr_op :
        translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩) =
          (if isMove then .Move ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩
           else .Copy ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩) := by
      cases isMove <;> rfl
    have ha_proj :
        evalOperand af.locals (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)
            .nil globals body.layouts .nil =
          match get? af.locals idx with
          | some (.init rootVal) =>
              match readProjectedValue af.locals rootVal (p0 :: ps) with
              | .ok fieldVal => .ok fieldVal af.locals
              | .ub => .ub
              | .unsupported => .unsupported
          | _ => .ub := by
      cases isMove <;> cases p0 <;> (try exact False.elim (hp0_nd rfl)) <;>
        (simp only [mkPlaceOperand, Bool.false_eq_true, ↓reduceIte]
         unfold evalOperand; dsimp only; cases get? af.locals idx with
          | none => rfl
          | some sl => cases sl <;> rfl)
    cases hloc with
    | base _ _ henv_none _ =>
      rw [henv] at henv_none; cases henv_none
    | structDead _ _ c _ _ =>
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        exact EStateM.bind_apply_error
          (annealEvalOperand_projected_dead hframes hlt_mf hdecl hmls_eq hcache)
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitImm _ _ c _ _ =>
      have heval_p := annealEvalProjection_uninit_of_validFieldProjChain hchain
        { m with stack := ⟨#[topFrame']⟩ }
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p),
            annealReadImmediate_uninit]
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitInd f' p' mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, _, hprov, hmis, _, hlive,
        hbase, hptr, hovf, _, _, _, _, _, hmask_uninit⟩
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hbnd_off := hchain.bounds
      have hlt_u64 := (translateTy decl.ty body.layouts).layout.size.bytes.toNat_lt
      have hend := lm22_allocRange_end (start := (fields[k]'hk_f).offset)
        (sz := (translateTy leafTy body.layouts).layout.size) (by omega)
      have hle_end : (Miri.ABI.Size.ofBytes ((fields[k]'hk_f).offset.bytes +
          (translateTy leafTy body.layouts).layout.size.bytes)).bytes ≤
          (translateTy decl.ty body.layouts).layout.size.bytes := by
        rw [UInt64.le_iff_toNat_le]
        dsimp [Miri.ABI.Size.ofBytes]
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)]
        exact hbnd_off
      have huninit_q : localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[k]'hk_f).offset
            (translateTy leafTy body.layouts).layout.size) =
          .ok (.error (Miri.Memory.allocRange (fields[k]'hk_f).offset
            (translateTy leafTy body.layouts).layout.size)) := by
        rw [hmask_uninit]
        exact Miri.Memory.InitMask.lazy_uninitialized_query
          (translateTy decl.ty body.layouts).layout.size _ _ hend hle_end
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + (fields[k]'hk_f).offset.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + (fields[k]'hk_f).offset.bytes) := by
        rw [hptr]; rfl
      have hread_ub := annealReadIndirectImmediate_scalar_uninit_ub
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + (fields[k]'hk_f).offset.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hprim_leaf hprov hbase hptr_proj hlive.1 huninit_q
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized memory field")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ub
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structImm f' p' v imm c henv' _ himm =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      cases himm with
      | scalarWrapper f₀ p₀ a sc msc v _ _ _ hz _ hfl₀ _ hwrap hrel hsz₀ hbool₀ hchar₀ =>
        have hk0 : k = 0 := by simp at hk_f; omega
        subst hk0
        dsimp at hpath_k hty_k
        subst hpath_k hty_k
        have heval_p := hz.annealEvalProjection_scalar (.fromScalarInt msc)
          { m with stack := ⟨#[topFrame']⟩ }
        have ha_read := hwrap.readProjectedValue_eq af.locals
        have hlaysz : (translateTy f₀.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes := by
          rw [← hfl₀, hsz₀]
        refine Or.inl ⟨sc, msc, translateTy f₀.ty body.layouts, ?_, ?_,
          .scalar sc msc hrel hlaysz hbool₀ hchar₀⟩
        · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
        · rw [htr_op]; dsimp only [Bind.bind]
          rw [EStateM.bind_apply_ok
                ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                  (Or.inr (by nofun))).trans heval_p)]
          rfl
      | scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b bOff sc₀ sc₁ msc₀ msc₁ v₀ v₁
          hvalid _ _ _ hrepr _ _ hoff₀ hoff₁ hf₀_off hf₁_off hfl₀ hfl₁
          hrt₀ hrt₁ hprim₀ hprim₁ hz₀ hz₁ hw₀ hw₁ hrel₀ hrel₁ hsz₀ hsz₁
          hbool₀ hchar₀ hbool₁ hchar₁ =>
        have hpos₀ : 0 < f₀.fieldLayout.size.bytes.toNat := by
          rw [hsz₀]; exact translateSizeBytes_pos hrel₀.validBytes
        have hpos₁ : 0 < f₁.fieldLayout.size.bytes.toNat := by
          rw [hsz₁]; exact translateSizeBytes_pos hrel₁.validBytes
        have hdisj01 := hvalid.fields_disjoint 0 1 (by simp) (by simp) (by decide)
        dsimp at hdisj01
        rw [hf₀_off, hf₁_off] at hdisj01
        have hle_bOff : f₀.fieldLayout.size.bytes.toNat ≤ bOff.bytes.toNat := by
          dsimp [Miri.ABI.Size.ZERO] at hdisj01; omega
        have hbnd₁_tot : bOff.bytes.toNat + f₁.fieldLayout.size.bytes.toNat ≤
            (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
          simpa [hf₁_off] using hvalid.fields_in_bounds 1 (by simp)
        have hk01 : k = 0 ∨ k = 1 := by simp at hk_f; omega
        rcases hk01 with rfl | rfl
        · dsimp at hpath_k hty_k; subst hty_k
          injection hpath_k with hp0_eq hps_eq; subst hp0_eq hps_eq
          have ha_read :
              readProjectedValue af.locals (.aggregate 0 [v₀, v₁]) (.field 0 mid₀ :: z₀) =
                .ok (.scalar sc₀) := by
            dsimp [readProjectedValue, get?]; exact hw₀.readProjectedValue_eq af.locals
          have hlaysz : (translateTy f₀.ty body.layouts).layout.size = translateSizeBytes sc₀.sizeBytes := by
            rw [← hfl₀, hsz₀]
          cases z₀ with
          | nil =>
            refine Or.inl ⟨sc₀, msc₀, ⟨encodeTyId mid₀, (translateTy decl.ty body.layouts).layout⟩,
              ?_, ?_, .scalar sc₀ msc₀ hrel₀ hlaysz hbool₀ hchar₀⟩
            · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
            · rw [htr_op]; dsimp only [Bind.bind, List.map, translateProjectionElem]
              rw [EStateM.bind_apply_ok
                    (annealEvalOperand_projected_scalarPair_single hframes hlt_mf hdecl hmls_eq hcache
                      (Or.inl rfl))]
              rfl
          | cons q₀ qs₀ =>
            have hmid₀_sz : (translateTy mid₀ body.layouts).layout.size = f₀.fieldLayout.size := by
              rw [← hz₀.size_eq, ← hfl₀]
            have hsz_ne₀ : (translateTy mid₀ body.layouts).layout.size ≠
                (translateTy decl.ty body.layouts).layout.size := by
              intro heq
              have := congrArg (fun s : Miri.ABI.Size => s.bytes.toNat) heq
              rw [hmid₀_sz] at this; omega
            have hbnd₀ : (translateTy mid₀ body.layouts).layout.size.bytes.toNat ≤
                (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
              rw [hmid₀_sz]; omega
            have hpf0 := projectField_immediate_scalarPair_zero_nonForget_eq
              (s0 := .fromScalarInt msc₀) (s1 := .fromScalarInt msc₁)
              hrt₀ (hz₀.isNonForget hprim₀) hrepr hoff₀ hsz_ne₀ hbnd₀
            have heval_p :
                annealEvalProjection body.layouts
                  ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                    translateTy decl.ty body.layouts⟩
                  ((.field 0 mid₀ :: q₀ :: qs₀).map translateProjectionElem)
                  { m with stack := ⟨#[topFrame']⟩ } =
                .ok ⟨.immediate (.scalar (.fromScalarInt msc₀)), translateTy f₀.ty body.layouts⟩
                  { m with stack := ⟨#[topFrame']⟩ } := by
              have hhead :
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                      translateTy decl.ty body.layouts⟩
                    (translateProjectionElem (.field 0 mid₀) :: (q₀ :: qs₀).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } =
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalar (.fromScalarInt msc₀)), translateTy mid₀ body.layouts⟩
                    ((q₀ :: qs₀).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } := by
                dsimp only [translateProjectionElem, annealEvalProjection]
                with_unfolding_all
                  simp only [Miri.Interpreter.project, hpf0, Bind.bind, Pure.pure]
                  rfl
              exact hhead.trans (annealEvalProjection_optZeroChain hz₀ _ _)
            refine Or.inl ⟨sc₀, msc₀, translateTy f₀.ty body.layouts,
              ?_, ?_, .scalar sc₀ msc₀ hrel₀ hlaysz hbool₀ hchar₀⟩
            · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
            · rw [htr_op]; dsimp only [Bind.bind]
              rw [EStateM.bind_apply_ok
                    ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                      (Or.inl (by nofun))).trans heval_p)]
              rfl
        · dsimp at hpath_k hty_k; subst hty_k
          injection hpath_k with hp0_eq hps_eq; subst hp0_eq hps_eq
          have ha_read :
              readProjectedValue af.locals (.aggregate 0 [v₀, v₁]) (.field 1 mid₁ :: z₁) =
                .ok (.scalar sc₁) := by
            dsimp [readProjectedValue, get?]; exact hw₁.readProjectedValue_eq af.locals
          have hlaysz : (translateTy f₁.ty body.layouts).layout.size = translateSizeBytes sc₁.sizeBytes := by
            rw [← hfl₁, hsz₁]
          cases z₁ with
          | nil =>
            refine Or.inl ⟨sc₁, msc₁, ⟨encodeTyId mid₁, (translateTy decl.ty body.layouts).layout⟩,
              ?_, ?_, .scalar sc₁ msc₁ hrel₁ hlaysz hbool₁ hchar₁⟩
            · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
            · rw [htr_op]; dsimp only [Bind.bind, List.map, translateProjectionElem]
              rw [EStateM.bind_apply_ok
                    (annealEvalOperand_projected_scalarPair_single hframes hlt_mf hdecl hmls_eq hcache
                      (Or.inr rfl))]
              rfl
          | cons q₁ qs₁ =>
            have hmid₁_sz : (translateTy mid₁ body.layouts).layout.size = f₁.fieldLayout.size := by
              rw [← hz₁.size_eq, ← hfl₁]
            have hbOff_ne : bOff ≠ Miri.ABI.Size.ZERO := by
              intro hz; rw [hz] at hle_bOff; dsimp [Miri.ABI.Size.ZERO] at hle_bOff; omega
            have hsz_ne₁ : (translateTy mid₁ body.layouts).layout.size ≠
                (translateTy decl.ty body.layouts).layout.size := by
              intro heq
              have := congrArg (fun s : Miri.ABI.Size => s.bytes.toNat) heq
              rw [hmid₁_sz] at this; omega
            have hbnd₁ : bOff.bytes.toNat + (translateTy mid₁ body.layouts).layout.size.bytes.toNat ≤
                (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
              rw [hmid₁_sz]; exact hbnd₁_tot
            have hpf1 := projectField_immediate_scalarPair_one_nonForget_eq
              (s0 := .fromScalarInt msc₀) (s1 := .fromScalarInt msc₁)
              hrt₁ (hz₁.isNonForget hprim₁) hrepr hoff₁ hbOff_ne hsz_ne₁ hbnd₁
            have heval_p :
                annealEvalProjection body.layouts
                  ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                    translateTy decl.ty body.layouts⟩
                  ((.field 1 mid₁ :: q₁ :: qs₁).map translateProjectionElem)
                  { m with stack := ⟨#[topFrame']⟩ } =
                .ok ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy f₁.ty body.layouts⟩
                  { m with stack := ⟨#[topFrame']⟩ } := by
              have hhead :
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                      translateTy decl.ty body.layouts⟩
                    (translateProjectionElem (.field 1 mid₁) :: (q₁ :: qs₁).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } =
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy mid₁ body.layouts⟩
                    ((q₁ :: qs₁).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } := by
                dsimp only [translateProjectionElem, annealEvalProjection]
                with_unfolding_all
                  simp only [Miri.Interpreter.project, hpf1, Bind.bind, Pure.pure]
                  rfl
              exact hhead.trans (annealEvalProjection_optZeroChain hz₁ _ _)
            refine Or.inl ⟨sc₁, msc₁, translateTy f₁.ty body.layouts,
              ?_, ?_, .scalar sc₁ msc₁ hrel₁ hlaysz hbool₁ hchar₁⟩
            · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
            · rw [htr_op]; dsimp only [Bind.bind]
              rw [EStateM.bind_apply_ok
                    ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                      (Or.inl (by nofun))).trans heval_p)]
              rfl
    | structInd f' p' v mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, word, hvalid, hplen, _, _,
        hprov, _, _, hlive, hbase, hptr, hovf, _, _, _, _, _, _, _, hfields_rel, _⟩
      obtain ⟨_, hfl_k, _, hvpath_k, sc, msc, hrpv_k, hrel_k, hsz_k, hbool_k, hchar_k, _, hread_k⟩ :=
        hfields_rel k hk_f
      rw [hpath_k] at hvpath_k hrpv_k
      rw [hty_k] at hbool_k hchar_k
      rw [hfl_k, hty_k] at hsz_k hread_k
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + (fields[k]'hk_f).offset.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + (fields[k]'hk_f).offset.bytes) := by
        rw [hptr]; rfl
      have hread_ok := annealReadIndirectImmediate_scalar_ok
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + (fields[k]'hk_f).offset.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hprim_leaf hprov hbase hptr_proj hlive.1 hread_k
      have ha_read : readProjectedValue af.locals v (p0 :: ps) = .ok (.scalar sc) :=
        (hvpath_k.readProjectedValue_indep af.locals).trans hrpv_k
      have hlaysz : (translateTy leafTy body.layouts).layout.size = translateSizeBytes sc.sizeBytes := by
        exact hsz_k
      refine Or.inl ⟨sc, msc, translateTy leafTy body.layouts, ?_, ?_,
        .scalar sc msc hrel_k hlaysz hbool_k hchar_k⟩
      · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
      · rw [htr_op]; dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ok

/-- Single and arbitrarily nested `ProjectionElem.Field` read simulation
(`LM-2.2` Deliverable 3): under `FrameRelLM2_2` and syntactic
`WellTypedLM2_2ProjectedRead`, evaluating `.copy ⟨idx, projs⟩` or
`.move ⟨idx, projs⟩` in Anneal's `evalOperand` simulates `lean-miri`'s
`annealEvalOperand >>= annealReadImmediate` across dead locals (UB),
uninitialized immediate/indirect locals (UB), `.Scalar` 1-field wrappers,
`.ScalarPair` 2-scalar tuples/structs (flat and wrapped), and `.Memory` /
memory-backed unpadded & padded aggregates at arbitrary nesting depth. -/
theorem evalProjection_nested_field_read_simulation
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {leafTy : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedRead body env idx projs leafTy)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedReadSimRelLM2_2 body env af topFrame m leafTy
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m) := by
  have hdecl_ex : ∃ decl, get? body.localDecls idx = some decl := by
    cases hwt with
    | mk decl _ _ _ _ _ hd _ _ _ _ _ => exact ⟨decl, hd⟩
  obtain ⟨decl, hdecl⟩ := hdecl_ex
  obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
  have hfr' := hframe.cache_local_layout hdecl hlt_mf
  have hval_eq :
      ∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    by_cases hk : k = idx
    · subst hk
      dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_mf, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
  rcases evalProjection_nested_field_read_at_local hframes hdecl hlt_mf hslot hmls_eq
      hloc hwt globals known with
    ⟨sc, msc, outLay, ha_ok, hm_ok, hrel⟩ | ⟨msg, m', ha_ub, hm_ub⟩
  · rw [ha_ok, hm_ok]
    exact .ok sc msc outLay topFrame' hfr' hrel rfl rfl rfl hval_eq
      (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
  · rw [ha_ub, hm_ub]
    exact .ub msg m'

/-! ## 5. Fresh Stack Allocations, `forceAllocation`, and `StructMemPlaceRel` Writes -/

private theorem align_bytes_fromBytes_fin30 :
    ∀ p : Fin 30,
      Miri.ABI.Align.bytes ⟨p.val⟩ = .ok ((1 : UInt64) <<< UInt64.ofNat p.val) ∧
      Miri.ABI.Align.fromBytes ((1 : UInt64) <<< UInt64.ofNat p.val) = .ok ⟨p.val⟩ := by
  decide

/-- Any layout alignment with `align.pow2 ≤ 29` deterministically allocates a
fresh uninitialized mutable `Miri.Memory.Allocation` under `annealZeroedStorage`. -/
theorem tryNew_uninit_of_pow2_le_29 (size : Miri.ABI.Size) (align : Miri.ABI.Align)
    (halign : align.pow2 ≤ 29) :
    ∃ rawAlloc : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok rawAlloc ∧
      (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).byteSize = size ∧
      (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).len = size.bytes.toNat ∧
      (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).mutability = .Mut ∧
      (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).provenanceMap =
        Miri.Memory.ProvenanceMap.new ∧
      (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).initializationMask =
        Miri.Memory.InitMask.new size false := by
  have hp : align.pow2 < 30 := by omega
  have ha_eq : (⟨align.pow2⟩ : Miri.ABI.Align) = align := by cases align; rfl
  obtain ⟨hbytes, hnorm⟩ := align_bytes_fromBytes_fin30 ⟨align.pow2, hp⟩
  dsimp at hbytes hnorm
  rw [ha_eq] at hbytes hnorm
  obtain ⟨rawAlloc, htry, hbs, hlen, _, hmut, _⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv)
      size align ((1 : UInt64) <<< UInt64.ofNat align.pow2) hbytes hnorm
  have htry' : Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage =
      .ok rawAlloc := htry
  obtain ⟨hprov, hmask⟩ :=
    Miri.Memory.Allocation.tryNew_uninit_shape size align rawAlloc htry
  refine ⟨rawAlloc, htry', ?_, ?_, ?_, ?_, ?_⟩ <;>
    (cases rawAlloc; simpa [Miri.Memory.Allocation.withExtra] using ‹_›)

theorem annealWriteIndirectImmediate_scalar_ok
    {s : Miri.Memory.Scalar AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {relOffset : Miri.ABI.Size}
    {fieldLay : Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {mpOff : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat} {m : AnnealStepState}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + mpOff.bytes))
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes (mpOff.bytes + relOffset.bytes)) s.size)
        s localAlloc.allocation = .ok () alloc') :
    annealWriteIndirectImmediate (.scalar s) mp relOffset fieldLay m =
      .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } := by
  have hsub : (mp.ptr.offset.bytes - baseAddr) = mpOff.bytes := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr mpOff.bytes, UInt64.add_sub_cancel]
  have hget? : m.machine.memory.live[u]? = some (allocId, localAlloc) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at hw
  with_unfolding_all
    unfold annealWriteIndirectImmediate updateAllocMachine
    simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
      hbase, hsub, hfidx, hget?, hw]

theorem annealWriteIndirectImmediate_scalarPair_ok
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {relOffset : Miri.ABI.Size}
    {pairLay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {mpOff : Miri.ABI.Size}
    {localAlloc : AnnealLocalAlloc}
    {alloc₁ alloc₂ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat} {m : AnnealStepState}
    (hrepr : pairLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + mpOff.bytes))
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hw₀ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes (mpOff.bytes + relOffset.bytes)) s0.size)
        s0 localAlloc.allocation = .ok () alloc₁)
    (hw₁ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes ((mpOff.bytes + relOffset.bytes) + bOff.bytes)) s1.size)
        s1 alloc₁ = .ok () alloc₂) :
    annealWriteIndirectImmediate (.scalarPair s0 s1) mp relOffset pairLay m =
      .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc₂ } := by
  have hsub : (mp.ptr.offset.bytes - baseAddr) = mpOff.bytes := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]
    rw [UInt64.add_comm baseAddr mpOff.bytes, UInt64.add_sub_cancel]
  have hget? : m.machine.memory.live[u]? = some (allocId, localAlloc) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget]
  rcases localAlloc with ⟨kind, alloc⟩
  dsimp only at hw₀ hw₁
  with_unfolding_all
    unfold annealWriteIndirectImmediate updateAllocMachine
    dsimp only [Miri.ABI.Size.ofBytes, get, getThe, MonadStateOf.get, EStateM.get,
      set, MonadStateOf.set, EStateM.set, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    dsimp only [Miri.ABI.Size.ofBytes] at hw₀ hw₁
    rw [hprov]
    dsimp only [Option.bind, Miri.Memory.Provenance.getAllocId]
    rw [hbase]
    dsimp only
    rw [hsub, hfidx]
    dsimp only
    rw [hget?]
    dsimp only
    rw [hrepr]
    dsimp only
    rw [hw₀]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hw₁]
    rfl

theorem forceAllocation_dead_err {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {offOpt : Option Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {lay : Miri.Interpreter.LocalLayout}
    {c : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hdead : tf.locals[localId]'hlt = ⟨.dead, c⟩) :
    Miri.Interpreter.forceAllocation (annealMutablePlaceHooks ld ly) ()
        ⟨.local 0 localId offOpt iden, lay⟩ m =
      .error (.stack (.localExpectedLive localId)) m := by
  have hget : tf.getLocal localId = .ok ⟨.dead, c⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, hdead, pure, Except.pure]
  have hgop := frame_getLocalOperand_dead _ hget
  have hfi : (annealMutablePlaceHooks ld ly).frameIndex m = .ok 0 m :=
    annealPlaceHooks_frameIndex_eq (ld := ld) (ly := ly) hframes
  have hgf : (annealMutablePlaceHooks ld ly).getFrame m = .ok tf m :=
    annealPlaceHooks_getFrame_eq (ld := ld) (ly := ly) hframes
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealMutablePlaceHooks ld ly) iden rfl,
    bind, EStateM.bind, hfi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, EStateM.pure, hgf, hgop]
  with_unfolding_all rfl

theorem forceAllocation_indirect_some_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {lay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hind : tf.locals[localId]'hlt = ⟨.live (.indirect mp), c⟩)
    (hovf : mp.ptr.offset.bytes.toNat + relOff.bytes.toNat < 2 ^ 64) :
    Miri.Interpreter.forceAllocation (annealMutablePlaceHooks ld ly) ()
        ⟨.local 0 localId (some relOff) iden, lay⟩ m =
      .ok ⟨{ mp with
              ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + relOff.bytes) }
              metadata := .none },
            lay⟩ m := by
  have hget : tf.getLocal localId = .ok ⟨.live (.indirect mp), c⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, hind, pure, Except.pure]
  have hgop := frame_getLocalOperand_live _ hget
  obtain ⟨hadd, _⟩ := size_add_of_no_overflow hovf
  have hfi : (annealMutablePlaceHooks ld ly).frameIndex m = .ok 0 m :=
    annealPlaceHooks_frameIndex_eq (ld := ld) (ly := ly) hframes
  have hgf : (annealMutablePlaceHooks ld ly).getFrame m = .ok tf m :=
    annealPlaceHooks_getFrame_eq (ld := ld) (ly := ly) hframes
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealMutablePlaceHooks ld ly) iden rfl,
    bind, EStateM.bind, hfi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, EStateM.pure, hgf, hgop, Miri.Interpreter.stackLift_ok]
  unfold annealMutablePlaceHooks annealPlaceHooks
  simp [Miri.Interpreter.MemPlaceMeta.hasMeta, hadd, pure, EStateM.pure]

theorem forceAllocation_indirect_none_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {lay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hind : tf.locals[localId]'hlt = ⟨.live (.indirect mp), c⟩) :
    Miri.Interpreter.forceAllocation (annealMutablePlaceHooks ld ly) ()
        ⟨.local 0 localId none iden, lay⟩ m =
      .ok ⟨mp, lay⟩ m := by
  have hget : tf.getLocal localId = .ok ⟨.live (.indirect mp), c⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, hind, pure, Except.pure]
  have hgop := frame_getLocalOperand_live _ hget
  have hfi : (annealMutablePlaceHooks ld ly).frameIndex m = .ok 0 m :=
    annealPlaceHooks_frameIndex_eq (ld := ld) (ly := ly) hframes
  have hgf : (annealMutablePlaceHooks ld ly).getFrame m = .ok tf m :=
    annealPlaceHooks_getFrame_eq (ld := ld) (ly := ly) hframes
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealMutablePlaceHooks ld ly) iden rfl,
    bind, EStateM.bind, hfi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, EStateM.pure, hgf, hgop, Miri.Interpreter.stackLift_ok]

theorem allocateStack_ok_of_tryNew_reserve {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {wholeLay : Miri.Interpreter.LocalLayout}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id)) :
    (annealMutablePlaceHooks ld ly).allocateStack () wholeLay m =
      .ok ⟨stackAllocPlace id, wholeLay⟩
        { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } := by
  unfold annealMutablePlaceHooks annealPlaceHooks stackAllocMachine stackAllocPlace
  simp [htry, hres, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, bind, EStateM.bind, pure, EStateM.pure]

theorem writeIndirect_fresh_stackAlloc_scalar
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 a1 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {s : Miri.Memory.Scalar AnnealProv} {relOff : Miri.ABI.Size}
    {fieldLay : Miri.Interpreter.LocalLayout}
    {stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s.size) s a0 = .ok () a1) :
    annealWriteIndirectImmediate (.scalar s)
        { stackAllocPlace id with
          ptr := { (stackAllocPlace id).ptr with
            offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
          metadata := .none }
        Miri.ABI.Size.ZERO fieldLay
        ⟨stack, stackAllocMachine mach mem' id a0⟩ =
      .ok () ⟨stack, stackAllocMachine mach mem' id a1⟩ := by
  have hbase := lookupBaseAddr_stackAllocMachine_self mach mem' id a0
  have hfidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : AnnealLocalAlloc) hfresh
  have hlt : mem'.live.size < (stackAllocMachine mach mem' id a0).memory.live.size := by
    simp [stackAllocMachine]
  have hget : (stackAllocMachine mach mem' id a0).memory.live[mem'.live.size]'hlt =
      (id, ⟨.stack, a0⟩) := by
    simp [stackAllocMachine]
  have hw' : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOff.bytes + Miri.ABI.Size.ZERO.bytes)) s.size)
      s a0 = .ok () a1 := by
    dsimp [Miri.ABI.Size.ZERO]
    rw [UInt64.add_zero]
    have hsz_eq : Miri.ABI.Size.ofBytes relOff.bytes = relOff := by cases relOff; rfl
    rw [hsz_eq]; exact hw
  have hstep := annealWriteIndirectImmediate_scalar_ok
    (mp := { stackAllocPlace id with
      ptr := { (stackAllocPlace id).ptr with
        offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
      metadata := .none })
    (relOffset := Miri.ABI.Size.ZERO) (fieldLay := fieldLay)
    (mpOff := relOff) (m := ⟨stack, stackAllocMachine mach mem' id a0⟩)
    rfl hbase rfl hlt hfidx hget hw'
  rw [hstep]
  dsimp only [updateAllocMachine, stackAllocMachine]
  rw [array_push_set!_size]

theorem writeIndirect_fresh_stackAlloc_scalarPair
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 a1 a2 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {s0 s1 : Miri.Memory.Scalar AnnealProv} {relOff : Miri.ABI.Size}
    {pairLay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hrepr : pairLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hw₀ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s0.size) s0 a0 = .ok () a1)
    (hw₁ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOff.bytes + bOff.bytes)) s1.size)
        s1 a1 = .ok () a2) :
    annealWriteIndirectImmediate (.scalarPair s0 s1)
        { stackAllocPlace id with
          ptr := { (stackAllocPlace id).ptr with
            offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
          metadata := .none }
        Miri.ABI.Size.ZERO pairLay
        ⟨stack, stackAllocMachine mach mem' id a0⟩ =
      .ok () ⟨stack, stackAllocMachine mach mem' id a2⟩ := by
  have hbase := lookupBaseAddr_stackAllocMachine_self mach mem' id a0
  have hfidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : AnnealLocalAlloc) hfresh
  have hlt : mem'.live.size < (stackAllocMachine mach mem' id a0).memory.live.size := by
    simp [stackAllocMachine]
  have hget : (stackAllocMachine mach mem' id a0).memory.live[mem'.live.size]'hlt =
      (id, ⟨.stack, a0⟩) := by
    simp [stackAllocMachine]
  have hsz_eq : Miri.ABI.Size.ofBytes (relOff.bytes + Miri.ABI.Size.ZERO.bytes) = relOff := by
    dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]; cases relOff; rfl
  have hsz_eq_b : Miri.ABI.Size.ofBytes ((relOff.bytes + Miri.ABI.Size.ZERO.bytes) + bOff.bytes) =
      Miri.ABI.Size.ofBytes (relOff.bytes + bOff.bytes) := by
    dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hstep := annealWriteIndirectImmediate_scalarPair_ok
    (mp := { stackAllocPlace id with
      ptr := { (stackAllocPlace id).ptr with
        offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
      metadata := .none })
    (relOffset := Miri.ABI.Size.ZERO) (pairLay := pairLay)
    (mpOff := relOff) (m := ⟨stack, stackAllocMachine mach mem' id a0⟩)
    hrepr rfl hbase rfl hlt hfidx hget
    (by rw [hsz_eq]; exact hw₀) (by rw [hsz_eq_b]; exact hw₁)
  rw [hstep]
  dsimp only [updateAllocMachine, stackAllocMachine]
  rw [array_push_set!_size]

theorem forceAllocation_immediate_cached_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {lay wholeLay : Miri.Interpreter.LocalLayout}
    {oldImm : Miri.Interpreter.Immediate AnnealProv}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {alloc_init : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (himm : tf.locals[localId]'hlt = ⟨.live (.immediate oldImm), some wholeLay⟩)
    (hsized : wholeLay.layout.isSized = true)
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hw_old :
      match oldImm with
      | .uninit => alloc_init = rawAlloc.withExtra none
      | _ =>
        annealWriteIndirectImmediate oldImm (stackAllocPlace id) Miri.ABI.Size.ZERO wholeLay
          { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init })
    (hovf : (annealStackBaseAddr id).toNat + relOff.bytes.toNat < 2 ^ 64) :
    Miri.Interpreter.forceAllocation (annealMutablePlaceHooks ld ly) ()
        ⟨.local 0 localId (some relOff) iden, lay⟩ m =
      .ok ⟨{ stackAllocPlace id with
              ptr := { (stackAllocPlace id).ptr with
                offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
              metadata := .none },
            lay⟩
        ⟨⟨#[{ tf with
              locals := tf.locals.set localId
                ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine m.machine mem' id alloc_init⟩ := by
  rcases m with ⟨⟨frames⟩, mach⟩
  dsimp at hframes; subst hframes
  have hget : tf.getLocal localId = .ok ⟨.live (.immediate oldImm), some wholeLay⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, himm, pure, Except.pure]
  have hgop := frame_getLocalOperand_live _ hget
  have hpl : Miri.Interpreter.placeLayoutOfLocal (annealMutablePlaceHooks ld ly) () localId
      ⟨⟨#[tf]⟩, mach⟩ = .ok wholeLay ⟨⟨#[tf]⟩, mach⟩ := by
    unfold Miri.Interpreter.placeLayoutOfLocal annealMutablePlaceHooks
    simp [annealPlaceHooks_getFrame_mk, hget, Miri.Interpreter.stackLift_ok,
      bind, EStateM.bind, pure, EStateM.pure]
  have halloc := allocateStack_ok_of_tryNew_reserve (ld := ld) (ly := ly)
    (m := ⟨⟨#[tf]⟩, mach⟩) htry hres
  have hset_op := frame_setLocalOperand_live hlt (by rw [himm]) (.indirect (stackAllocPlace id))
  rw [himm] at hset_op
  have hfi : (annealMutablePlaceHooks ld ly).frameIndex ⟨⟨#[tf]⟩, mach⟩ = .ok 0 ⟨⟨#[tf]⟩, mach⟩ :=
    annealPlaceHooks_frameIndex_eq (ld := ld) (ly := ly) (tf := tf) rfl
  have hgf : (annealMutablePlaceHooks ld ly).getFrame ⟨⟨#[tf]⟩, mach⟩ = .ok tf ⟨⟨#[tf]⟩, mach⟩ :=
    annealPlaceHooks_getFrame_mk (ld := ld) (ly := ly) tf mach
  obtain ⟨hadd, _⟩ := size_add_of_no_overflow
    (a := Miri.ABI.Size.ofBytes (annealStackBaseAddr id)) (b := relOff) hovf
  have hmoff :
      (annealMutablePlaceHooks ld ly).memoryOffset () (stackAllocPlace id) relOff .wrapping .none
        ⟨⟨#[{ tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine mach mem' id alloc_init⟩ =
      .ok { stackAllocPlace id with
            ptr := { (stackAllocPlace id).ptr with
              offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + relOff.bytes) }
            metadata := .none }
        ⟨⟨#[{ tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine mach mem' id alloc_init⟩ := by
    unfold annealMutablePlaceHooks annealPlaceHooks stackAllocPlace
    dsimp only [Miri.ABI.Size.ofBytes] at hadd ⊢
    simp only [Miri.Interpreter.MemPlaceMeta.hasMeta, hadd, Bind.bind, Pure.pure]
    rfl
  have hafter :
      (annealMutablePlaceHooks ld ly).afterLocalMovedToMemory () localId ⟨stackAllocPlace id, wholeLay⟩
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ =
      .ok () ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ := rfl
  have hgf2 :
      (annealMutablePlaceHooks ld ly).getFrame
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ =
      .ok tf ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ := rfl
  have hsf :
      (annealMutablePlaceHooks ld ly).setFrame
        { tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ =
      .ok ()
        ⟨⟨#[{ tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine mach mem' id alloc_init⟩ := rfl
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealMutablePlaceHooks ld ly) iden rfl,
    bind, EStateM.bind, hfi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, EStateM.pure, hgf]
  rw [hgop, Miri.Interpreter.stackLift_ok]
  simp only [pure, EStateM.pure]
  rw [EStateM.bind_apply_ok hpl]
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [EStateM.bind_apply_ok halloc]
  cases oldImm with
  | uninit =>
    dsimp at hw_old; subst hw_old
    simp only [EStateM.bind, pure, EStateM.pure, hafter, hgf2, hset_op,
      Miri.Interpreter.stackLift_ok, hsf, hmoff]
  | scalar s =>
    dsimp at hw_old
    have hw_hook : (annealMutablePlaceHooks ld ly).writeMemoryNoValidate () (.scalar s)
        ⟨stackAllocPlace id, wholeLay⟩
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ =
      .ok () ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ := hw_old
    simp only [EStateM.bind, hw_hook, pure, EStateM.pure, hafter, hgf2, hset_op,
      Miri.Interpreter.stackLift_ok, hsf, hmoff]
  | scalarPair s0 s1 =>
    dsimp at hw_old
    have hw_hook : (annealMutablePlaceHooks ld ly).writeMemoryNoValidate () (.scalarPair s0 s1)
        ⟨stackAllocPlace id, wholeLay⟩
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ =
      .ok () ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id alloc_init⟩ := hw_old
    simp only [EStateM.bind, hw_hook, pure, EStateM.pure, hafter, hgf2, hset_op,
      Miri.Interpreter.stackLift_ok, hsf, hmoff]

theorem forceAllocation_uninit_none_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {wholeLay : Miri.Interpreter.LocalLayout}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (himm : tf.locals[localId]'hlt = ⟨.live (.immediate .uninit), some wholeLay⟩)
    (hsized : wholeLay.layout.isSized = true)
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id)) :
    Miri.Interpreter.forceAllocation (annealMutablePlaceHooks ld ly) ()
        ⟨.local 0 localId none iden, wholeLay⟩ m =
      .ok ⟨stackAllocPlace id, wholeLay⟩
        ⟨⟨#[{ tf with
              locals := tf.locals.set localId
                ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)⟩ := by
  rcases m with ⟨⟨frames⟩, mach⟩
  dsimp at hframes; subst hframes
  have hget : tf.getLocal localId = .ok ⟨.live (.immediate .uninit), some wholeLay⟩ := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, himm, pure, Except.pure]
  have hgop := frame_getLocalOperand_live _ hget
  have hpl : Miri.Interpreter.placeLayoutOfLocal (annealMutablePlaceHooks ld ly) () localId
      ⟨⟨#[tf]⟩, mach⟩ = .ok wholeLay ⟨⟨#[tf]⟩, mach⟩ := by
    unfold Miri.Interpreter.placeLayoutOfLocal annealMutablePlaceHooks
    simp [annealPlaceHooks_getFrame_mk, hget, Miri.Interpreter.stackLift_ok,
      bind, EStateM.bind, pure, EStateM.pure]
  have halloc := allocateStack_ok_of_tryNew_reserve (ld := ld) (ly := ly)
    (m := ⟨⟨#[tf]⟩, mach⟩) htry hres
  have hset_op := frame_setLocalOperand_live hlt (by rw [himm]) (.indirect (stackAllocPlace id))
  rw [himm] at hset_op
  have hfi : (annealMutablePlaceHooks ld ly).frameIndex ⟨⟨#[tf]⟩, mach⟩ = .ok 0 ⟨⟨#[tf]⟩, mach⟩ :=
    annealPlaceHooks_frameIndex_eq (ld := ld) (ly := ly) (tf := tf) rfl
  have hgf : (annealMutablePlaceHooks ld ly).getFrame ⟨⟨#[tf]⟩, mach⟩ = .ok tf ⟨⟨#[tf]⟩, mach⟩ :=
    annealPlaceHooks_getFrame_mk (ld := ld) (ly := ly) tf mach
  have hafter :
      (annealMutablePlaceHooks ld ly).afterLocalMovedToMemory () localId ⟨stackAllocPlace id, wholeLay⟩
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ =
      .ok () ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ := rfl
  have hgf2 :
      (annealMutablePlaceHooks ld ly).getFrame
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ =
      .ok tf ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ := rfl
  have hsf :
      (annealMutablePlaceHooks ld ly).setFrame
        { tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }
        ⟨⟨#[tf]⟩, stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ =
      .ok ()
        ⟨⟨#[{ tf with locals := tf.locals.set localId ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine mach mem' id (rawAlloc.withExtra none)⟩ := rfl
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealMutablePlaceHooks ld ly) iden rfl,
    bind, EStateM.bind, hfi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, EStateM.pure, hgf]
  rw [hgop, Miri.Interpreter.stackLift_ok]
  simp only [pure, EStateM.pure]
  rw [EStateM.bind_apply_ok hpl]
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [EStateM.bind_apply_ok halloc]
  simp only [pure, EStateM.bind, EStateM.pure, hafter, hgf2, hset_op,
    Miri.Interpreter.stackLift_ok, hsf]

theorem annealWriteProjectedLocalImmediate_dead_ub
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {val : Miri.Interpreter.Immediate AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {fieldLay : Miri.Interpreter.LocalLayout}
    {c : Option Miri.Interpreter.LocalLayout}
    (hsized : fieldLay.layout.isSized = true)
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hdead : tf.locals[localId]'hlt = ⟨.dead, c⟩) :
    annealWriteProjectedLocalImmediate val
        ⟨.local 0 localId (some relOff) iden, fieldLay⟩ localDecls layouts m =
      .error (.undefinedBehavior "write to dead local") m := by
  have hfa := forceAllocation_dead_err (ld := localDecls) (ly := layouts)
    (offOpt := some relOff) (iden := iden) (lay := fieldLay) hframes hlt hdead
  unfold annealWriteProjectedLocalImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal
  simp [hsized, Option.isSome, hfa, bind, EStateM.bind]

theorem annealWriteProjectedLocalImmediate_indirect_scalar_ok
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {s : Miri.Memory.Scalar AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {fieldLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hsized : fieldLay.layout.isSized = true)
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hind : tf.locals[localId]'hlt = ⟨.live (.indirect mp), c⟩)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + relOff.bytes.toNat < 2 ^ 64)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s.size) s localAlloc.allocation = .ok () alloc') :
    annealWriteProjectedLocalImmediate (.scalar s)
        ⟨.local 0 localId (some relOff) iden, fieldLay⟩ localDecls layouts m =
      .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } := by
  have hovf' : mp.ptr.offset.bytes.toNat + relOff.bytes.toNat < 2 ^ 64 := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
  have hfa := forceAllocation_indirect_some_ok (ld := localDecls) (ly := layouts)
    (iden := iden) (lay := fieldLay) hframes hlt hind hovf'
  have hptr_off :
      ({ mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + relOff.bytes) }
          metadata := .none } : Miri.Interpreter.MemPlace AnnealProv).ptr.offset =
      Miri.ABI.Size.ofBytes (baseAddr + relOff.bytes) := by
    rw [hptr]; rfl
  have hsz_eq : Miri.ABI.Size.ofBytes (relOff.bytes + Miri.ABI.Size.ZERO.bytes) = relOff := by
    dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]; cases relOff; rfl
  have hw_ind := annealWriteIndirectImmediate_scalar_ok
    (mp := { mp with
      ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + relOff.bytes) }
      metadata := .none })
    (relOffset := Miri.ABI.Size.ZERO) (fieldLay := fieldLay) (mpOff := relOff) (m := m)
    hprov hbase hptr_off hu_lt hfidx hget (by rw [hsz_eq]; exact hw)
  unfold annealWriteProjectedLocalImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [hfa]
  dsimp only [annealMutablePlaceHooks]
  rw [hw_ind]

theorem annealWriteProjectedLocalImmediate_indirect_scalarPair_ok
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {pairLay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc}
    {alloc₁ alloc₂ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hsized : pairLay.layout.isSized = true)
    (hrepr : pairLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (hind : tf.locals[localId]'hlt = ⟨.live (.indirect mp), c⟩)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + relOff.bytes.toNat < 2 ^ 64)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hw₀ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s0.size) s0 localAlloc.allocation = .ok () alloc₁)
    (hw₁ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOff.bytes + bOff.bytes)) s1.size)
        s1 alloc₁ = .ok () alloc₂) :
    annealWriteProjectedLocalImmediate (.scalarPair s0 s1)
        ⟨.local 0 localId (some relOff) iden, pairLay⟩ localDecls layouts m =
      .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc₂ } := by
  have hovf' : mp.ptr.offset.bytes.toNat + relOff.bytes.toNat < 2 ^ 64 := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
  have hfa := forceAllocation_indirect_some_ok (ld := localDecls) (ly := layouts)
    (iden := iden) (lay := pairLay) hframes hlt hind hovf'
  have hptr_off :
      ({ mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + relOff.bytes) }
          metadata := .none } : Miri.Interpreter.MemPlace AnnealProv).ptr.offset =
      Miri.ABI.Size.ofBytes (baseAddr + relOff.bytes) := by
    rw [hptr]; rfl
  have hsz_eq : Miri.ABI.Size.ofBytes (relOff.bytes + Miri.ABI.Size.ZERO.bytes) = relOff := by
    dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]; cases relOff; rfl
  have hsz_eq_b : Miri.ABI.Size.ofBytes ((relOff.bytes + Miri.ABI.Size.ZERO.bytes) + bOff.bytes) =
      Miri.ABI.Size.ofBytes (relOff.bytes + bOff.bytes) := by
    dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hw_ind := annealWriteIndirectImmediate_scalarPair_ok
    (mp := { mp with
      ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + relOff.bytes) }
      metadata := .none })
    (relOffset := Miri.ABI.Size.ZERO) (pairLay := pairLay) (mpOff := relOff) (m := m)
    hrepr hprov hbase hptr_off hu_lt hfidx hget
    (by rw [hsz_eq]; exact hw₀) (by rw [hsz_eq_b]; exact hw₁)
  unfold annealWriteProjectedLocalImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [hfa]
  dsimp only [annealMutablePlaceHooks]
  rw [hw_ind]

theorem ValidAggregateFieldPath.noZeroByteLeaves_write
    {layouts : LayoutTable} {rootVal newVal rootVal' : Value} {projs : List ProjectionElem}
    (h : ValidAggregateFieldPath layouts rootVal projs)
    (hw : writeProjectedValue [] rootVal projs newVal = .ok rootVal')
    (hroot : NoZeroByteLeaves rootVal)
    (hnew : NoZeroByteLeaves newVal) :
    NoZeroByteLeaves rootVal' := by
  induction h generalizing rootVal' with
  | single fields idx fty oldVal hget =>
    have hlt : idx < fields.length := by
      rw [get?_eq_getElem?] at hget
      exact (List.getElem?_eq_some_iff.mp hget).1
    have hset : set? fields idx newVal = some (fields.set idx newVal) := by
      simp [set?, hlt]
    dsimp [writeProjectedValue] at hw
    rw [hget] at hw; dsimp only at hw; rw [hset] at hw
    injection hw with hr; subst hr
    exact NoZeroByteLeaves.of_set_nonempty hget hroot hnew
  | cons fields idx fty rest subVal hget _ hsub ih =>
    have hlt : idx < fields.length := by
      rw [get?_eq_getElem?] at hget
      exact (List.getElem?_eq_some_iff.mp hget).1
    have hsub_nz : NoZeroByteLeaves subVal := by
      clear hw ih hsub hlt
      induction fields generalizing idx with
      | nil => rw [get?_eq_getElem?] at hget; cases hget
      | cons hd tl ih_l =>
        rcases hroot with ⟨hhd, htl⟩
        cases idx with
        | zero =>
          rw [get?_eq_getElem?] at hget
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          rwa [← hget]
        | succ n =>
          rw [get?_eq_getElem?, List.getElem?_cons_succ, ← get?_eq_getElem?] at hget
          cases tl with
          | nil => rw [get?_eq_getElem?] at hget; cases hget
          | cons x xs => exact ih_l n hget htl
    dsimp [writeProjectedValue] at hw
    rw [hget] at hw; dsimp only at hw
    cases hw_s : writeProjectedValue [] subVal rest newVal with
    | ub | unsupported => rw [hw_s] at hw; cases hw
    | ok subVal' =>
      rw [hw_s] at hw; dsimp only at hw
      have hset : set? fields idx subVal' = some (fields.set idx subVal') := by
        simp [set?, hlt]
      rw [hset] at hw
      injection hw with hr; subst hr
      exact NoZeroByteLeaves.of_set_nonempty hget hroot (ih hw_s hsub_nz)

theorem StructMemPlaceRel.write_leaf_field
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {k : Nat} (hk : k < fields.length) (hk_p : k < paths.length)
    (hdisj_paths : ∀ j (hj_p : j < paths.length), j ≠ k →
      DisjointFieldPaths (paths[k]'hk_p) (paths[j]'hj_p))
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc'.sizeBytes)
    (hbool' : (fields[k]'hk).ty.kind = .bool → sc'.sizeBytes = 1 ∧ (sc'.bits = 0 ∨ sc'.bits = 1))
    (hchar' : (fields[k]'hk).ty.kind = .char → sc'.sizeBytes = 4 ∧ isValidCharCode sc'.bits = true) :
    ∃ (rootVal' : Value) (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (u : Nat),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      mach.lookupBaseAddr allocId = some baseAddr ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr ∧
      baseAddr.toNat + (fields[k]'hk).offset.bytes.toNat < 2 ^ 64 ∧
      ∃ (hu_lt : u < mach.memory.live.size),
        mach.memory.live.findIdx? (fun (id, _) => id == allocId) = some u ∧
        mach.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[k]'hk).offset msc'.size)
          (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' ∧
        (∀ locals, writeProjectedValue locals rootVal
          (paths[k]'hk_p) (.scalar sc') = .ok rootVal') ∧
        StructMemPlaceRel
          (updateAllocMachine mach u allocId localAlloc.kind alloc')
          ty layouts fields paths rootVal' mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, hvalid, hplen,
    ⟨_, hnz_root⟩, hleaf_bytes, hprov, hmis, hmeta, hlive, hbase, hptr, hovf,
    hmut, halign, hbsize, hlen, hpmap, hmask, hbits, hfields, hpad⟩
  obtain ⟨hp_ne_k, hfl_k, hprim_k, hvpath_k, sc_old, msc_old, hrpv_old, hrel_old, hsz_old, _, _, _, _⟩ :=
    hfields k hk
  dsimp at hp_ne_k hfl_k hprim_k hvpath_k hrpv_old hsz_old
  obtain ⟨oldVal, rootVal', hrpv_spec, hw_spec, hvpath_k', hbytes_eq, hrpv_new, _, hdisj_spec⟩ :=
    hvpath_k.writeProjectedValue_spec (.scalar sc')
  rw [hrpv_old] at hrpv_spec
  injection hrpv_spec with hold_eq; subst hold_eq
  have hsc_bytes : sc'.sizeBytes = sc_old.sizeBytes := by
    have heq_ts : translateSizeBytes sc'.sizeBytes = translateSizeBytes sc_old.sizeBytes :=
      hsz'.symm.trans hsz_old
    have h1 := hrel'.validBytes
    have h2 := hrel_old.validBytes
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      (rw [h1, h2] at heq_ts ⊢; try (revert heq_ts; decide))
  have hleaf_bytes' : valueLeafBytes rootVal' = structSumFieldBytes fields :=
    (hbytes_eq hsc_bytes).trans hleaf_bytes
  obtain ⟨alloc', words', hwrite, hbs', hlen', hmut', hpmap', hmask', hbits',
      hinit_k', hread_k', hother', hpad'⟩ :=
    writeField_preserves_other_fields_and_padding hvalid hk hrel' hsz' hbsize hlen hmut hpmap hmask
  obtain ⟨hfind_live, u, hu_lt, hfidx, hget⟩ := hlive
  have hlive_self : LiveAllocEntry (mach.memory.live.set! u (allocId, ⟨localAlloc.kind, alloc'⟩))
      allocId ⟨localAlloc.kind, alloc'⟩ :=
    LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget⟩ hu_lt hfidx ⟨localAlloc.kind, alloc'⟩
  have hbnd_k := hvalid.fields_in_bounds k hk
  have hsc'_pos : 0 < sc'.sizeBytes := by
    rcases hrel'.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
  have hnz_root' : NoZeroByteLeaves rootVal' :=
    hvpath_k.noZeroByteLeaves_write (hw_spec []) hnz_root hsc'_pos
  refine ⟨rootVal', allocId, tag, baseAddr, localAlloc, alloc', u,
    hprov, hbase, hptr, by omega, hu_lt, hfidx, hget, hwrite, hw_spec, ?_⟩
  refine .mk allocId tag baseAddr ⟨localAlloc.kind, alloc'⟩ words' hvalid hplen
    ⟨hvpath_k'.nonempty_agg, hnz_root'⟩ hleaf_bytes' hprov hmis hmeta
    hlive_self
    hbase hptr hovf hmut' halign hbs' hlen' hpmap' hmask' ?_ ?_ ?_
  · intro i hi b hlo hhi
    have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
      have := hvalid.fields_in_bounds i hi; omega
    rw [hbits' b hb_lt]
    by_cases hik : i = k
    · subst hik
      have hin : (fields[i]'hi).offset.bytes.toNat ≤ b ∧
          b < (fields[i]'hi).offset.bytes.toNat + (fields[i]'hi).fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin]
    · rw [hbits i hi b hlo hhi]; simp
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      exact ⟨hp_ne_k, hfl_k, hprim_k, hvpath_k', sc', msc', hrpv_new [],
        hrel', hsz', hbool', hchar', hinit_k', hread_k'⟩
    · obtain ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j, sc_j, msc_j, hrpv_j, hrel_j,
        hsz_j, hbool_j, hchar_j, _, hread_j⟩ := hfields j hj
      dsimp at hp_ne_j hfl_j hprim_j hvpath_j hrpv_j hsz_j hbool_j hchar_j hread_j ⊢
      have hpos_j : 0 < (fields[j]'hj).fieldLayout.size.bytes.toNat := by
        rw [hsz_j]; exact translateSizeBytes_pos hrel_j.validBytes
      obtain ⟨hinit_j', hread_j_eq⟩ := hother' j hj hjk hpos_j (hbits j hj)
      have hj_p : j < paths.length := by rw [hplen]; exact hj
      obtain ⟨hrpv_j_eq, hvpath_j'⟩ := hdisj_spec (paths[j]'hj_p)
        (hdisj_paths j hj_p hjk)
      exact ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j' hvpath_j, sc_j, msc_j,
        (hrpv_j_eq []).trans hrpv_j, hrel_j, hsz_j, hbool_j, hchar_j,
        hinit_j', hread_j_eq.trans hread_j⟩
  · intro p hp
    exact (hpad' p hp).trans (hpad p hp)

theorem ZeroScalarWrappedVal.agg_length_le_two
    {layouts : LayoutTable} {fty : Ty}
    {sc : MirAst.ScalarInt} {v : Value} {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) :
    ∀ sf, v = .aggregate 0 sf →
      (∀ a b bOff,
        (translateTy fty layouts).layout.backendRepr =
          .ScalarPair (a := a) (b := b) (bOffset := bOff) →
        sf.length ≤ 2) ∧
      (∀ a, (translateTy fty layouts).layout.backendRepr = .Scalar a → sf.length = 1) := by
  intro sf heq
  cases h with
  | bare => cases heq
  | wrap_cons => injection heq with _ hsf; subst hsf; simp

theorem ZeroScalarWrappedVal.toValidAggregateFieldPath
    {layouts : LayoutTable}
    {sc : MirAst.ScalarInt} {v : Value} {projs : List ProjectionElem}
    (h : ZeroScalarWrappedVal sc v projs) (hne : projs ≠ []) :
    ValidAggregateFieldPath layouts v projs := by
  induction h with
  | bare => exact False.elim (hne rfl)
  | wrap_cons fty rest subVal hsub ih =>
    cases rest with
    | nil => exact .single [subVal] 0 fty subVal rfl
    | cons p ps =>
      exact .cons [subVal] 0 fty (p :: ps) subVal rfl hsub.agg_length_le_two (ih (by nofun))

theorem annealWriteProjectedLocalImmediate_immediate_scalar_ok
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {s : Miri.Memory.Scalar AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {fieldLay wholeLay : Miri.Interpreter.LocalLayout}
    {oldImm : Miri.Interpreter.Immediate AnnealProv}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {alloc_init alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hsized_f : fieldLay.layout.isSized = true)
    (hsized_w : wholeLay.layout.isSized = true)
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (himm : tf.locals[localId]'hlt = ⟨.live (.immediate oldImm), some wholeLay⟩)
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw_old :
      match oldImm with
      | .uninit => alloc_init = rawAlloc.withExtra none
      | _ =>
        annealWriteIndirectImmediate oldImm (stackAllocPlace id) Miri.ABI.Size.ZERO wholeLay
          { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init })
    (hovf : (annealStackBaseAddr id).toNat + relOff.bytes.toNat < 2 ^ 64)
    (hw_new : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s.size) s alloc_init = .ok () alloc_final) :
    annealWriteProjectedLocalImmediate (.scalar s)
        ⟨.local 0 localId (some relOff) iden, fieldLay⟩ localDecls layouts m =
      .ok ()
        ⟨⟨#[{ tf with
              locals := tf.locals.set localId
                ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine m.machine mem' id alloc_final⟩ := by
  have hfa := forceAllocation_immediate_cached_ok (ld := localDecls) (ly := layouts)
    (relOff := relOff) (iden := iden) (lay := fieldLay)
    hframes hlt himm hsized_w htry hres hw_old hovf
  have hw_fin := writeIndirect_fresh_stackAlloc_scalar
    (mach := m.machine) (fieldLay := fieldLay)
    (stack := ⟨#[{ tf with
      locals := tf.locals.set localId
        ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩)
    hfresh hw_new
  unfold annealWriteProjectedLocalImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal
  simp only [hsized_f, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [hfa]
  dsimp only [annealMutablePlaceHooks]
  rw [hw_fin]

theorem annealWriteProjectedLocalImmediate_immediate_scalarPair_ok
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {s0 s1 : Miri.Memory.Scalar AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {pairLay wholeLay : Miri.Interpreter.LocalLayout}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {oldImm : Miri.Interpreter.Immediate AnnealProv}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {alloc_init alloc₁ alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hsized_f : pairLay.layout.isSized = true)
    (hrepr : pairLay.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hsized_w : wholeLay.layout.isSized = true)
    (hframes : m.stack.frames = #[tf])
    (hlt : localId < tf.locals.size)
    (himm : tf.locals[localId]'hlt = ⟨.live (.immediate oldImm), some wholeLay⟩)
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw_old :
      match oldImm with
      | .uninit => alloc_init = rawAlloc.withExtra none
      | _ =>
        annealWriteIndirectImmediate oldImm (stackAllocPlace id) Miri.ABI.Size.ZERO wholeLay
          { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init })
    (hovf : (annealStackBaseAddr id).toNat + relOff.bytes.toNat < 2 ^ 64)
    (hw₀ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange relOff s0.size) s0 alloc_init = .ok () alloc₁)
    (hw₁ : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (relOff.bytes + bOff.bytes)) s1.size)
        s1 alloc₁ = .ok () alloc_final) :
    annealWriteProjectedLocalImmediate (.scalarPair s0 s1)
        ⟨.local 0 localId (some relOff) iden, pairLay⟩ localDecls layouts m =
      .ok ()
        ⟨⟨#[{ tf with
              locals := tf.locals.set localId
                ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine m.machine mem' id alloc_final⟩ := by
  have hfa := forceAllocation_immediate_cached_ok (ld := localDecls) (ly := layouts)
    (relOff := relOff) (iden := iden) (lay := pairLay)
    hframes hlt himm hsized_w htry hres hw_old hovf
  have hw_fin := writeIndirect_fresh_stackAlloc_scalarPair
    (mach := m.machine) (pairLay := pairLay)
    (stack := ⟨#[{ tf with
      locals := tf.locals.set localId
        ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩)
    hfresh hrepr hw₀ hw₁
  unfold annealWriteProjectedLocalImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal
  simp only [hsized_f, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [hfa]
  dsimp only [annealMutablePlaceHooks]
  rw [hw_fin]

/-- Materializing an `ImmediateStructRel` (`.Scalar` wrapper or `.ScalarPair`
tuple/struct) into a fresh stack allocation `id` via `tryNew` + `reserveAllocId` +
`writeMemoryNoValidate` yields a full `StructMemPlaceRel` preserving all leaf
fields and keeping every alignment padding byte `.uninit` (`InitMask.get = .ok false`). -/
theorem StructMemPlaceRel.of_immediate
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {oldVal : Value} {oldImm : Miri.Interpreter.Immediate AnnealProv}
    {b : Nat}
    (himm : ImmediateStructRel ty layouts fields paths oldVal oldImm)
    (halign : (translateTy ty layouts).layout.align.abi.pow2 ≤ 29)
    (hwm : AllocIdWatermark (b + 1) m.machine.memory) :
    ∃ (rawAlloc : Miri.Memory.Allocation AnnealProv Unit)
      (mem' : AnnealMemory) (id : Miri.Memory.AllocId)
      (alloc_init : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      Miri.Memory.Allocation.tryNew (translateTy ty layouts).layout.size
        (translateTy ty layouts).layout.align.abi .Uninit annealZeroedStorage = .ok rawAlloc ∧
      m.machine.memory.reserveAllocId = (mem', .ok id) ∧
      mem'.live = m.machine.memory.live ∧
      mem'.live.any (fun entry => entry.1 == id) = false ∧
      (∀ alloc, AllocIdWatermark b (stackAllocMachine m.machine mem' id alloc).memory) ∧
      (∀ sz : Nat, sz < 2 ^ 32 → (annealStackBaseAddr id).toNat + sz < 2 ^ 64) ∧
      annealWriteIndirectImmediate oldImm (stackAllocPlace id) Miri.ABI.Size.ZERO
          (translateTy ty layouts)
          { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init } ∧
      StructMemPlaceRel (stackAllocMachine m.machine mem' id alloc_init)
        ty layouts fields paths oldVal (stackAllocPlace id) := by
  have hsz4g := himm.size_lt_4gib
  obtain ⟨rawAlloc, htry, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
    tryNew_uninit_of_pow2_le_29 (translateTy ty layouts).layout.size
      (translateTy ty layouts).layout.align.abi halign
  obtain ⟨mem', id, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ := hwm.reserve_step
  have hfresh : mem'.live.any (fun entry => entry.1 == id) = false := by
    rw [hlive_eq]; exact hfresh_old
  let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
  have hlen0' : a0.len = a0.byteSize.bytes.toNat := by rw [hbs0]; exact hlen0
  cases himm with
  | scalarWrapper f₀ p₀ a sc msc _ hvalid _ hp₀_ne _ hf₀_off hfl₀ hprim₀ hwrap hrel hsz₀ hbool₀ hchar₀ =>
    have hmask_w0 : InitMaskWordRel a0.initializationMask a0.byteSize
        (initWordsFalse (translateTy ty layouts).layout.size) := by
      rw [hmask0, hbs0]; exact initMaskWordRel_new_false
    obtain ⟨alloc_init, words₁, hw₀, hbs₁, hlen₁, hmut₁, hpmap₁, hmask₁, hbits₁,
        hinit₀, hread₀, _, hpad₁⟩ :=
      writeField_preserves_other_fields_and_padding hvalid (i := 0) (by simp)
        hrel hsz₀ hbs0 hlen0' hmut0 hpmap0 hmask_w0
    dsimp at hw₀
    rw [hf₀_off] at hw₀
    have hw_step :
        annealWriteIndirectImmediate (.scalar (.fromScalarInt msc)) (stackAllocPlace id)
          Miri.ABI.Size.ZERO (translateTy ty layouts)
          { m with machine := stackAllocMachine m.machine mem' id a0 } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init } := by
      have h := writeIndirect_fresh_stackAlloc_scalar (mach := m.machine)
        (relOff := Miri.ABI.Size.ZERO) (fieldLay := translateTy ty layouts)
        (stack := m.stack) hfresh hw₀
      have hptr_eq :
          { stackAllocPlace id with
            ptr := { (stackAllocPlace id).ptr with
              offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + Miri.ABI.Size.ZERO.bytes) }
            metadata := .none } = stackAllocPlace id := by
        dsimp [stackAllocPlace, Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
      rw [hptr_eq] at h; exact h
    have hvpath₀ := hwrap.toValidAggregateFieldPath (layouts := layouts) hp₀_ne
    have hleaf_bytes : valueLeafBytes oldVal = structSumFieldBytes [f₀] := by
      rw [hwrap.valueLeafBytes_eq]
      dsimp [structSumFieldBytes]
      rw [hsz₀]
      have hb0 : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
        rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      omega
    have hsc_pos : 0 < sc.sizeBytes := by
      rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    refine ⟨rawAlloc, mem', id, alloc_init, htry, hres, hlive_eq, hfresh,
      hwm_next, hovf_all, hw_step, ?_⟩
    refine .mk id Miri.Memory.BorTag.one (annealStackBaseAddr id) ⟨.stack, alloc_init⟩ words₁ hvalid rfl
      ⟨hvpath₀.nonempty_agg, hwrap.noZeroByteLeaves hsc_pos⟩ hleaf_bytes rfl rfl rfl
      (LiveAllocEntry.of_push_fresh_self _ hfresh)
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _)
      rfl (hovf_all _ hsz4g) hmut₁
      (annealStackBaseAddr_isAligned id _ halign)
      hbs₁ hlen₁ hpmap₁ hmask₁ ?_ ?_ ?_
    · intro i hi b hlo hhi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
        have := hvalid.fields_in_bounds 0 (by simp); dsimp at hhi this; omega
      rw [hbits₁ b hb_lt]
      have hin : f₀.offset.bytes.toNat ≤ b ∧ b < f₀.offset.bytes.toNat + f₀.fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin]
    · intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact ⟨hp₀_ne, hfl₀, hprim₀, hvpath₀, sc, msc, hwrap.readProjectedValue_eq [],
        hrel, hsz₀, hbool₀, hchar₀, hinit₀, hread₀⟩
    · intro p hp
      rw [hpad₁ p hp, hmask0]
      exact (initMaskWordRel_get (initMaskWordRel_new_false) hp.1).trans
        (by rw [maskBlocksGetBit_initWordsFalse])
  | scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b_sc bOff sc₀ sc₁ msc₀ msc₁ v₀ v₁
      hvalid _ _ _ hrepr _ _ _ _ hf₀_off hf₁_off hfl₀ hfl₁
      _ _ hprim₀ hprim₁ _ _ hw₀ hw₁ hrel₀ hrel₁ hsz₀ hsz₁
      hbool₀ hchar₀ hbool₁ hchar₁ =>
    have hmask_w0 : InitMaskWordRel a0.initializationMask a0.byteSize
        (initWordsFalse (translateTy ty layouts).layout.size) := by
      rw [hmask0, hbs0]; exact initMaskWordRel_new_false
    obtain ⟨a₁, alloc_init, words₂, hw_a0, hw_a1, hbs₂, hlen₂, hmut₂, hpmap₂, hmask₂,
        hbits₂, hinit₀, hread₀, hinit₁, hread₁, _, hpad₂⟩ :=
      writeScalarPairField_preserves_other_fields_and_padding hvalid
        (i₀ := 0) (i₁ := 1) (by simp) (by simp) (by decide)
        hrel₀ hrel₁ hsz₀ hsz₁ hbs0 hlen0' hmut0 hpmap0 hmask_w0
    dsimp at hw_a0 hw_a1
    rw [hf₀_off] at hw_a0
    rw [hf₁_off] at hw_a1
    have hw_step :
        annealWriteIndirectImmediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))
          (stackAllocPlace id) Miri.ABI.Size.ZERO (translateTy ty layouts)
          { m with machine := stackAllocMachine m.machine mem' id a0 } =
        .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_init } := by
      have hbOff_z : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + bOff.bytes) = bOff := by
        dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]; cases bOff; rfl
      have h := writeIndirect_fresh_stackAlloc_scalarPair (mach := m.machine)
        (relOff := Miri.ABI.Size.ZERO) (pairLay := translateTy ty layouts)
        (stack := m.stack) hfresh hrepr hw_a0 (by rw [hbOff_z]; exact hw_a1)
      have hptr_eq :
          { stackAllocPlace id with
            ptr := { (stackAllocPlace id).ptr with
              offset := Miri.ABI.Size.ofBytes ((annealStackBaseAddr id) + Miri.ABI.Size.ZERO.bytes) }
            metadata := .none } = stackAllocPlace id := by
        dsimp [stackAllocPlace, Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
      rw [hptr_eq] at h; exact h
    have hvpath₀ : ValidAggregateFieldPath layouts (.aggregate 0 [v₀, v₁]) (.field 0 mid₀ :: z₀) := by
      cases z₀ with
      | nil => exact .single [v₀, v₁] 0 mid₀ v₀ rfl
      | cons q qs =>
        exact .cons [v₀, v₁] 0 mid₀ (q :: qs) v₀ rfl hw₀.agg_length_le_two
          (hw₀.toValidAggregateFieldPath (by nofun))
    have hvpath₁ : ValidAggregateFieldPath layouts (.aggregate 0 [v₀, v₁]) (.field 1 mid₁ :: z₁) := by
      cases z₁ with
      | nil => exact .single [v₀, v₁] 1 mid₁ v₁ rfl
      | cons q qs =>
        exact .cons [v₀, v₁] 1 mid₁ (q :: qs) v₁ rfl hw₁.agg_length_le_two
          (hw₁.toValidAggregateFieldPath (by nofun))
    have hleaf_bytes : valueLeafBytes (.aggregate 0 [v₀, v₁]) = structSumFieldBytes [f₀, f₁] := by
      dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList, structSumFieldBytes]
      rw [hw₀.valueLeafBytes_eq, hw₁.valueLeafBytes_eq, hsz₀, hsz₁]
      have hb0 : (translateSizeBytes sc₀.sizeBytes).bytes.toNat = sc₀.sizeBytes := by
        rcases hrel₀.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      have hb1 : (translateSizeBytes sc₁.sizeBytes).bytes.toNat = sc₁.sizeBytes := by
        rcases hrel₁.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      omega
    have hsc0_pos : 0 < sc₀.sizeBytes := by
      rcases hrel₀.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    have hsc1_pos : 0 < sc₁.sizeBytes := by
      rcases hrel₁.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    refine ⟨rawAlloc, mem', id, alloc_init, htry, hres, hlive_eq, hfresh,
      hwm_next, hovf_all, hw_step, ?_⟩
    refine .mk id Miri.Memory.BorTag.one (annealStackBaseAddr id) ⟨.stack, alloc_init⟩ words₂ hvalid rfl
      ⟨⟨v₀, [v₁], rfl⟩, ⟨hw₀.noZeroByteLeaves hsc0_pos, hw₁.noZeroByteLeaves hsc1_pos, True.intro⟩⟩
      hleaf_bytes rfl rfl rfl
      (LiveAllocEntry.of_push_fresh_self _ hfresh)
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _)
      rfl (hovf_all _ hsz4g) hmut₂
      (annealStackBaseAddr_isAligned id _ halign)
      hbs₂ hlen₂ hpmap₂ hmask₂ ?_ ?_ ?_
    · intro i hi b hlo hhi
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl
      · have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
          have := hvalid.fields_in_bounds 0 (by simp); dsimp at hhi this; omega
        rw [hbits₂ b hb_lt]
        have hin : f₀.offset.bytes.toNat ≤ b ∧ b < f₀.offset.bytes.toNat + f₀.fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin]
      · have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
          have := hvalid.fields_in_bounds 1 (by simp); dsimp at hhi this; omega
        rw [hbits₂ b hb_lt]
        have hin : f₁.offset.bytes.toNat ≤ b ∧ b < f₁.offset.bytes.toNat + f₁.fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin]
    · intro i hi
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl
      · exact ⟨by nofun, hfl₀, hprim₀, hvpath₀, sc₀, msc₀,
          by dsimp [readProjectedValue, get?]; exact hw₀.readProjectedValue_eq [],
          hrel₀, hsz₀, hbool₀, hchar₀, hinit₀, hread₀⟩
      · exact ⟨by nofun, hfl₁, hprim₁, hvpath₁, sc₁, msc₁,
          by dsimp [readProjectedValue, get?]; exact hw₁.readProjectedValue_eq [],
          hrel₁, hsz₁, hbool₁, hchar₁, hinit₁, hread₁⟩
    · intro p hp
      rw [hpad₂ p hp, hmask0]
      exact (initMaskWordRel_get (initMaskWordRel_new_false) hp.1).trans
        (by rw [maskBlocksGetBit_initWordsFalse])

/-- Overwriting the existing stack allocation behind a memory-backed aggregate
local with a whole immediate (`annealWriteIndirectImmediate` at relative offset
`0`) re-establishes `StructMemPlaceRel` for the new value.

Upstream `Miri.Interpreter.writePlaceImmediateNoValidate` takes this path for an
unprojected write to an `.indirect` local (`asMplaceOrMutableLocal` returns
`.memory`), so `annealWriteImmediate` does too. The allocation may hold any
previous field contents, but every inter-field and trailing padding byte must be
uninitialized, which both `StructMemPlaceRel` (`padding_uninit`) and
`UninitStructMemPlaceRel` (`mask_uninit`) provide. The write initializes exactly
the leaf field bytes and leaves every padding byte `.uninit`. -/
theorem StructMemPlaceRel.of_overwrite_immediate
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc} {words0 : Array UInt64}
    (himm : ImmediateStructRel ty layouts fields paths newVal imm)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (hmut : localAlloc.allocation.mutability = .Mut)
    (halign : mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
    (hbs : localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
    (hpmap : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel localAlloc.allocation.initializationMask
      localAlloc.allocation.byteSize words0)
    (hpad : ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      localAlloc.allocation.initializationMask.get
        (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) :
    ∃ (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp := by
  obtain ⟨hfind_live, u, hu_lt, hfidx, hget⟩ := hlive
  have hlive_self : ∀ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      LiveAllocEntry (m.machine.memory.live.set! u (allocId, ⟨localAlloc.kind, alloc'⟩))
        allocId ⟨localAlloc.kind, alloc'⟩ := fun alloc' =>
    LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget⟩ hu_lt hfidx
      ⟨localAlloc.kind, alloc'⟩
  have hptr0 : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hzz : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + Miri.ABI.Size.ZERO.bytes) =
      Miri.ABI.Size.ZERO := by
    dsimp [Miri.ABI.Size.ZERO]; rfl
  cases himm with
  | scalarWrapper f₀ p₀ a sc msc _ hvalid _ hp₀_ne _ hf₀_off hfl₀ hprim₀ hwrap hrel hsz₀ hbool₀ hchar₀ =>
    obtain ⟨alloc', words₁, hw₀, hbs₁, hlen₁, hmut₁, hpmap₁, hmask₁, hbits₁,
        hinit₀, hread₀, _, hpad₁⟩ :=
      writeField_preserves_other_fields_and_padding hvalid (i := 0) (by simp)
        hrel hsz₀ hbs hlen hmut hpmap hmask
    dsimp at hw₀
    rw [hf₀_off] at hw₀
    have hw_step :
        annealWriteIndirectImmediate (.scalar (.fromScalarInt msc)) mp Miri.ABI.Size.ZERO
          (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } :=
      annealWriteIndirectImmediate_scalar_ok (mpOff := Miri.ABI.Size.ZERO)
        hprov hbase hptr0 hu_lt hfidx hget (by rw [hzz]; exact hw₀)
    have hvpath₀ := hwrap.toValidAggregateFieldPath (layouts := layouts) hp₀_ne
    have hleaf_bytes : valueLeafBytes newVal = structSumFieldBytes [f₀] := by
      rw [hwrap.valueLeafBytes_eq]
      dsimp [structSumFieldBytes]
      rw [hsz₀]
      have hb0 : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
        rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      omega
    have hsc_pos : 0 < sc.sizeBytes := by
      rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    refine ⟨u, hu_lt, alloc', hget, hw_step, ?_⟩
    refine .mk allocId tag baseAddr ⟨localAlloc.kind, alloc'⟩ words₁ hvalid rfl
      ⟨hvpath₀.nonempty_agg, hwrap.noZeroByteLeaves hsc_pos⟩ hleaf_bytes hprov hmis hmeta
      (hlive_self alloc') hbase hptr hovf hmut₁ halign hbs₁ hlen₁ hpmap₁ hmask₁ ?_ ?_ ?_
    · intro i hi b hlo hhi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
        have := hvalid.fields_in_bounds 0 (by simp); dsimp at hhi this; omega
      rw [hbits₁ b hb_lt]
      have hin : f₀.offset.bytes.toNat ≤ b ∧ b < f₀.offset.bytes.toNat + f₀.fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin]
    · intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact ⟨hp₀_ne, hfl₀, hprim₀, hvpath₀, sc, msc, hwrap.readProjectedValue_eq [],
        hrel, hsz₀, hbool₀, hchar₀, hinit₀, hread₀⟩
    · intro p hp
      exact (hpad₁ p hp).trans (hpad p hp)
  | scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b_sc bOff sc₀ sc₁ msc₀ msc₁ v₀ v₁
      hvalid _ _ _ hrepr _ _ _ _ hf₀_off hf₁_off hfl₀ hfl₁
      _ _ hprim₀ hprim₁ _ _ hw₀ hw₁ hrel₀ hrel₁ hsz₀ hsz₁
      hbool₀ hchar₀ hbool₁ hchar₁ =>
    obtain ⟨a₁, alloc', words₂, hw_a0, hw_a1, hbs₂, hlen₂, hmut₂, hpmap₂, hmask₂,
        hbits₂, hinit₀, hread₀, hinit₁, hread₁, _, hpad₂⟩ :=
      writeScalarPairField_preserves_other_fields_and_padding hvalid
        (i₀ := 0) (i₁ := 1) (by simp) (by simp) (by decide)
        hrel₀ hrel₁ hsz₀ hsz₁ hbs hlen hmut hpmap hmask
    dsimp at hw_a0 hw_a1
    rw [hf₀_off] at hw_a0
    rw [hf₁_off] at hw_a1
    have hzb : Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ZERO.bytes + Miri.ABI.Size.ZERO.bytes) + bOff.bytes) = bOff := by
      dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]; cases bOff; rfl
    have hw_step :
        annealWriteIndirectImmediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))
          mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } :=
      annealWriteIndirectImmediate_scalarPair_ok (mpOff := Miri.ABI.Size.ZERO)
        hrepr hprov hbase hptr0 hu_lt hfidx hget
        (by rw [hzz]; exact hw_a0) (by rw [hzb]; exact hw_a1)
    have hvpath₀ : ValidAggregateFieldPath layouts (.aggregate 0 [v₀, v₁]) (.field 0 mid₀ :: z₀) := by
      cases z₀ with
      | nil => exact .single [v₀, v₁] 0 mid₀ v₀ rfl
      | cons q qs =>
        exact .cons [v₀, v₁] 0 mid₀ (q :: qs) v₀ rfl hw₀.agg_length_le_two
          (hw₀.toValidAggregateFieldPath (by nofun))
    have hvpath₁ : ValidAggregateFieldPath layouts (.aggregate 0 [v₀, v₁]) (.field 1 mid₁ :: z₁) := by
      cases z₁ with
      | nil => exact .single [v₀, v₁] 1 mid₁ v₁ rfl
      | cons q qs =>
        exact .cons [v₀, v₁] 1 mid₁ (q :: qs) v₁ rfl hw₁.agg_length_le_two
          (hw₁.toValidAggregateFieldPath (by nofun))
    have hleaf_bytes : valueLeafBytes (.aggregate 0 [v₀, v₁]) = structSumFieldBytes [f₀, f₁] := by
      dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList, structSumFieldBytes]
      rw [hw₀.valueLeafBytes_eq, hw₁.valueLeafBytes_eq, hsz₀, hsz₁]
      have hb0 : (translateSizeBytes sc₀.sizeBytes).bytes.toNat = sc₀.sizeBytes := by
        rcases hrel₀.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      have hb1 : (translateSizeBytes sc₁.sizeBytes).bytes.toNat = sc₁.sizeBytes := by
        rcases hrel₁.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      omega
    have hsc0_pos : 0 < sc₀.sizeBytes := by
      rcases hrel₀.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    have hsc1_pos : 0 < sc₁.sizeBytes := by
      rcases hrel₁.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
    refine ⟨u, hu_lt, alloc', hget, hw_step, ?_⟩
    refine .mk allocId tag baseAddr ⟨localAlloc.kind, alloc'⟩ words₂ hvalid rfl
      ⟨⟨v₀, [v₁], rfl⟩, ⟨hw₀.noZeroByteLeaves hsc0_pos, hw₁.noZeroByteLeaves hsc1_pos, True.intro⟩⟩
      hleaf_bytes hprov hmis hmeta
      (hlive_self alloc') hbase hptr hovf hmut₂ halign hbs₂ hlen₂ hpmap₂ hmask₂ ?_ ?_ ?_
    · intro i hi b hlo hhi
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl
      · have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
          have := hvalid.fields_in_bounds 0 (by simp); dsimp at hhi this; omega
        rw [hbits₂ b hb_lt]
        have hin : f₀.offset.bytes.toNat ≤ b ∧ b < f₀.offset.bytes.toNat + f₀.fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin]
      · have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
          have := hvalid.fields_in_bounds 1 (by simp); dsimp at hhi this; omega
        rw [hbits₂ b hb_lt]
        have hin : f₁.offset.bytes.toNat ≤ b ∧ b < f₁.offset.bytes.toNat + f₁.fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin]
    · intro i hi
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl
      · exact ⟨by nofun, hfl₀, hprim₀, hvpath₀, sc₀, msc₀,
          by dsimp [readProjectedValue, get?]; exact hw₀.readProjectedValue_eq [],
          hrel₀, hsz₀, hbool₀, hchar₀, hinit₀, hread₀⟩
      · exact ⟨by nofun, hfl₁, hprim₁, hvpath₁, sc₁, msc₁,
          by dsimp [readProjectedValue, get?]; exact hw₁.readProjectedValue_eq [],
          hrel₁, hsz₁, hbool₁, hchar₁, hinit₁, hread₁⟩
    · intro p hp
      exact (hpad₂ p hp).trans (hpad p hp)

/-- `StructMemPlaceRel` provides every precondition of
`StructMemPlaceRel.of_overwrite_immediate`: overwriting an initialized
memory-backed aggregate with a whole immediate of the same type yields a
`StructMemPlaceRel` for the new value. -/
theorem StructMemPlaceRel.overwrite_immediate
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {oldVal newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmp : StructMemPlaceRel m.machine ty layouts fields paths oldVal mp)
    (himm : ImmediateStructRel ty layouts fields paths newVal imm) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (localAlloc : AnnealLocalAlloc)
      (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp := by
  rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, words, _, _, _, _, hprov, hmis, hmeta,
    hlive, hbase, hptr, hovf, hmut, halign, hbs, hlen, hpmap, hmask, _, _, hpad⟩
  obtain ⟨u, hu_lt, alloc', hget, hw, hrel⟩ :=
    StructMemPlaceRel.of_overwrite_immediate himm hprov hmis hmeta hlive hbase hptr hovf
      hmut halign hbs hlen hpmap hmask hpad
  exact ⟨allocId, tag, localAlloc, u, hu_lt, alloc', hprov, hget, hw, hrel⟩

/-- `UninitStructMemPlaceRel` (a memory-backed aggregate local whose allocation
is entirely uninitialized) provides every precondition of
`StructMemPlaceRel.of_overwrite_immediate`. -/
theorem UninitStructMemPlaceRel.overwrite_immediate
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmp : UninitStructMemPlaceRel m.machine ty layouts fields mp)
    (himm : ImmediateStructRel ty layouts fields paths newVal imm) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (localAlloc : AnnealLocalAlloc)
      (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp := by
  rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, _, hprov, hmis, hmeta,
    hlive, hbase, hptr, hovf, hmut, halign, hbs, hlen, hpmap, hmask_new⟩
  have hmask : InitMaskWordRel localAlloc.allocation.initializationMask
      localAlloc.allocation.byteSize (initWordsFalse (translateTy ty layouts).layout.size) := by
    rw [hmask_new, hbs]; exact initMaskWordRel_new_false
  have hpad : ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      localAlloc.allocation.initializationMask.get
        (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false := by
    intro p hp
    rw [hmask_new]
    exact (initMaskWordRel_get (initMaskWordRel_new_false) hp.1).trans
      (by rw [maskBlocksGetBit_initWordsFalse])
  obtain ⟨u, hu_lt, alloc', hget, hw, hrel⟩ :=
    StructMemPlaceRel.of_overwrite_immediate himm hprov hmis hmeta hlive hbase hptr hovf
      hmut halign hbs hlen hpmap hmask hpad
  exact ⟨allocId, tag, localAlloc, u, hu_lt, alloc', hprov, hget, hw, hrel⟩

/-- Writing a whole 2-scalar `ScalarPair` sub-struct `.aggregate 0 [.scalar sc₀', .scalar sc₁']`
at non-empty projection path `projs` into a memory-backed aggregate (`StructMemPlaceRel`)
updates leaves `k₀` (`projs ++ [.field 0 mid₀]`) and `k₁` (`projs ++ [.field 1 mid₁]`)
in place while preserving all other leaf fields (`j ≠ k₀, j ≠ k₁`) and keeping every
inter-field and trailing padding byte `.uninit`. -/
theorem StructMemPlaceRel.write_substruct_scalarPair
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {projs : List ProjectionElem} {subIdx : Nat} {subTy mid₀ mid₁ : Ty}
    {a b : Miri.ABI.Scalar} {bOff : Miri.ABI.Size}
    {k₀ k₁ : Nat} (hk₀ : k₀ < fields.length) (hk₁ : k₁ < fields.length)
    (hk₀_p : k₀ < paths.length) (hk₁_p : k₁ < paths.length)
    (hne : k₀ ≠ k₁)
    (hprojs_ne : projs ≠ [])
    (hlast : projs.getLast? = some (.field subIdx subTy))
    (hrepr : (translateTy subTy layouts).layout.backendRepr =
      .ScalarPair (a := a) (b := b) (bOffset := bOff))
    (hpath₀ : paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀])
    (hpath₁ : paths[k₁]'hk₁_p = projs ++ [.field 1 mid₁])
    (hdisj_paths : ∀ j (hj_p : j < paths.length), j ≠ k₀ → j ≠ k₁ →
      DisjointFieldPaths projs (paths[j]'hj_p))
    {sc₀' sc₁' : MirAst.ScalarInt} {msc₀' msc₁' : Miri.Memory.ScalarInt}
    (hrel₀' : ScalarRel sc₀' msc₀')
    (hrel₁' : ScalarRel sc₁' msc₁')
    (hsz₀' : (fields[k₀]'hk₀).fieldLayout.size = translateSizeBytes sc₀'.sizeBytes)
    (hsz₁' : (fields[k₁]'hk₁).fieldLayout.size = translateSizeBytes sc₁'.sizeBytes)
    (hbool₀' : (fields[k₀]'hk₀).ty.kind = .bool → sc₀'.sizeBytes = 1 ∧ (sc₀'.bits = 0 ∨ sc₀'.bits = 1))
    (hchar₀' : (fields[k₀]'hk₀).ty.kind = .char → sc₀'.sizeBytes = 4 ∧ isValidCharCode sc₀'.bits = true)
    (hbool₁' : (fields[k₁]'hk₁).ty.kind = .bool → sc₁'.sizeBytes = 1 ∧ (sc₁'.bits = 0 ∨ sc₁'.bits = 1))
    (hchar₁' : (fields[k₁]'hk₁).ty.kind = .char → sc₁'.sizeBytes = 4 ∧ isValidCharCode sc₁'.bits = true) :
    ∃ (rootVal' : Value) (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (alloc₁ alloc₂ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (u : Nat),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      mach.lookupBaseAddr allocId = some baseAddr ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr ∧
      baseAddr.toNat + (fields[k₀]'hk₀).offset.bytes.toNat < 2 ^ 64 ∧
      ∃ (hu_lt : u < mach.memory.live.size),
        mach.memory.live.findIdx? (fun (id, _) => id == allocId) = some u ∧
        mach.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[k₀]'hk₀).offset msc₀'.size)
          (.fromScalarInt msc₀') localAlloc.allocation = .ok () alloc₁ ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[k₁]'hk₁).offset msc₁'.size)
          (.fromScalarInt msc₁') alloc₁ = .ok () alloc₂ ∧
        (∀ locals, writeProjectedValue locals rootVal projs
          (.aggregate 0 [.scalar sc₀', .scalar sc₁']) = .ok rootVal') ∧
        StructMemPlaceRel
          (updateAllocMachine mach u allocId localAlloc.kind alloc₂)
          ty layouts fields paths rootVal' mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, hvalid, hplen,
    ⟨_, hnz_root⟩, hleaf_bytes, hprov, hmis, hmeta, hlive, hbase, hptr, hovf,
    hmut, halign, hbsize, hlen, hpmap, hmask, hbits, hfields, hpad⟩
  obtain ⟨hp_ne_0, hfl_0, hprim_0, hvpath_0, sc₀_old, msc₀_old, hrpv_0, hrel₀_old, hsz₀_old, _, _, _, _⟩ :=
    hfields k₀ hk₀
  obtain ⟨hp_ne_1, hfl_1, hprim_1, hvpath_1, sc₁_old, msc₁_old, hrpv_1, hrel₁_old, hsz₁_old, _, _, _, _⟩ :=
    hfields k₁ hk₁
  dsimp at hp_ne_0 hfl_0 hprim_0 hvpath_0 hrpv_0 hsz₀_old hp_ne_1 hfl_1 hprim_1 hvpath_1 hrpv_1 hsz₁_old
  have hvpath_0_app : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 0 mid₀]) := by
    rwa [← hpath₀]
  have hrpv_0_app : readProjectedValue [] rootVal (projs ++ [.field 0 mid₀]) = .ok (.scalar sc₀_old) := by
    rwa [← hpath₀]
  have hvpath_1_app : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 1 mid₁]) := by
    rwa [← hpath₁]
  have hrpv_1_app : readProjectedValue [] rootVal (projs ++ [.field 1 mid₁]) = .ok (.scalar sc₁_old) := by
    rwa [← hpath₁]
  obtain ⟨hvpath_sub, hrpv_sub⟩ :=
    ValidAggregateFieldPath.read_substruct_scalarPair hprojs_ne hlast hrepr
      hvpath_0_app hrpv_0_app hvpath_1_app hrpv_1_app
  let newSubVal : Value := .aggregate 0 [.scalar sc₀', .scalar sc₁']
  obtain ⟨oldSubVal, rootVal', hrpv_spec, hw_spec, hvpath_sub', hbytes_eq, _, happend_spec, hdisj_spec⟩ :=
    hvpath_sub.writeProjectedValue_spec newSubVal
  rw [hrpv_sub []] at hrpv_spec
  injection hrpv_spec with hold_eq; subst hold_eq
  have hsc0_bytes : sc₀'.sizeBytes = sc₀_old.sizeBytes := by
    have heq_ts : translateSizeBytes sc₀'.sizeBytes = translateSizeBytes sc₀_old.sizeBytes :=
      hsz₀'.symm.trans hsz₀_old
    have h1 := hrel₀'.validBytes
    have h2 := hrel₀_old.validBytes
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      (rw [h1, h2] at heq_ts ⊢; try (revert heq_ts; decide))
  have hsc1_bytes : sc₁'.sizeBytes = sc₁_old.sizeBytes := by
    have heq_ts : translateSizeBytes sc₁'.sizeBytes = translateSizeBytes sc₁_old.sizeBytes :=
      hsz₁'.symm.trans hsz₁_old
    have h1 := hrel₁'.validBytes
    have h2 := hrel₁_old.validBytes
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      (rw [h1, h2] at heq_ts ⊢; try (revert heq_ts; decide))
  have hsub_bytes : valueLeafBytes newSubVal =
      valueLeafBytes (.aggregate 0 [.scalar sc₀_old, .scalar sc₁_old]) := by
    dsimp [newSubVal, valueLeafBytes, valueLeafBytes.valueLeafBytesList]
    omega
  have hleaf_bytes' : valueLeafBytes rootVal' = structSumFieldBytes fields :=
    (hbytes_eq hsub_bytes).trans hleaf_bytes
  obtain ⟨alloc₁, alloc₂, words', hw₀, hw₁, hbs', hlen', hmut', hpmap', hmask', hbits',
      hinit_0', hread_0', hinit_1', hread_1', hother', hpad'⟩ :=
    writeScalarPairField_preserves_other_fields_and_padding hvalid hk₀ hk₁ hne
      hrel₀' hrel₁' hsz₀' hsz₁' hbsize hlen hmut hpmap hmask
  obtain ⟨hfind_live, u, hu_lt, hfidx, hget⟩ := hlive
  have hlive_self : LiveAllocEntry (mach.memory.live.set! u (allocId, ⟨localAlloc.kind, alloc₂⟩))
      allocId ⟨localAlloc.kind, alloc₂⟩ :=
    LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget⟩ hu_lt hfidx ⟨localAlloc.kind, alloc₂⟩
  have hbnd_0 := hvalid.fields_in_bounds k₀ hk₀
  have hsc0'_pos : 0 < sc₀'.sizeBytes := by
    rcases hrel₀'.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
  have hsc1'_pos : 0 < sc₁'.sizeBytes := by
    rcases hrel₁'.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
  have hnz_new : NoZeroByteLeaves newSubVal :=
    ⟨hsc0'_pos, hsc1'_pos, True.intro⟩
  have hnz_root' : NoZeroByteLeaves rootVal' :=
    hvpath_sub.noZeroByteLeaves_write (hw_spec []) hnz_root hnz_new
  have hnew_len : ∀ sf_old sf_new,
      Value.aggregate 0 [.scalar sc₀_old, .scalar sc₁_old] = .aggregate 0 sf_old →
      newSubVal = .aggregate 0 sf_new → sf_new.length = sf_old.length := by
    intro sf_old sf_new h1 h2
    injection h1 with _ h1'; injection h2 with _ h2'
    subst h1' h2'; rfl
  refine ⟨rootVal', allocId, tag, baseAddr, localAlloc, alloc₁, alloc₂, u,
    hprov, hbase, hptr, by omega, hu_lt, hfidx, hget, hw₀, hw₁, hw_spec, ?_⟩
  refine .mk allocId tag baseAddr ⟨localAlloc.kind, alloc₂⟩ words' hvalid hplen
    ⟨hvpath_sub'.nonempty_agg, hnz_root'⟩ hleaf_bytes' hprov hmis hmeta
    hlive_self hbase hptr hovf hmut' halign hbs' hlen' hpmap' hmask' ?_ ?_ ?_
  · intro i hi b hlo hhi
    have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
      have := hvalid.fields_in_bounds i hi; omega
    rw [hbits' b hb_lt]
    by_cases hi0 : i = k₀
    · subst hi0
      have hin0 : (fields[i]'hi).offset.bytes.toNat ≤ b ∧
          b < (fields[i]'hi).offset.bytes.toNat + (fields[i]'hi).fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin0]
    · by_cases hi1 : i = k₁
      · subst hi1
        have hin1 : (fields[i]'hi).offset.bytes.toNat ≤ b ∧
            b < (fields[i]'hi).offset.bytes.toNat + (fields[i]'hi).fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin1]
      · rw [hbits i hi b hlo hhi]; simp
  · intro j hj
    by_cases hj0 : j = k₀
    · subst hj0
      obtain ⟨hr_0, hp_0⟩ := happend_spec [.field 0 mid₀]
      have hv_0 : ValidAggregateFieldPath layouts rootVal' (paths[j]'hk₀_p) := by
        rw [hpath₀]
        exact hp_0 hnew_len hvpath_0_app (.single [.scalar sc₀', .scalar sc₁'] 0 mid₀ (.scalar sc₀') rfl)
      have hrpv_0' : readProjectedValue [] rootVal' (paths[j]'hk₀_p) = .ok (.scalar sc₀') := by
        rw [hpath₀, hr_0]; rfl
      exact ⟨hp_ne_0, hfl_0, hprim_0, hv_0, sc₀', msc₀', hrpv_0',
        hrel₀', hsz₀', hbool₀', hchar₀', hinit_0', hread_0'⟩
    · by_cases hj1 : j = k₁
      · subst hj1
        obtain ⟨hr_1, hp_1⟩ := happend_spec [.field 1 mid₁]
        have hv_1 : ValidAggregateFieldPath layouts rootVal' (paths[j]'hk₁_p) := by
          rw [hpath₁]
          exact hp_1 hnew_len hvpath_1_app (.single [.scalar sc₀', .scalar sc₁'] 1 mid₁ (.scalar sc₁') rfl)
        have hrpv_1' : readProjectedValue [] rootVal' (paths[j]'hk₁_p) = .ok (.scalar sc₁') := by
          rw [hpath₁, hr_1]; rfl
        exact ⟨hp_ne_1, hfl_1, hprim_1, hv_1, sc₁', msc₁', hrpv_1',
          hrel₁', hsz₁', hbool₁', hchar₁', hinit_1', hread_1'⟩
      · obtain ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j, sc_j, msc_j, hrpv_j, hrel_j,
          hsz_j, hbool_j, hchar_j, _, hread_j⟩ := hfields j hj
        dsimp at hp_ne_j hfl_j hprim_j hvpath_j hrpv_j hsz_j hbool_j hchar_j hread_j ⊢
        have hpos_j : 0 < (fields[j]'hj).fieldLayout.size.bytes.toNat := by
          rw [hsz_j]; exact translateSizeBytes_pos hrel_j.validBytes
        obtain ⟨hinit_j', hread_j_eq⟩ := hother' j hj hj0 hj1 hpos_j (hbits j hj)
        have hj_p : j < paths.length := by rw [hplen]; exact hj
        obtain ⟨hrpv_j_eq, hvpath_j'⟩ := hdisj_spec (paths[j]'hj_p)
          (hdisj_paths j hj_p hj0 hj1)
        exact ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j' hvpath_j, sc_j, msc_j,
          (hrpv_j_eq []).trans hrpv_j, hrel_j, hsz_j, hbool_j, hchar_j,
          hinit_j', hread_j_eq.trans hread_j⟩
  · intro p hp
    exact (hpad' p hp).trans (hpad p hp)

/-- Syntactic well-typedness of a non-empty `ProjectionElem.Field` chain
`projs` projecting from local `idx` (`decl.ty`) to a 2-scalar `ScalarPair`
sub-struct `subTy` at byte offset `subOff`, backed by leaves `k₀` and `k₁`
at `projs ++ [.field 0 mid₀]` and `projs ++ [.field 1 mid₁]`. -/
inductive WellTypedLM2_2ProjectedSubStructRead
    (body : CapturedMir) (env : StructTypeEnv)
    (idx : Local) (projs : List ProjectionElem)
    (subTy : Ty) (sf₀ sf₁ : StructFieldDesc) (mid₀ mid₁ : Ty) : Prop where
  | mk (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k₀ k₁ : Nat)
      (hk₀_f : k₀ < fields.length) (hk₁_f : k₁ < fields.length)
      (hk₀_p : k₀ < paths.length) (hk₁_p : k₁ < paths.length)
      (subOff bOff : Miri.ABI.Size)
      (a b : Miri.ABI.Scalar) :
      get? body.localDecls idx = some decl →
      env decl.ty = some (fields, paths) →
      env subTy = some ([sf₀, sf₁], [[.field 0 mid₀], [.field 1 mid₁]]) →
      k₀ ≠ k₁ →
      paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀] →
      paths[k₁]'hk₁_p = projs ++ [.field 1 mid₁] →
      (fields[k₀]'hk₀_f).ty = mid₀ →
      (fields[k₁]'hk₁_f).ty = mid₁ →
      (fields[k₀]'hk₀_f).offset = subOff →
      (fields[k₁]'hk₁_f).offset = Miri.ABI.Size.ofBytes (subOff.bytes + bOff.bytes) →
      (fields[k₀]'hk₀_f).fieldLayout = sf₀.fieldLayout →
      0 < sf₀.fieldLayout.size.bytes.toNat →
      sf₀.ty = mid₀ →
      sf₁.ty = mid₁ →
      sf₀.offset = Miri.ABI.Size.ZERO →
      sf₁.offset = bOff →
      sf₀.fieldLayout = (translateTy mid₀ body.layouts).layout →
      sf₁.fieldLayout = (translateTy mid₁ body.layouts).layout →
      ValidStructLayout (translateTy subTy body.layouts).layout [sf₀, sf₁] →
      (translateTy subTy body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      (translateTy subTy body.layouts).layout.size.bytes.toNat < 2 ^ 32 →
      ((∃ ts, subTy.kind = .tuple ts) ∨ (∃ p adtArgs, subTy.kind = .adt p adtArgs)) →
      (∀ t₁, subTy.kind = .tuple [t₁, .bool] → mid₁.kind = .bool) →
      (translateTy subTy body.layouts).layout.backendRepr =
        .ScalarPair (a := a) (b := b) (bOffset := bOff) →
      a.size annealRuntimeDataLayout = .ok sf₀.fieldLayout.size →
      b.size annealRuntimeDataLayout = .ok sf₁.fieldLayout.size →
      (translateTy subTy body.layouts).layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO →
      (translateTy subTy body.layouts).layout.fields.offset 1 = .ok bOff →
      IsRoundtripTy mid₀ →
      IsRoundtripTy mid₁ →
      IsPrimScalarTy mid₀ →
      IsPrimScalarTy mid₁ →
      ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts)
        projs subTy subOff →
      WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁

/-- Simulation relation for reading a whole projected 2-scalar `ScalarPair`
sub-struct via `.copy ⟨idx, projs⟩` or `.move ⟨idx, projs⟩`. -/
inductive ProjectedSubStructReadSimRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState)
    (subTy : Ty) (sf₀ sf₁ : StructFieldDesc) (mid₀ mid₁ : Ty) :
    OperandEvalResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  | ok (sc₀ sc₁ : MirAst.ScalarInt) (msc₀ msc₁ : Miri.Memory.ScalarInt)
      (outLay : Miri.Interpreter.LocalLayout)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
      FrameRelLM2_2 body env m.machine af topFrame' →
      ImmediateStructRel subTy body.layouts [sf₀, sf₁]
        [[.field 0 mid₀], [.field 1 mid₁]]
        (.aggregate 0 [.scalar sc₀, .scalar sc₁])
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)) →
      ImmediateRel subTy body.layouts
        (.aggregate 0 [.scalar sc₀, .scalar sc₁])
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)) →
      topFrame'.localsIdentity = topFrame.localsIdentity →
      topFrame'.returnContinuation = topFrame.returnContinuation →
      topFrame'.returnPlace = topFrame.returnPlace →
      (∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value) →
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') →
      ProjectedSubStructReadSimRelLM2_2 body env af topFrame m subTy sf₀ sf₁ mid₀ mid₁
        (.ok (.aggregate 0 [.scalar sc₀, .scalar sc₁]) af.locals)
        (.ok ⟨.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁), outLay⟩
          { m with stack := ⟨#[topFrame']⟩ })
  | ub (msg : String) (m' : AnnealStepState) :
      ProjectedSubStructReadSimRelLM2_2 body env af topFrame m subTy sf₀ sf₁ mid₀ mid₁
        .ub (.error (.undefinedBehavior msg) m')

/-- Per-local core lemma for reading a projected 2-scalar `ScalarPair` sub-struct. -/
theorem evalProjection_nested_substruct_read_at_local
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local} {decl : LocalDecl}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ sf₁ : StructFieldDesc} {mid₀ mid₁ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < topFrame.locals.size)
    (hslot : get? af.locals idx = some slot)
    (hmls_eq : topFrame.locals[idx]'hlt_mf = mls)
    (hloc : LocalRelLM2_2 env m.machine decl body.layouts slot mls)
    (hwt : WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ sc₀ sc₁ msc₀ msc₁ outLay,
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil =
        .ok (.aggregate 0 [.scalar sc₀, .scalar sc₁]) af.locals ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁), outLay⟩
          { m with
            stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt_mf
              (translateTy decl.ty body.layouts)]⟩ } ∧
      ImmediateStructRel subTy body.layouts [sf₀, sf₁]
        [[.field 0 mid₀], [.field 1 mid₁]]
        (.aggregate 0 [.scalar sc₀, .scalar sc₁])
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)) ∧
      ImmediateRel subTy body.layouts
        (.aggregate 0 [.scalar sc₀, .scalar sc₁])
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))) ∨
    (∃ msg m',
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil = .ub ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') := by
  cases hwt with
  | mk decl' fields paths k₀ k₁ hk₀_f hk₁_f hk₀_p hk₁_p subOff bOff a b
      hdecl' henv _ hne_k hpath₀ hpath₁ hty₀ hty₁ hoff_k₀ hoff_k₁ hfl_k₀ hpos_sf₀
      hsf₀_ty hsf₁_ty hsf₀_off hsf₁_off hsf₀_fl hsf₁_fl
      hvalid_sub hnz_sub hsz4g_sub hagg_sub hbool_sub hrepr_sub hszA hszB
      hoff0_sub hoff1_sub hrt₀ hrt₁ hprim₀ hprim₁ hchain =>
    have hdecl_eq : decl' = decl := Option.some.inj (hdecl'.symm.trans hdecl)
    cases hdecl_eq
    have hcache := hloc.layout_eq
    let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
    have hp_ne : projs ≠ [] := hchain.ne_nil
    obtain ⟨p0, ps, hp_cons⟩ : ∃ p0 ps, projs = p0 :: ps := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons p0 ps => exact ⟨p0, ps, rfl⟩
    subst hp_cons
    have hp0_nd : p0 ≠ .deref := hchain.not_deref_head
    have htr_op :
        translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩) =
          (if isMove then .Move ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩
           else .Copy ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩) := by
      cases isMove <;> rfl
    have ha_proj :
        evalOperand af.locals (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)
            .nil globals body.layouts .nil =
          match get? af.locals idx with
          | some (.init rootVal) =>
              match readProjectedValue af.locals rootVal (p0 :: ps) with
              | .ok fieldVal => .ok fieldVal af.locals
              | .ub => .ub
              | .unsupported => .unsupported
          | _ => .ub := by
      cases isMove <;> cases p0 <;> (try exact False.elim (hp0_nd rfl)) <;>
        (simp only [mkPlaceOperand, Bool.false_eq_true, ↓reduceIte]
         unfold evalOperand; dsimp only; cases get? af.locals idx with
          | none => rfl
          | some sl => cases sl <;> rfl)
    cases hloc with
    | base _ _ henv_none _ =>
      rw [henv] at henv_none; cases henv_none
    | structDead _ _ c _ _ =>
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        exact EStateM.bind_apply_error
          (annealEvalOperand_projected_dead hframes hlt_mf hdecl hmls_eq hcache)
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitImm _ _ c _ _ =>
      have heval_p := annealEvalProjection_uninit_of_validFieldProjChain hchain
        { m with stack := ⟨#[topFrame']⟩ }
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p),
            annealReadImmediate_uninit]
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitInd f' p' mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, hvalid_outer, hprov, hmis, _, hlive,
        hbase, hptr, hovf, _, _, _, _, _, hmask_uninit⟩
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hbnd_k0 := hvalid_outer.fields_in_bounds k₀ hk₀_f
      rw [hoff_k₀, hfl_k₀] at hbnd_k0
      have hlt_u64 := (translateTy decl.ty body.layouts).layout.size.bytes.toNat_lt
      have hend := lm22_allocRange_end (start := subOff) (sz := sf₀.fieldLayout.size) (by omega)
      have hle_end : (Miri.ABI.Size.ofBytes (subOff.bytes + sf₀.fieldLayout.size.bytes)).bytes ≤
          (translateTy decl.ty body.layouts).layout.size.bytes := by
        rw [UInt64.le_iff_toNat_le]
        dsimp [Miri.ABI.Size.ofBytes]
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)]
        exact hbnd_k0
      have huninit_q : localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange subOff sf₀.fieldLayout.size) =
          .ok (.error (Miri.Memory.allocRange subOff sf₀.fieldLayout.size)) := by
        rw [hmask_uninit]
        exact Miri.Memory.InitMask.lazy_uninitialized_query
          (translateTy decl.ty body.layouts).layout.size _ _ hend hle_end
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + subOff.bytes) := by
        rw [hptr]; rfl
      have hnot_array : ∀ s c, (translateTy subTy body.layouts).layout.fields ≠ Miri.ABI.FieldsShape.Array s c := by intro s c heq; rcases hvalid_sub.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all
      have hread_ub := annealReadIndirectImmediate_scalarPair_uninit_ub
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (lay := translateTy subTy body.layouts)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hnz_sub hnot_array hrepr_sub hszA hprov hbase hptr_proj hlive.1 huninit_q
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized scalarPair field 0")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ub
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structImm f' p' v imm c henv' _ himm =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      cases himm with
      | scalarWrapper =>
        simp at hk₀_f hk₁_f
        omega
      | scalarPair _ _ m₀ m₁ z₀ z₁ =>
        simp at hk₀_f hk₁_f
        have hk01 : (k₀ = 0 ∧ k₁ = 1) ∨ (k₀ = 1 ∧ k₁ = 0) := by omega
        rcases hk01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · dsimp [List.append] at hpath₀ hpath₁
          injection hpath₀ with hh0 _
          injection hpath₁ with hh1 _
          rw [← hh0] at hh1
          cases hh1
        · dsimp [List.append] at hpath₀ hpath₁
          injection hpath₀ with hh0 _
          injection hpath₁ with hh1 _
          rw [← hh0] at hh1
          cases hh1
    | structInd f' p' v mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, words, _, _, _, _,
        hprov, _, _, hlive, hbase, hptr, hovf, _, _, _, _, _, _, _, hfields_rel, _⟩
      obtain ⟨_, _, _, hvpath_0, sc₀, msc₀, hrpv_0, hrel_0, hsz_0, hbool_0, hchar_0, _, hread_0⟩ :=
        hfields_rel k₀ hk₀_f
      obtain ⟨_, _, _, hvpath_1, sc₁, msc₁, hrpv_1, hrel_1, hsz_1, hbool_1, hchar_1, _, hread_1⟩ :=
        hfields_rel k₁ hk₁_f
      rw [hpath₀] at hvpath_0 hrpv_0
      rw [hpath₁] at hvpath_1 hrpv_1
      obtain ⟨subIdx, hlast_p⟩ := hchain.last_eq
      obtain ⟨_, hrpv_sub⟩ :=
        ValidAggregateFieldPath.read_substruct_scalarPair (by nofun) hlast_p hrepr_sub
          hvpath_0 hrpv_0 hvpath_1 hrpv_1
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + subOff.bytes) := by
        rw [hptr]; rfl
      have hfl_k₁ : (fields[k₁]'hk₁_f).fieldLayout = sf₁.fieldLayout := by
        have h1 := (hfields_rel k₁ hk₁_f).2.1
        rw [h1, hty₁, ← hsf₁_fl]
      have hread_0' : localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange subOff sf₀.fieldLayout.size) false =
          .ok (Miri.Memory.Scalar.fromScalarInt msc₀) := by
        rwa [← hoff_k₀, ← hfl_k₀]
      have hread_1' : localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (subOff.bytes + bOff.bytes)) sf₁.fieldLayout.size) false =
          .ok (Miri.Memory.Scalar.fromScalarInt msc₁) := by
        rwa [← hoff_k₁, ← hfl_k₁]
      have hnot_array : ∀ s c, (translateTy subTy body.layouts).layout.fields ≠ Miri.ABI.FieldsShape.Array s c := by intro s c heq; rcases hvalid_sub.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all
      have hread_ok := annealReadIndirectImmediate_scalarPair_ok
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (lay := translateTy subTy body.layouts)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hnz_sub hnot_array hrepr_sub hszA hszB hprov hbase hptr_proj hlive.1 hread_0' hread_1'
      have himm_sub : ImmediateStructRel subTy body.layouts [sf₀, sf₁]
          [[.field 0 mid₀], [.field 1 mid₁]]
          (.aggregate 0 [.scalar sc₀, .scalar sc₁])
          (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)) := by
        refine .scalarPair sf₀ sf₁ mid₀ mid₁ [] [] a b bOff sc₀ sc₁ msc₀ msc₁
          (.scalar sc₀) (.scalar sc₁)
          hvalid_sub hsz4g_sub hagg_sub
          (fun t₁ ht => by rw [hsf₁_ty]; exact hbool_sub t₁ ht)
          hrepr_sub hszA hszB hoff0_sub hoff1_sub hsf₀_off hsf₁_off
          (by rw [hsf₀_ty]; exact hsf₀_fl) (by rw [hsf₁_ty]; exact hsf₁_fl)
          hrt₀ hrt₁
          (by rw [hsf₀_ty]; exact hprim₀) (by rw [hsf₁_ty]; exact hprim₁)
          (Or.inl ⟨rfl, hsf₀_ty.symm⟩) (Or.inl ⟨rfl, hsf₁_ty.symm⟩)
          .bare .bare hrel_0 hrel_1
          (by rw [← hfl_k₀]; exact hsz_0) (by rw [← hfl_k₁]; exact hsz_1)
          (by rw [hsf₀_ty, ← hty₀]; exact hbool_0)
          (by rw [hsf₀_ty, ← hty₀]; exact hchar_0)
          (by rw [hsf₁_ty, ← hty₁]; exact hbool_1)
          (by rw [hsf₁_ty, ← hty₁]; exact hchar_1)
      refine Or.inl ⟨sc₀, sc₁, msc₀, msc₁, translateTy subTy body.layouts, ?_, ?_,
        himm_sub, himm_sub.toImmediateRel_of_flat⟩
      · rw [ha_proj, hslot]; dsimp only; rw [hrpv_sub af.locals]
      · rw [htr_op]; dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ok

/-- Reading a projected 2-scalar `ScalarPair` sub-struct (e.g. `_3 = copy _2.1`
with `_2.1 : InnerPair`) simulates `annealEvalOperand >>= annealReadImmediate`
across dead locals (UB), uninitialized immediate/indirect locals (UB), and
memory-backed aggregates (`StructMemPlaceRel`). -/
theorem evalOperand_nested_substruct_read_simulation
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ sf₁ : StructFieldDesc} {mid₀ mid₁ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedSubStructReadSimRelLM2_2 body env af topFrame m subTy sf₀ sf₁ mid₀ mid₁
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m) := by
  have hdecl_ex : ∃ decl, get? body.localDecls idx = some decl := by
    cases hwt with
    | mk decl _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨decl, hd⟩
  obtain ⟨decl, hdecl⟩ := hdecl_ex
  obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
  have hfr' := hframe.cache_local_layout hdecl hlt_mf
  have hval_eq :
      ∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    by_cases hk : k = idx
    · subst hk
      dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_mf, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
  rcases evalProjection_nested_substruct_read_at_local hframes hdecl hlt_mf hslot hmls_eq
      hloc hwt globals known with
    ⟨sc₀, sc₁, msc₀, msc₁, outLay, ha_ok, hm_ok, himm_s, himm_r⟩ | ⟨msg, m', ha_ub, hm_ub⟩
  · rw [ha_ok, hm_ok]
    exact .ok sc₀ sc₁ msc₀ msc₁ outLay topFrame' hfr' himm_s himm_r rfl rfl rfl hval_eq
      (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
  · rw [ha_ub, hm_ub]
    exact .ub msg m'

theorem copyWholeStructAllocation_props
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (extra : Option Miri.TreeBorrows.BorrowTree) :
    let alloc' := copyWholeStructAllocation alloc extra
    alloc'.mutability = .Mut ∧
    alloc'.byteSize = alloc.byteSize ∧
    alloc'.len = alloc.len ∧
    alloc'.provenanceMap = alloc.provenanceMap ∧
    alloc'.initializationMask = alloc.initializationMask ∧
    (∀ dl r rp, alloc'.readScalar dl r rp = alloc.readScalar dl r rp) := by
  cases alloc
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem StructMemPlaceRel.of_copy_fresh
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value}
    {srcLocal : AnnealLocalAlloc} {words : Array UInt64}
    (hvalid : ValidStructLayout (translateTy ty layouts).layout fields)
    (hplen : paths.length = fields.length)
    (hagg : (∃ hd tl, rootVal = .aggregate 0 (hd :: tl)) ∧ NoZeroByteLeaves rootVal)
    (hleaf : valueLeafBytes rootVal = structSumFieldBytes fields)
    (hbs : srcLocal.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : srcLocal.allocation.len = srcLocal.allocation.byteSize.bytes.toNat)
    (hpmap : srcLocal.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel srcLocal.allocation.initializationMask
      srcLocal.allocation.byteSize words)
    (hbits : ∀ i (hi : i < fields.length) b,
      (fields[i]'hi).offset.bytes.toNat ≤ b →
      b < (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat →
      maskBlocksGetBit words b = true)
    (hfields : ∀ (i : Nat) (hi : i < fields.length),
      let f := fields[i]'hi
      let path := paths[i]'(by rw [hplen]; exact hi)
      path ≠ [] ∧
      f.fieldLayout = (translateTy f.ty layouts).layout ∧
      IsPrimScalarTy f.ty ∧
      ValidAggregateFieldPath layouts rootVal path ∧
      ∃ sc msc,
        readProjectedValue [] rootVal path = .ok (.scalar sc) ∧
        ScalarRel sc msc ∧
        f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
        (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
        (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
        srcLocal.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
        srcLocal.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) false = .ok (.fromScalarInt msc))
    (hpad : ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      srcLocal.allocation.initializationMask.get
        (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false)
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hovf : (annealStackBaseAddr id).toNat +
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : (translateTy ty layouts).layout.align.abi.pow2 ≤ 29) :
    StructMemPlaceRel
      (stackAllocMachine mach mem' id (copyWholeStructAllocation srcLocal.allocation none))
      ty layouts fields paths rootVal (stackAllocPlace id) := by
  let alloc' := copyWholeStructAllocation srcLocal.allocation none
  obtain ⟨hmut', hbs', hlen', hpmap', hmask_eq, hread_eq⟩ :=
    copyWholeStructAllocation_props srcLocal.allocation none
  refine .mk id Miri.Memory.BorTag.one (annealStackBaseAddr id) ⟨.stack, alloc'⟩ words hvalid hplen
    hagg hleaf rfl rfl rfl
    (LiveAllocEntry.of_push_fresh_self _ hfresh)
    (lookupBaseAddr_stackAllocMachine_self _ _ _ _)
    rfl hovf hmut'
    (annealStackBaseAddr_isAligned id _ halign)
    (hbs'.trans hbs) (by rw [hlen', hbs']; exact hlen)
    (hpmap'.trans hpmap) (by rw [hmask_eq, hbs']; exact hmask) hbits ?_ ?_
  · intro i hi
    obtain ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
        hbool_i, hchar_i, hinit_i, hread_i⟩ := hfields i hi
    exact ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
      hbool_i, hchar_i, by dsimp; rw [hmask_eq]; exact hinit_i,
      by dsimp; rw [hread_eq]; exact hread_i⟩
  · intro p hp
    dsimp; rw [hmask_eq]; exact hpad p hp

theorem StructMemPlaceRel.of_copy_overwrite
    {mach : AnnealMachine} {u : Nat}
    {destId : Miri.Memory.AllocId} {destBase : UInt64}
    {destLocal : AnnealLocalAlloc}
    {destMp : Miri.Interpreter.MemPlace AnnealProv}
    {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value}
    {srcLocal : AnnealLocalAlloc} {words : Array UInt64}
    (hvalid : ValidStructLayout (translateTy ty layouts).layout fields)
    (hplen : paths.length = fields.length)
    (hagg : (∃ hd tl, rootVal = .aggregate 0 (hd :: tl)) ∧ NoZeroByteLeaves rootVal)
    (hleaf : valueLeafBytes rootVal = structSumFieldBytes fields)
    (hbs : srcLocal.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : srcLocal.allocation.len = srcLocal.allocation.byteSize.bytes.toNat)
    (hpmap : srcLocal.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel srcLocal.allocation.initializationMask
      srcLocal.allocation.byteSize words)
    (hbits : ∀ i (hi : i < fields.length) b,
      (fields[i]'hi).offset.bytes.toNat ≤ b →
      b < (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat →
      maskBlocksGetBit words b = true)
    (hfields : ∀ (i : Nat) (hi : i < fields.length),
      let f := fields[i]'hi
      let path := paths[i]'(by rw [hplen]; exact hi)
      path ≠ [] ∧
      f.fieldLayout = (translateTy f.ty layouts).layout ∧
      IsPrimScalarTy f.ty ∧
      ValidAggregateFieldPath layouts rootVal path ∧
      ∃ sc msc,
        readProjectedValue [] rootVal path = .ok (.scalar sc) ∧
        ScalarRel sc msc ∧
        f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
        (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
        (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
        srcLocal.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
        srcLocal.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) false = .ok (.fromScalarInt msc))
    (hpad : ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      srcLocal.allocation.initializationMask.get
        (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hmis_d : destMp.misaligned = none)
    (hmeta_d : destMp.metadata = .none)
    (hlive_d : LiveAllocEntry mach.memory.live destId destLocal)
    (hu_lt : u < mach.memory.live.size)
    (hfidx_d : mach.memory.live.findIdx? (fun (k, _) => k == destId) = some u)
    (hbase_d : mach.lookupBaseAddr destId = some destBase)
    (hptr_d : destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase)
    (hovf_d : destBase.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign_d : destMp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true) :
    StructMemPlaceRel
      (updateAllocMachine mach u destId destLocal.kind
        (copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra))
      ty layouts fields paths rootVal destMp := by
  let alloc' := copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra
  obtain ⟨hmut', hbs', hlen', hpmap', hmask_eq, hread_eq⟩ :=
    copyWholeStructAllocation_props srcLocal.allocation destLocal.allocation.extra
  have hlive_self : LiveAllocEntry (mach.memory.live.set! u (destId, ⟨destLocal.kind, alloc'⟩))
      destId ⟨destLocal.kind, alloc'⟩ :=
    hlive_d.of_set!_self hu_lt hfidx_d ⟨destLocal.kind, alloc'⟩
  refine .mk destId tag_d destBase ⟨destLocal.kind, alloc'⟩ words hvalid hplen
    hagg hleaf hprov_d hmis_d hmeta_d hlive_self hbase_d hptr_d hovf_d
    hmut' halign_d (hbs'.trans hbs) (by rw [hlen', hbs']; exact hlen)
    (hpmap'.trans hpmap) (by rw [hmask_eq, hbs']; exact hmask) hbits ?_ ?_
  · intro i hi
    obtain ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
        hbool_i, hchar_i, hinit_i, hread_i⟩ := hfields i hi
    exact ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
      hbool_i, hchar_i, by dsimp; rw [hmask_eq]; exact hinit_i,
      by dsimp; rw [hread_eq]; exact hread_i⟩
  · intro p hp
    dsimp; rw [hmask_eq]; exact hpad p hp

theorem annealStructMemCopyOp_dead_ub
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hdead : tf.locals[dstIdx]'hlt = ⟨.dead, c⟩) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  have hfa := forceAllocation_dead_err (ld := ld) (ly := ly)
    (offOpt := none) (iden := iden) (lay := wholeLay) hframes hlt hdead
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa]

theorem annealStructMemCopyOp_uninitImm_ok
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
    {mem' : AnnealMemory} {id srcId : Miri.Memory.AllocId}
    {srcBase : UInt64} {srcLocal : AnnealLocalAlloc}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (himm : tf.locals[dstIdx]'hlt = ⟨.live (.immediate .uninit), some wholeLay⟩)
    (hsized : wholeLay.layout.isSized = true)
    (htry : Miri.Memory.Allocation.tryNew wholeLay.layout.size wholeLay.layout.align.abi .Uninit
      annealZeroedStorage = .ok rawAlloc)
    (hbs0 : (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).byteSize = wholeLay.layout.size)
    (hmut0 : (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).mutability = .Mut)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hptr_s : srcMp.ptr.offset = Miri.ABI.Size.ofBytes srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    (hbs_s : srcLocal.allocation.byteSize = wholeLay.layout.size) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .ok ()
        ⟨⟨#[{ tf with
              locals := tf.locals.set dstIdx
                ⟨.live (.indirect (stackAllocPlace id)), some wholeLay⟩ hlt }]⟩,
          stackAllocMachine m.machine mem' id
            (copyWholeStructAllocation srcLocal.allocation none)⟩ := by
  obtain ⟨hlive_eq, _⟩ := reserveAllocId_ok_live hres
  obtain ⟨_, _, hbase_all⟩ := stackAllocMachine_live_base (rawAlloc.withExtra none) hres
  have hmem_s := hlive_s.mem_toList
  have hne_id : (srcId == id) = false := by
    apply beq_false_of_ne
    intro heq; subst heq
    rw [hlive_eq] at hfresh
    rw [hlive_s.any_true] at hfresh
    cases hfresh
  have hfa := forceAllocation_uninit_none_ok (ld := ld) (ly := ly)
    (iden := iden) hframes hlt himm hsized htry hres
  have hfind_s :
      (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).memory.live.find?
        (fun (k, _) => k == srcId) = some (srcId, srcLocal) := by
    dsimp [stackAllocMachine]; rw [hlive_eq]
    exact (hlive_s.of_push_other (id, ⟨.stack, rawAlloc.withExtra none⟩)).1
  have hbase_s' :
      (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).lookupBaseAddr srcId =
        some srcBase :=
    (hbase_all srcId srcLocal hmem_s).trans hbase_s
  have hbase_d :
      (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).lookupBaseAddr id =
        some (annealStackBaseAddr id) :=
    lookupBaseAddr_stackAllocMachine_self m.machine mem' id (rawAlloc.withExtra none)
  have hfidx_d :
      (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).memory.live.findIdx?
        (fun (k, _) => k == id) = some mem'.live.size :=
    findIdx?_push_fresh mem'.live id ⟨.stack, rawAlloc.withExtra none⟩ hfresh
  have hlt_push :
      mem'.live.size < (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).memory.live.size := by
    simp [stackAllocMachine]
  have hget_d :
      (stackAllocMachine m.machine mem' id (rawAlloc.withExtra none)).memory.live[mem'.live.size]? =
        some (id, ⟨.stack, rawAlloc.withExtra none⟩) := by
    rw [Array.getElem?_eq_getElem hlt_push]
    simp [stackAllocMachine]
  have hsub_s : Miri.ABI.Size.ofBytes (srcMp.ptr.offset.bytes - srcBase) = Miri.ABI.Size.ZERO := by
    rw [hptr_s]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hsub_d :
      Miri.ABI.Size.ofBytes ((stackAllocPlace id).ptr.offset.bytes - annealStackBaseAddr id) =
        Miri.ABI.Size.ZERO := by
    dsimp [stackAllocPlace, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hcopy_cond :
      isWholeStructAllocationCopy srcLocal.allocation (rawAlloc.withExtra none)
        Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO wholeLay.layout.size (srcId == id) = true := by
    unfold isWholeStructAllocationCopy
    rw [hne_id, hbs_s, hbs0, hmut0]
    simp [Miri.ABI.Size.ZERO]
  have hextra0 : (rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).extra = none := by
    cases rawAlloc; rfl
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, hprov_s, Option.bind,
    Miri.Memory.Provenance.getAllocId, hbase_s', hfind_s,
    show (stackAllocPlace id).ptr.provenance = some (.concrete id Miri.Memory.BorTag.one) from rfl,
    hbase_d, hfidx_d, hget_d, hsub_s, hsub_d, hcopy_cond, ↓reduceIte, hextra0]
  dsimp only [stackAllocMachine]
  rw [array_push_set!_size]
  rfl

theorem annealStructMemCopyOp_indirect_ok
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId destId : Miri.Memory.AllocId}
    {srcBase destBase : UInt64}
    {srcLocal destLocal : AnnealLocalAlloc}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    (hne_id : srcId ≠ destId)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hptr_s : srcMp.ptr.offset = Miri.ABI.Size.ofBytes srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    (hbs_s : srcLocal.allocation.byteSize = wholeLay.layout.size)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hbase_d : m.machine.lookupBaseAddr destId = some destBase)
    (hptr_d : destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx_d : m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some u)
    (hget_d : m.machine.memory.live[u]'hu_lt = (destId, destLocal))
    (hbs_d : destLocal.allocation.byteSize = wholeLay.layout.size)
    (hmut_d : destLocal.allocation.mutability = .Mut) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .ok ()
        { m with
          machine := updateAllocMachine m.machine u destId destLocal.kind
            (copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra) } := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  have hne_beq : (srcId == destId) = false := beq_false_of_ne hne_id
  have hget_d? : m.machine.memory.live[u]? = some (destId, ⟨destLocal.kind, destLocal.allocation⟩) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget_d]
  have hsub_s : Miri.ABI.Size.ofBytes (srcMp.ptr.offset.bytes - srcBase) = Miri.ABI.Size.ZERO := by
    rw [hptr_s]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hsub_d : Miri.ABI.Size.ofBytes (destMp.ptr.offset.bytes - destBase) = Miri.ABI.Size.ZERO := by
    rw [hptr_d]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hcopy_cond :
      isWholeStructAllocationCopy srcLocal.allocation destLocal.allocation
        Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO wholeLay.layout.size (srcId == destId) = true := by
    unfold isWholeStructAllocationCopy
    rw [hne_beq, hbs_s, hbs_d, hmut_d]
    simp [Miri.ABI.Size.ZERO]
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, hprov_s, hprov_d, Option.bind,
    Miri.Memory.Provenance.getAllocId, hbase_s, hlive_s.1, hbase_d, hfidx_d,
    hget_d?, hsub_s, hsub_d, hcopy_cond, ↓reduceIte]
  rfl

/-- Copying into a read-only (`Mutability.Not`) indirect destination allocation
always bypasses `isWholeStructAllocationCopy` (even when `srcLocal` is also
`Mutability.Not`) and raises `StepError.undefinedBehavior` via
`Miri.Memory.Allocation.copy` / `annealStructMemCopyError`. -/
theorem annealStructMemCopyOp_readOnly_ub
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId destId : Miri.Memory.AllocId}
    {srcBase destBase : UInt64}
    {srcLocal destLocal : AnnealLocalAlloc}
    {destAlloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hptr_s : srcMp.ptr.offset = Miri.ABI.Size.ofBytes srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hbase_d : m.machine.lookupBaseAddr destId = some destBase)
    (hptr_d : destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx_d : m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some u)
    (hget_d : m.machine.memory.live[u]'hu_lt = (destId, destLocal))
    (hmut_d : destLocal.allocation.mutability = .Not)
    (hcopy_err : Miri.Memory.Allocation.copy srcLocal.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO wholeLay.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (srcId == destId) true
        destLocal.allocation = .error .readOnlyAllocation destAlloc') :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "write to read-only allocation") m := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  have hget_d? : m.machine.memory.live[u]? = some (destId, ⟨destLocal.kind, destLocal.allocation⟩) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget_d]
  have hsub_s : Miri.ABI.Size.ofBytes (srcMp.ptr.offset.bytes - srcBase) = Miri.ABI.Size.ZERO := by
    rw [hptr_s]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hsub_d : Miri.ABI.Size.ofBytes (destMp.ptr.offset.bytes - destBase) = Miri.ABI.Size.ZERO := by
    rw [hptr_d]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hcopy_cond :
      isWholeStructAllocationCopy srcLocal.allocation destLocal.allocation
        Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO wholeLay.layout.size (srcId == destId) = false := by
    unfold isWholeStructAllocationCopy
    rw [hmut_d]
    simp
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    hprov_s, hprov_d, Option.bind,
    Miri.Memory.Provenance.getAllocId, hbase_s, hlive_s.1, hbase_d, hfidx_d,
    hget_d?, hsub_s, hsub_d, hcopy_cond, Bool.false_eq_true, ↓reduceIte,
    hcopy_err, annealStructMemCopyError]

/-- Copying from a freed/dangling source `AllocId` (`memory.live.find? = none`)
in `annealStructMemCopyOp` raises `StepError.undefinedBehavior` (`DanglingPointer`
UB, matching `annealReadIndirectImmediate`). -/
theorem annealStructMemCopyOp_dangling_src_ub
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId : Miri.Memory.AllocId}
    {srcBase : UInt64}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hdead_s : m.machine.memory.live.find? (fun (k, _) => k == srcId) = none) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "dangling allocation in memory copy") m := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    hprov_s, Option.bind, Miri.Memory.Provenance.getAllocId, hbase_s, hdead_s]

/-- Copying into a freed/dangling destination `AllocId` (`memory.live.findIdx? = none`)
in `annealStructMemCopyOp` raises `StepError.undefinedBehavior`. -/
theorem annealStructMemCopyOp_dangling_dest_ub
    {ld : List LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId destId : Miri.Memory.AllocId}
    {srcBase destBase : UInt64}
    {srcLocal : AnnealLocalAlloc}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hbase_d : m.machine.lookupBaseAddr destId = some destBase)
    (hdead_d : m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = none) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "dangling allocation in memory copy") m := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    hprov_s, hprov_d, Option.bind, Miri.Memory.Provenance.getAllocId,
    hbase_s, hlive_s.1, hbase_d, hdead_d]

/-- Self-copy (`srcId = destId`, `sameAllocation = true`) on an indirect `.Memory`
struct allocation bypasses `isWholeStructAllocationCopy` and raises
`StepError.undefinedBehavior "whole-value copy between overlapping ranges"`
when `Miri.Memory.Allocation.copy` (`nonoverlapping = true`) reports
`AllocError.copyRangesOverlap`. -/
theorem annealStructMemCopyOp_overlap_ub
    {ld : List LocalDecl} {ly : LayoutTable}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : idx < tf.locals.size)
    (hind : tf.locals[idx]'hlt = ⟨.live (.indirect mp), c⟩)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hcopy_err : Miri.Memory.Allocation.copy localAlloc.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO wholeLay.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        localAlloc.allocation = .error .copyRangesOverlap alloc') :
    annealStructMemCopyOp ld ly ⟨.indirect mp, srcLay⟩
        ⟨.local 0 idx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "whole-value copy between overlapping ranges") m := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  have hget? : m.machine.memory.live[u]? = some (allocId, ⟨localAlloc.kind, localAlloc.allocation⟩) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget]
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]; rw [UInt64.sub_self]
  have hsame : (allocId == allocId) = true := beq_self_eq_true allocId
  have hcopy_cond :
      isWholeStructAllocationCopy localAlloc.allocation localAlloc.allocation
        Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO wholeLay.layout.size true = false := by
    simp [isWholeStructAllocationCopy]
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw,
    hprov, Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hlive.1, hfidx,
    hget?, hsub, hsame, hcopy_cond, Bool.false_eq_true, ↓reduceIte,
    hcopy_err, annealStructMemCopyError]
  rfl

theorem StructMemPlaceRel.write_substruct_scalarWrap
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {k₀ : Nat} (hk₀ : k₀ < fields.length) (hk₀_p : k₀ < paths.length)
    {projs : List ProjectionElem} {subIdx : Nat} {subTy mid₀ : Ty}
    {a : Miri.ABI.Scalar}
    (hprojs_ne : projs ≠ [])
    (hlast : projs.getLast? = some (.field subIdx subTy))
    (hrepr : (translateTy subTy layouts).layout.backendRepr = .Scalar a)
    (hpath₀ : paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀])
    (hdisj_paths : ∀ j (hj_p : j < paths.length), j ≠ k₀ →
      DisjointFieldPaths projs (paths[j]'hj_p))
    {sc₀' : MirAst.ScalarInt} {msc₀' : Miri.Memory.ScalarInt}
    (hrel₀' : ScalarRel sc₀' msc₀')
    (hsz₀' : (fields[k₀]'hk₀).fieldLayout.size = translateSizeBytes sc₀'.sizeBytes)
    (hbool₀' : (fields[k₀]'hk₀).ty.kind = .bool → sc₀'.sizeBytes = 1 ∧ (sc₀'.bits = 0 ∨ sc₀'.bits = 1))
    (hchar₀' : (fields[k₀]'hk₀).ty.kind = .char → sc₀'.sizeBytes = 4 ∧ isValidCharCode sc₀'.bits = true) :
    ∃ (rootVal' : Value) (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (u : Nat),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      mach.lookupBaseAddr allocId = some baseAddr ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr ∧
      baseAddr.toNat + (fields[k₀]'hk₀).offset.bytes.toNat < 2 ^ 64 ∧
      ∃ (hu_lt : u < mach.memory.live.size),
        mach.memory.live.findIdx? (fun (id, _) => id == allocId) = some u ∧
        mach.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[k₀]'hk₀).offset msc₀'.size)
          (.fromScalarInt msc₀') localAlloc.allocation = .ok () alloc' ∧
        (∀ locals, writeProjectedValue locals rootVal projs
          (.aggregate 0 [.scalar sc₀']) = .ok rootVal') ∧
        StructMemPlaceRel
          (updateAllocMachine mach u allocId localAlloc.kind alloc')
          ty layouts fields paths rootVal' mp := by
  rcases h with ⟨allocId, tag, baseAddr, localAlloc, words, hvalid, hplen,
    ⟨_, hnz_root⟩, hleaf_bytes, hprov, hmis, hmeta, hlive, hbase, hptr, hovf,
    hmut, halign, hbsize, hlen, hpmap, hmask, hbits, hfields, hpad⟩
  obtain ⟨hp_ne_0, hfl_0, hprim_0, hvpath_0, sc₀_old, msc₀_old, hrpv_0, hrel₀_old, hsz₀_old, _, _, _, _⟩ :=
    hfields k₀ hk₀
  dsimp at hp_ne_0 hfl_0 hprim_0 hvpath_0 hrpv_0 hsz₀_old
  have hvpath_0_app : ValidAggregateFieldPath layouts rootVal (projs ++ [.field 0 mid₀]) := by
    rwa [← hpath₀]
  have hrpv_0_app : readProjectedValue [] rootVal (projs ++ [.field 0 mid₀]) = .ok (.scalar sc₀_old) := by
    rwa [← hpath₀]
  obtain ⟨hvpath_sub, hrpv_sub⟩ :=
    ValidAggregateFieldPath.read_substruct_scalarWrap hprojs_ne hlast hrepr
      hvpath_0_app hrpv_0_app
  let newSubVal : Value := .aggregate 0 [.scalar sc₀']
  obtain ⟨oldSubVal, rootVal', hrpv_spec, hw_spec, hvpath_sub', hbytes_eq, _, happend_spec, hdisj_spec⟩ :=
    hvpath_sub.writeProjectedValue_spec newSubVal
  rw [hrpv_sub []] at hrpv_spec
  injection hrpv_spec with hold_eq; subst hold_eq
  have hsc0_bytes : sc₀'.sizeBytes = sc₀_old.sizeBytes := by
    have heq_ts : translateSizeBytes sc₀'.sizeBytes = translateSizeBytes sc₀_old.sizeBytes :=
      hsz₀'.symm.trans hsz₀_old
    have h1 := hrel₀'.validBytes
    have h2 := hrel₀_old.validBytes
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      (rw [h1, h2] at heq_ts ⊢; try (revert heq_ts; decide))
  have hsub_bytes : valueLeafBytes newSubVal =
      valueLeafBytes (.aggregate 0 [.scalar sc₀_old]) := by
    dsimp [newSubVal, valueLeafBytes, valueLeafBytes.valueLeafBytesList]
    omega
  have hleaf_bytes' : valueLeafBytes rootVal' = structSumFieldBytes fields :=
    (hbytes_eq hsub_bytes).trans hleaf_bytes
  obtain ⟨alloc', words', hw₀, hbs', hlen', hmut', hpmap', hmask', hbits',
      hinit_0', hread_0', hother', hpad'⟩ :=
    writeField_preserves_other_fields_and_padding hvalid hk₀ hrel₀' hsz₀'
      hbsize hlen hmut hpmap hmask
  obtain ⟨hfind_live, u, hu_lt, hfidx, hget⟩ := hlive
  have hlive_self : LiveAllocEntry (mach.memory.live.set! u (allocId, ⟨localAlloc.kind, alloc'⟩))
      allocId ⟨localAlloc.kind, alloc'⟩ :=
    LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget⟩ hu_lt hfidx ⟨localAlloc.kind, alloc'⟩
  have hbnd_0 := hvalid.fields_in_bounds k₀ hk₀
  have hsc0'_pos : 0 < sc₀'.sizeBytes := by
    rcases hrel₀'.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
  have hnz_new : NoZeroByteLeaves newSubVal := ⟨hsc0'_pos, True.intro⟩
  have hnz_root' : NoZeroByteLeaves rootVal' :=
    hvpath_sub.noZeroByteLeaves_write (hw_spec []) hnz_root hnz_new
  have hnew_len : ∀ sf_old sf_new,
      Value.aggregate 0 [.scalar sc₀_old] = .aggregate 0 sf_old →
      newSubVal = .aggregate 0 sf_new → sf_new.length = sf_old.length := by
    intro sf_old sf_new h1 h2
    injection h1 with _ h1'; injection h2 with _ h2'
    subst h1' h2'; rfl
  refine ⟨rootVal', allocId, tag, baseAddr, localAlloc, alloc', u,
    hprov, hbase, hptr, by omega, hu_lt, hfidx, hget, hw₀, hw_spec, ?_⟩
  refine .mk allocId tag baseAddr ⟨localAlloc.kind, alloc'⟩ words' hvalid hplen
    ⟨hvpath_sub'.nonempty_agg, hnz_root'⟩ hleaf_bytes' hprov hmis hmeta
    hlive_self hbase hptr hovf hmut' halign hbs' hlen' hpmap' hmask' ?_ ?_ ?_
  · intro i hi b hlo hhi
    have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
      have := hvalid.fields_in_bounds i hi; omega
    rw [hbits' b hb_lt]
    by_cases hi0 : i = k₀
    · subst hi0
      have hin0 : (fields[i]'hi).offset.bytes.toNat ≤ b ∧
          b < (fields[i]'hi).offset.bytes.toNat + (fields[i]'hi).fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin0]
    · rw [hbits i hi b hlo hhi]; simp
  · intro j hj
    by_cases hj0 : j = k₀
    · subst hj0
      obtain ⟨hr_0, hp_0⟩ := happend_spec [.field 0 mid₀]
      have hv_0 : ValidAggregateFieldPath layouts rootVal' (paths[j]'hk₀_p) := by
        rw [hpath₀]
        exact hp_0 hnew_len hvpath_0_app (.single [.scalar sc₀'] 0 mid₀ (.scalar sc₀') rfl)
      have hrpv_0' : readProjectedValue [] rootVal' (paths[j]'hk₀_p) = .ok (.scalar sc₀') := by
        rw [hpath₀, hr_0]; rfl
      exact ⟨hp_ne_0, hfl_0, hprim_0, hv_0, sc₀', msc₀', hrpv_0',
        hrel₀', hsz₀', hbool₀', hchar₀', hinit_0', hread_0'⟩
    · obtain ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j, sc_j, msc_j, hrpv_j, hrel_j,
        hsz_j, hbool_j, hchar_j, _, hread_j⟩ := hfields j hj
      dsimp at hp_ne_j hfl_j hprim_j hvpath_j hrpv_j hsz_j hbool_j hchar_j hread_j ⊢
      have hpos_j : 0 < (fields[j]'hj).fieldLayout.size.bytes.toNat := by
        rw [hsz_j]; exact translateSizeBytes_pos hrel_j.validBytes
      obtain ⟨hinit_j', hread_j_eq⟩ := hother' j hj hj0 hpos_j (hbits j hj)
      have hj_p : j < paths.length := by rw [hplen]; exact hj
      obtain ⟨hrpv_j_eq, hvpath_j'⟩ := hdisj_spec (paths[j]'hj_p)
        (hdisj_paths j hj_p hj0)
      exact ⟨hp_ne_j, hfl_j, hprim_j, hvpath_j' hvpath_j, sc_j, msc_j,
        (hrpv_j_eq []).trans hrpv_j, hrel_j, hsz_j, hbool_j, hchar_j,
        hinit_j', hread_j_eq.trans hread_j⟩
  · intro p hp
    exact (hpad' p hp).trans (hpad p hp)

/-- Syntactic well-typedness of a non-empty `ProjectionElem.Field` chain
`projs` projecting from an aggregate local `idx` (`decl.ty`, with `.Scalar`,
`.ScalarPair`, or `.Memory` backend representation) to a 1-field `.Scalar`
wrapper sub-struct `subTy` at byte offset `subOff`, backed by leaf `k₀` at
`projs ++ [.field 0 mid₀]`. -/
inductive WellTypedLM2_2ProjectedScalarWrapRead
    (body : CapturedMir) (env : StructTypeEnv)
    (idx : Local) (projs : List ProjectionElem)
    (subTy : Ty) (sf₀ : StructFieldDesc) (mid₀ : Ty) : Prop where
  | mk (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k₀ : Nat)
      (hk₀_f : k₀ < fields.length)
      (hk₀_p : k₀ < paths.length)
      (subOff : Miri.ABI.Size)
      (a : Miri.ABI.Scalar) :
      get? body.localDecls idx = some decl →
      env decl.ty = some (fields, paths) →
      env subTy = some ([sf₀], [[.field 0 mid₀]]) →
      paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀] →
      (fields[k₀]'hk₀_f).ty = mid₀ →
      (fields[k₀]'hk₀_f).offset = subOff →
      (fields[k₀]'hk₀_f).fieldLayout = sf₀.fieldLayout →
      0 < sf₀.fieldLayout.size.bytes.toNat →
      sf₀.ty = mid₀ →
      sf₀.offset = Miri.ABI.Size.ZERO →
      sf₀.fieldLayout = (translateTy mid₀ body.layouts).layout →
      (translateTy subTy body.layouts).layout.size = sf₀.fieldLayout.size →
      ValidStructLayout (translateTy subTy body.layouts).layout [sf₀] →
      (translateTy subTy body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      (translateTy subTy body.layouts).layout.backendRepr = .Scalar a →
      ValidZeroScalarChain body.layouts (translateTy subTy body.layouts)
        [.field 0 mid₀] mid₀ →
      IsPrimScalarTy mid₀ →
      ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts)
        projs subTy subOff →
      WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀

/-- Simulation relation for reading a whole projected 1-field `.Scalar` wrapper
sub-struct via `.copy ⟨idx, projs⟩` or `.move ⟨idx, projs⟩`. -/
inductive ProjectedScalarWrapReadSimRelLM2_2
    (body : CapturedMir)
    (env : StructTypeEnv)
    (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState)
    (subTy : Ty) (sf₀ : StructFieldDesc) (mid₀ : Ty) :
    OperandEvalResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  | ok (sc₀ : MirAst.ScalarInt) (msc₀ : Miri.Memory.ScalarInt)
      (outLay : Miri.Interpreter.LocalLayout)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
      FrameRelLM2_2 body env m.machine af topFrame' →
      ImmediateStructRel subTy body.layouts [sf₀]
        [[.field 0 mid₀]]
        (.aggregate 0 [.scalar sc₀])
        (.scalar (.fromScalarInt msc₀)) →
      topFrame'.localsIdentity = topFrame.localsIdentity →
      topFrame'.returnContinuation = topFrame.returnContinuation →
      topFrame'.returnPlace = topFrame.returnPlace →
      (∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value) →
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') →
      ProjectedScalarWrapReadSimRelLM2_2 body env af topFrame m subTy sf₀ mid₀
        (.ok (.aggregate 0 [.scalar sc₀]) af.locals)
        (.ok ⟨.scalar (.fromScalarInt msc₀), outLay⟩
          { m with stack := ⟨#[topFrame']⟩ })
  | ub (msg : String) (m' : AnnealStepState) :
      ProjectedScalarWrapReadSimRelLM2_2 body env af topFrame m subTy sf₀ mid₀
        .ub (.error (.undefinedBehavior msg) m')

/-- Per-local core lemma for reading a projected 1-field `.Scalar` wrapper sub-struct. -/
theorem evalProjection_nested_scalar_wrap_read_at_local
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local} {decl : LocalDecl}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ : StructFieldDesc} {mid₀ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < topFrame.locals.size)
    (hslot : get? af.locals idx = some slot)
    (hmls_eq : topFrame.locals[idx]'hlt_mf = mls)
    (hloc : LocalRelLM2_2 env m.machine decl body.layouts slot mls)
    (hwt : WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ sc₀ msc₀ outLay,
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil =
        .ok (.aggregate 0 [.scalar sc₀]) af.locals ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc₀), outLay⟩
          { m with
            stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt_mf
              (translateTy decl.ty body.layouts)]⟩ } ∧
      ImmediateStructRel subTy body.layouts [sf₀]
        [[.field 0 mid₀]]
        (.aggregate 0 [.scalar sc₀])
        (.scalar (.fromScalarInt msc₀))) ∨
    (∃ msg m',
      evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩)
          .nil globals body.layouts .nil = .ub ∧
      (annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') := by
  cases hwt with
  | mk decl' fields paths k₀ hk₀_f hk₀_p subOff a
      hdecl' henv _ hpath₀ hty₀ hoff_k₀ hfl_k₀ hpos_sf₀
      hsf₀_ty hsf₀_off hsf₀_fl hsz_sub hvalid_sub hnz_sub hrepr_sub
      hzchain_sub hprim₀ hchain =>
    have hdecl_eq : decl' = decl := Option.some.inj (hdecl'.symm.trans hdecl)
    cases hdecl_eq
    have hcache := hloc.layout_eq
    let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
    have hp_ne : projs ≠ [] := hchain.ne_nil
    obtain ⟨subIdx, hlast_p⟩ := hchain.last_eq
    obtain ⟨p0, ps, hp_cons⟩ : ∃ p0 ps, projs = p0 :: ps := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons p0 ps => exact ⟨p0, ps, rfl⟩
    subst hp_cons
    have hp0_nd : p0 ≠ .deref := hchain.not_deref_head
    have htr_op :
        translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩) =
          (if isMove then .Move ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩
           else .Copy ⟨idx, (translateProjectionElem p0 :: ps.map translateProjectionElem).toArray⟩) := by
      cases isMove <;> rfl
    have ha_proj :
        evalOperand af.locals (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)
            .nil globals body.layouts .nil =
          match get? af.locals idx with
          | some (.init rootVal) =>
              match readProjectedValue af.locals rootVal (p0 :: ps) with
              | .ok fieldVal => .ok fieldVal af.locals
              | .ub => .ub
              | .unsupported => .unsupported
          | _ => .ub := by
      cases isMove <;> cases p0 <;> (try exact False.elim (hp0_nd rfl)) <;>
        (simp only [mkPlaceOperand, Bool.false_eq_true, ↓reduceIte]
         unfold evalOperand; dsimp only; cases get? af.locals idx with
          | none => rfl
          | some sl => cases sl <;> rfl)
    cases hloc with
    | base _ _ henv_none _ =>
      rw [henv] at henv_none; cases henv_none
    | structDead _ _ c _ _ =>
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        exact EStateM.bind_apply_error
          (annealEvalOperand_projected_dead hframes hlt_mf hdecl hmls_eq hcache)
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitImm _ _ c _ _ =>
      have heval_p := annealEvalProjection_uninit_of_validFieldProjChain hchain
        { m with stack := ⟨#[topFrame']⟩ }
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p),
            annealReadImmediate_uninit]
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structUninitInd f' p' mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, hvalid_outer, hprov, _, _, hlive,
        hbase, hptr, hovf, _, _, _, _, _, hmask_uninit⟩
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hbnd_k0 := hvalid_outer.fields_in_bounds k₀ hk₀_f
      rw [hoff_k₀, hfl_k₀, ← hsz_sub] at hbnd_k0
      have hlt_u64 := (translateTy decl.ty body.layouts).layout.size.bytes.toNat_lt
      have hend := lm22_allocRange_end (start := subOff)
        (sz := (translateTy subTy body.layouts).layout.size) (by omega)
      have hle_end :
          (Miri.ABI.Size.ofBytes (subOff.bytes + (translateTy subTy body.layouts).layout.size.bytes)).bytes ≤
          (translateTy decl.ty body.layouts).layout.size.bytes := by
        rw [UInt64.le_iff_toNat_le]
        dsimp [Miri.ABI.Size.ofBytes]
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)]
        exact hbnd_k0
      have huninit_q : localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange subOff (translateTy subTy body.layouts).layout.size) =
          .ok (.error (Miri.Memory.allocRange subOff (translateTy subTy body.layouts).layout.size)) := by
        rw [hmask_uninit]
        exact Miri.Memory.InitMask.lazy_uninitialized_query
          (translateTy decl.ty body.layouts).layout.size _ _ hend hle_end
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + subOff.bytes) := by
        rw [hptr]; rfl
      have hnot_array : ∀ s c, (translateTy subTy body.layouts).layout.fields ≠ Miri.ABI.FieldsShape.Array s c := by intro s c heq; rcases hvalid_sub.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all
      have hread_ub := annealReadIndirectImmediate_scalarRepr_uninit_ub
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (lay := translateTy subTy body.layouts)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hnz_sub hnot_array hrepr_sub hprov hbase hptr_proj hlive.1 huninit_q
      have hm_err :
          (annealEvalOperand body.localDecls body.layouts
              (translateOperand (mkPlaceOperand isMove ⟨idx, p0 :: ps⟩)) known >>=
            annealReadImmediate) m =
            .error (.undefinedBehavior "read of uninitialized memory field")
              { m with stack := ⟨#[topFrame']⟩ } := by
        rw [htr_op]
        dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ub
      refine Or.inr ⟨_, _, ?_, hm_err⟩
      rw [ha_proj, hslot]
    | structImm f' p' v imm c henv' _ himm =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      cases himm with
      | scalarWrapper f₀ p₀ _ sc₀ msc₀ v _ _ _ hz _ _ _ hwrap hrel_0 hsz_0 hbool_0 hchar_0 =>
        have hk0 : k₀ = 0 := by simp at hk₀_f; omega
        subst hk0
        dsimp only [List.getElem_cons_zero] at hpath₀ hty₀ hfl_k₀
        rw [hpath₀] at hz hwrap
        have ha_read := hwrap.readProjectedValue_prefix_wrap (projs := p0 :: ps) (by nofun) af.locals
        have heval_p := hz.evalProjection_prefix_scalar (projs := p0 :: ps) (by nofun) hlast_p
          (.fromScalarInt msc₀) { m with stack := ⟨#[topFrame']⟩ }
        have himm_sub : ImmediateStructRel subTy body.layouts [sf₀]
            [[.field 0 mid₀]]
            (.aggregate 0 [.scalar sc₀])
            (.scalar (.fromScalarInt msc₀)) := by
          refine .scalarWrapper sf₀ [.field 0 mid₀] a sc₀ msc₀ (.aggregate 0 [.scalar sc₀])
            hvalid_sub hrepr_sub (by nofun) (by rw [hsf₀_ty]; exact hzchain_sub)
            hsf₀_off (by rw [hsf₀_ty]; exact hsf₀_fl)
            (by rw [hsf₀_ty]; exact hprim₀)
            (.wrap_cons mid₀ [] (.scalar sc₀) .bare)
            hrel_0 (by rw [← hfl_k₀]; exact hsz_0)
            (by rw [hsf₀_ty, ← hty₀]; exact hbool_0)
            (by rw [hsf₀_ty, ← hty₀]; exact hchar_0)
        refine Or.inl ⟨sc₀, msc₀, translateTy subTy body.layouts, ?_, ?_, himm_sub⟩
        · rw [ha_proj, hslot]; dsimp only; rw [ha_read]
        · rw [htr_op]; dsimp only [Bind.bind]
          rw [EStateM.bind_apply_ok
                ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                  (Or.inr (by nofun))).trans heval_p)]
          rfl
      | scalarPair f₀ f₁ mid₀' mid₁' z₀ z₁ _ _ bOff sc₀ sc₁ msc₀ msc₁ v₀ v₁
          hvalid_out _ _ _ hrepr_out _ _ hoff₀ hoff₁ hf₀_off hf₁_off hfl₀ hfl₁
          hrt₀ hrt₁ _ _ hz₀ hz₁ hw₀ hw₁ hrel₀ hrel₁ hsz₀ hsz₁
          hbool₀ hchar₀ hbool₁ hchar₁ =>
        have hpos₀ : 0 < f₀.fieldLayout.size.bytes.toNat := by
          rw [hsz₀]; exact translateSizeBytes_pos hrel₀.validBytes
        have hpos₁ : 0 < f₁.fieldLayout.size.bytes.toNat := by
          rw [hsz₁]; exact translateSizeBytes_pos hrel₁.validBytes
        have hdisj01 := hvalid_out.fields_disjoint 0 1 (by simp) (by simp) (by decide)
        dsimp at hdisj01
        rw [hf₀_off, hf₁_off] at hdisj01
        have hle_bOff : f₀.fieldLayout.size.bytes.toNat ≤ bOff.bytes.toNat := by
          dsimp [Miri.ABI.Size.ZERO] at hdisj01; omega
        have hbnd₁_tot : bOff.bytes.toNat + f₁.fieldLayout.size.bytes.toNat ≤
            (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
          simpa [hf₁_off] using hvalid_out.fields_in_bounds 1 (by simp)
        have hk01 : k₀ = 0 ∨ k₀ = 1 := by simp at hk₀_f; omega
        rcases hk01 with rfl | rfl
        · dsimp [List.append] at hpath₀ hty₀ hfl_k₀
          injection hpath₀ with hp0_eq hz0_eq; subst hp0_eq
          have hz₀_ne : z₀ ≠ [] := by rw [hz0_eq]; cases ps <;> nofun
          have himm_sub0 : ImmediateStructRel subTy body.layouts [sf₀]
              [[.field 0 mid₀]]
              (.aggregate 0 [.scalar sc₀])
              (.scalar (.fromScalarInt msc₀)) := by
            refine .scalarWrapper sf₀ [.field 0 mid₀] a sc₀ msc₀ (.aggregate 0 [.scalar sc₀])
              hvalid_sub hrepr_sub (by nofun) (by rw [hsf₀_ty]; exact hzchain_sub)
              hsf₀_off (by rw [hsf₀_ty]; exact hsf₀_fl)
              (by rw [hsf₀_ty]; exact hprim₀)
              (.wrap_cons mid₀ [] (.scalar sc₀) .bare)
              hrel₀ (by rw [← hfl_k₀]; exact hsz₀)
              (by rw [hsf₀_ty, ← hty₀]; exact hbool₀)
              (by rw [hsf₀_ty, ← hty₀]; exact hchar₀)
          rcases hz₀ with ⟨hz_nil, _⟩ | ⟨hnf₀, hz₀_c⟩
          · exact False.elim (hz₀_ne hz_nil)
          · rw [hz0_eq] at hz₀_c hw₀
            cases ps with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq,
                ProjectionElem.field.injEq] at hlast_p
              rcases hlast_p with ⟨_, rfl⟩
              dsimp [List.append] at hw₀
              cases hw₀ with
              | wrap_cons _ _ _ hbare =>
                cases hbare
                refine Or.inl ⟨sc₀, msc₀,
                  ⟨encodeTyId mid₀', (translateTy decl.ty body.layouts).layout⟩,
                  ?_, ?_, himm_sub0⟩
                · rw [ha_proj, hslot]; rfl
                · rw [htr_op]; dsimp only [Bind.bind, List.map, translateProjectionElem]
                  rw [EStateM.bind_apply_ok
                        (annealEvalOperand_projected_scalarPair_single hframes hlt_mf hdecl
                          hmls_eq hcache (Or.inl rfl))]
                  rfl
            | cons q₀ qs₀ =>
              have hlast_ps : (q₀ :: qs₀).getLast? = some (.field subIdx subTy) := by
                simpa using hlast_p
              have ha_sub := hw₀.readProjectedValue_prefix_wrap (projs := q₀ :: qs₀)
                (by nofun) af.locals
              have hmid₀_sz : (translateTy mid₀' body.layouts).layout.size = f₀.fieldLayout.size := by
                rw [← hz₀_c.leaf_prim_and_size.2, ← hfl₀]
              have hsz_ne₀ : (translateTy mid₀' body.layouts).layout.size ≠
                  (translateTy decl.ty body.layouts).layout.size := by
                intro heq
                have := congrArg (fun s : Miri.ABI.Size => s.bytes.toNat) heq
                rw [hmid₀_sz] at this; omega
              have hbnd₀ : (translateTy mid₀' body.layouts).layout.size.bytes.toNat ≤
                  (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
                rw [hmid₀_sz]; omega
              have hpf0 := projectField_immediate_scalarPair_zero_nonForget_eq
                (s0 := .fromScalarInt msc₀) (s1 := .fromScalarInt msc₁)
                hrt₀ hnf₀ hrepr_out hoff₀ hsz_ne₀ hbnd₀
              have heval_p :
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                      translateTy decl.ty body.layouts⟩
                    ((.field 0 mid₀' :: q₀ :: qs₀).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } =
                  .ok ⟨.immediate (.scalar (.fromScalarInt msc₀)), translateTy subTy body.layouts⟩
                    { m with stack := ⟨#[topFrame']⟩ } := by
                have hhead :
                    annealEvalProjection body.layouts
                      ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                        translateTy decl.ty body.layouts⟩
                      (translateProjectionElem (.field 0 mid₀') ::
                        (q₀ :: qs₀).map translateProjectionElem)
                      { m with stack := ⟨#[topFrame']⟩ } =
                    annealEvalProjection body.layouts
                      ⟨.immediate (.scalar (.fromScalarInt msc₀)), translateTy mid₀' body.layouts⟩
                      ((q₀ :: qs₀).map translateProjectionElem)
                      { m with stack := ⟨#[topFrame']⟩ } := by
                  dsimp only [translateProjectionElem, annealEvalProjection]
                  with_unfolding_all
                    simp only [Miri.Interpreter.project, hpf0, Bind.bind, Pure.pure]
                    rfl
                exact hhead.trans (hz₀_c.evalProjection_prefix_scalar (projs := q₀ :: qs₀)
                  (by nofun) hlast_ps _ _)
              refine Or.inl ⟨sc₀, msc₀, translateTy subTy body.layouts, ?_, ?_, himm_sub0⟩
              · rw [ha_proj, hslot]
                simp only [readProjectedValue, get?, List.getElem?_cons_zero, ha_sub]
              · rw [htr_op]; dsimp only [Bind.bind]
                rw [EStateM.bind_apply_ok
                      ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                        (Or.inl (by nofun))).trans heval_p)]
                rfl
        · dsimp [List.append] at hpath₀ hty₀ hfl_k₀
          injection hpath₀ with hp0_eq hz1_eq; subst hp0_eq
          have hz₁_ne : z₁ ≠ [] := by rw [hz1_eq]; cases ps <;> nofun
          have himm_sub1 : ImmediateStructRel subTy body.layouts [sf₀]
              [[.field 0 mid₀]]
              (.aggregate 0 [.scalar sc₁])
              (.scalar (.fromScalarInt msc₁)) := by
            refine .scalarWrapper sf₀ [.field 0 mid₀] a sc₁ msc₁ (.aggregate 0 [.scalar sc₁])
              hvalid_sub hrepr_sub (by nofun) (by rw [hsf₀_ty]; exact hzchain_sub)
              hsf₀_off (by rw [hsf₀_ty]; exact hsf₀_fl)
              (by rw [hsf₀_ty]; exact hprim₀)
              (.wrap_cons mid₀ [] (.scalar sc₁) .bare)
              hrel₁ (by rw [← hfl_k₀]; exact hsz₁)
              (by rw [hsf₀_ty, ← hty₀]; exact hbool₁)
              (by rw [hsf₀_ty, ← hty₀]; exact hchar₁)
          rcases hz₁ with ⟨hz_nil, _⟩ | ⟨hnf₁, hz₁_c⟩
          · exact False.elim (hz₁_ne hz_nil)
          · rw [hz1_eq] at hz₁_c hw₁
            cases ps with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq,
                ProjectionElem.field.injEq] at hlast_p
              rcases hlast_p with ⟨_, rfl⟩
              dsimp [List.append] at hw₁
              cases hw₁ with
              | wrap_cons _ _ _ hbare =>
                cases hbare
                refine Or.inl ⟨sc₁, msc₁,
                  ⟨encodeTyId mid₁', (translateTy decl.ty body.layouts).layout⟩,
                  ?_, ?_, himm_sub1⟩
                · rw [ha_proj, hslot]; rfl
                · rw [htr_op]; dsimp only [Bind.bind, List.map, translateProjectionElem]
                  rw [EStateM.bind_apply_ok
                        (annealEvalOperand_projected_scalarPair_single hframes hlt_mf hdecl
                          hmls_eq hcache (Or.inr rfl))]
                  rfl
            | cons q₁ qs₁ =>
              have hlast_ps : (q₁ :: qs₁).getLast? = some (.field subIdx subTy) := by
                simpa using hlast_p
              have ha_sub := hw₁.readProjectedValue_prefix_wrap (projs := q₁ :: qs₁)
                (by nofun) af.locals
              have hmid₁_sz : (translateTy mid₁' body.layouts).layout.size = f₁.fieldLayout.size := by
                rw [← hz₁_c.leaf_prim_and_size.2, ← hfl₁]
              have hbOff_ne : bOff ≠ Miri.ABI.Size.ZERO := by
                intro hz; rw [hz] at hle_bOff; dsimp [Miri.ABI.Size.ZERO] at hle_bOff; omega
              have hsz_ne₁ : (translateTy mid₁' body.layouts).layout.size ≠
                  (translateTy decl.ty body.layouts).layout.size := by
                intro heq
                have := congrArg (fun s : Miri.ABI.Size => s.bytes.toNat) heq
                rw [hmid₁_sz] at this; omega
              have hbnd₁ : bOff.bytes.toNat + (translateTy mid₁' body.layouts).layout.size.bytes.toNat ≤
                  (translateTy decl.ty body.layouts).layout.size.bytes.toNat := by
                rw [hmid₁_sz]; exact hbnd₁_tot
              have hpf1 := projectField_immediate_scalarPair_one_nonForget_eq
                (s0 := .fromScalarInt msc₀) (s1 := .fromScalarInt msc₁)
                hrt₁ hnf₁ hrepr_out hoff₁ hbOff_ne hsz_ne₁ hbnd₁
              have heval_p :
                  annealEvalProjection body.layouts
                    ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                      translateTy decl.ty body.layouts⟩
                    ((.field 1 mid₁' :: q₁ :: qs₁).map translateProjectionElem)
                    { m with stack := ⟨#[topFrame']⟩ } =
                  .ok ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy subTy body.layouts⟩
                    { m with stack := ⟨#[topFrame']⟩ } := by
                have hhead :
                    annealEvalProjection body.layouts
                      ⟨.immediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)),
                        translateTy decl.ty body.layouts⟩
                      (translateProjectionElem (.field 1 mid₁') ::
                        (q₁ :: qs₁).map translateProjectionElem)
                      { m with stack := ⟨#[topFrame']⟩ } =
                    annealEvalProjection body.layouts
                      ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy mid₁' body.layouts⟩
                      ((q₁ :: qs₁).map translateProjectionElem)
                      { m with stack := ⟨#[topFrame']⟩ } := by
                  dsimp only [translateProjectionElem, annealEvalProjection]
                  with_unfolding_all
                    simp only [Miri.Interpreter.project, hpf1, Bind.bind, Pure.pure]
                    rfl
                exact hhead.trans (hz₁_c.evalProjection_prefix_scalar (projs := q₁ :: qs₁)
                  (by nofun) hlast_ps _ _)
              refine Or.inl ⟨sc₁, msc₁, translateTy subTy body.layouts, ?_, ?_, himm_sub1⟩
              · rw [ha_proj, hslot]
                simp only [readProjectedValue, get?, List.getElem?_cons_succ,
                  List.getElem?_cons_zero, ha_sub]
              · rw [htr_op]; dsimp only [Bind.bind]
                rw [EStateM.bind_apply_ok
                      ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                        (Or.inl (by nofun))).trans heval_p)]
                rfl
    | structInd f' p' v mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      rcases hmp with ⟨allocId, tag, baseAddr, localAlloc, words, _, _, _, _,
        hprov, _, _, hlive, hbase, hptr, hovf, _, _, _, _, _, _, _, hfields_rel, _⟩
      obtain ⟨_, _, _, hvpath_0, sc₀, msc₀, hrpv_0, hrel_0, hsz_0, hbool_0, hchar_0, _, hread_0⟩ :=
        hfields_rel k₀ hk₀_f
      rw [hpath₀] at hvpath_0 hrpv_0
      obtain ⟨_, hrpv_sub⟩ :=
        ValidAggregateFieldPath.read_substruct_scalarWrap hp_ne hlast_p hrepr_sub
          hvpath_0 hrpv_0
      have hptr_ovf : mp.ptr.offset.bytes.toNat +
          (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
        rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
      have heval_p := annealEvalProjection_of_validFieldProjChain hchain hptr_ovf
        { m with stack := ⟨#[topFrame']⟩ }
      have hptr_proj :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + subOff.bytes) := by
        rw [hptr]; rfl
      have hread_0' : localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange subOff (translateTy subTy body.layouts).layout.size) false =
          .ok (Miri.Memory.Scalar.fromScalarInt msc₀) := by
        rwa [hsz_sub, ← hoff_k₀, ← hfl_k₀]
      have hnot_array : ∀ s c, (translateTy subTy body.layouts).layout.fields ≠ Miri.ABI.FieldsShape.Array s c := by intro s c heq; rcases hvalid_sub.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all
      have hread_ok := annealReadIndirectImmediate_scalarRepr_ok
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + subOff.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (lay := translateTy subTy body.layouts)
        (m := { m with stack := ⟨#[topFrame']⟩ })
        hnz_sub hnot_array hrepr_sub hprov hbase hptr_proj hlive.1 hread_0'
      have himm_sub : ImmediateStructRel subTy body.layouts [sf₀]
          [[.field 0 mid₀]]
          (.aggregate 0 [.scalar sc₀])
          (.scalar (.fromScalarInt msc₀)) := by
        refine .scalarWrapper sf₀ [.field 0 mid₀] a sc₀ msc₀ (.aggregate 0 [.scalar sc₀])
          hvalid_sub hrepr_sub (by nofun) (by rw [hsf₀_ty]; exact hzchain_sub)
          hsf₀_off (by rw [hsf₀_ty]; exact hsf₀_fl)
          (by rw [hsf₀_ty]; exact hprim₀)
          (.wrap_cons mid₀ [] (.scalar sc₀) .bare)
          hrel_0 (by rw [← hfl_k₀]; exact hsz_0)
          (by rw [hsf₀_ty, ← hty₀]; exact hbool_0)
          (by rw [hsf₀_ty, ← hty₀]; exact hchar_0)
      refine Or.inl ⟨sc₀, msc₀, translateTy subTy body.layouts, ?_, ?_, himm_sub⟩
      · rw [ha_proj, hslot]; dsimp only; rw [hrpv_sub af.locals]
      · rw [htr_op]; dsimp only [Bind.bind]
        rw [EStateM.bind_apply_ok
              ((annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache
                (Or.inr (by nofun))).trans heval_p)]
        dsimp [annealReadImmediate]
        exact hread_ok

/-- Reading a projected 1-field `.Scalar` wrapper sub-struct (e.g. `_3 = copy _1.1`
with `_1.1 : InnerU32`) simulates `annealEvalOperand >>= annealReadImmediate`
across dead locals (UB), uninitialized immediate/indirect locals (UB),
immediate `.Scalar` / `.ScalarPair` aggregates (`ImmediateStructRel`), and
memory-backed aggregates (`StructMemPlaceRel`). -/
theorem evalOperand_nested_scalar_wrap_read_simulation
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ : StructFieldDesc} {mid₀ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedScalarWrapReadSimRelLM2_2 body env af topFrame m subTy sf₀ mid₀
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediate) m) := by
  have hdecl_ex : ∃ decl, get? body.localDecls idx = some decl := by
    cases hwt with
    | mk decl _ _ _ _ _ _ _ hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨decl, hd⟩
  obtain ⟨decl, hdecl⟩ := hdecl_ex
  obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
  have hfr' := hframe.cache_local_layout hdecl hlt_mf
  have hval_eq :
      ∀ k : Nat, (topFrame'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    by_cases hk : k = idx
    · subst hk
      dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_mf, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · dsimp [topFrame', cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
  rcases evalProjection_nested_scalar_wrap_read_at_local hframes hdecl hlt_mf hslot hmls_eq
      hloc hwt globals known with
    ⟨sc₀, msc₀, outLay, ha_ok, hm_ok, himm_s⟩ | ⟨msg, m', ha_ub, hm_ub⟩
  · rw [ha_ok, hm_ok]
    exact .ok sc₀ msc₀ outLay topFrame' hfr' himm_s rfl rfl rfl hval_eq
      (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
  · rw [ha_ub, hm_ub]
    exact .ub msg m'

end LeanMiriSpec.Correspondence
